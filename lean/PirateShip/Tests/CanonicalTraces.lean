module

public import PirateShip.Proofs.Foundations

@[expose] public section

namespace PirateShip.Tests

open Model

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def four : Config :=
  { replicas := [0, 1, 2, 3], unavailable := 1, fsafe := 1,
    byzantine := [3], transactions := [1, 2, 3] }

def five : Config := { four with replicas := [0, 1, 2, 3, 4] }
def slowOnly : Config := { five with fsafe := 2 }
def evilLeader : Config := { four with byzantine := [0] }

theorem four_valid : four.Valid := by simp [four, Config.Valid]
theorem five_valid : five.Valid := by simp [five, four, Config.Valid]
theorem slowOnly_valid : slowOnly.Valid := by simp [slowOnly, five, four, Config.Valid]
theorem evilLeader_valid : evilLeader.Valid := by simp [evilLeader, four, Config.Valid]

def run (c : Config) : State -> List Action -> Option State
  | s, [] => some s
  | s, a :: rest => (step c s a).bind (fun next => run c next rest)

def execute (c : Config) (actions : List Action) : Option State :=
  run c (initialState c) actions

theorem run_sound (c : Config) (start finish : State) (actions : List Action)
    (executed : run c start actions = some finish) :
    CCF.Execution.Run (transitionSystem c) start actions finish := by
  induction actions generalizing start with
  | nil =>
    simp only [run, Option.some.injEq] at executed
    subst finish
    exact CCF.Execution.Run.nil (system := transitionSystem c) start
  | cons a rest ih =>
    simp only [run] at executed
    cases h : step c start a with
    | none => simp [h] at executed
    | some next =>
      simp only [h, Option.bind_some] at executed
      exact .cons h (ih next executed)

theorem run_reachable (c : Config) (start finish : State) (actions : List Action)
    (reachable : (transitionSystem c).Reachable start)
    (executed : run c start actions = some finish) :
    (transitionSystem c).Reachable finish := by
  induction actions generalizing start with
  | nil =>
    simp only [run, Option.some.injEq] at executed
    subst finish
    exact reachable
  | cons a rest ih =>
    simp only [run] at executed
    cases h : step c start a with
    | none => simp [h] at executed
    | some next =>
      simp only [h, Option.bind_some] at executed
      exact ih next (.step reachable h) executed

def majority : List Action :=
  [.propose 0 2, .deliver 1 0, .deliver 0 1, .deliver 2 0, .deliver 0 2]

def unanimous : List Action := majority ++ [.deliver 3 0, .deliver 0 3]

def twoHop : List Action :=
  majority ++ [.propose 0 3, .deliver 1 0, .deliver 0 1, .deliver 2 0,
    .deliver 0 2, .propose 0 1, .deliver 1 0]

def reports : List ViewChange := [⟨1, 1, [0]⟩, ⟨2, 1, [0]⟩, ⟨3, 1, [0]⟩]

def election : List Action :=
  unanimous ++ [.timeout 1, .timeout 2, .timeout 3,
    .deliver 1 1, .deliver 1 2, .deliver 1 3, .becomeLeader 1 reports [0]]

def stabilized : List Action :=
  election ++ [.deliver 2 1, .deliver 1 2, .deliver 3 1, .deliver 1 3, .propose 1 3]

theorem majority_commits :
    (execute four majority).map (fun s => ((s.nodes 0).commitIndex, (s.nodes 0).auditIndex)) =
      some (1, 0) := by decide

theorem unanimous_audits :
    (execute four unanimous).map (fun s => (s.nodes 0).auditIndex) = some 1 := by decide

theorem two_hop_audits :
    (execute four twoHop).map (fun s => ((s.nodes 0).auditIndex, (s.nodes 1).auditIndex)) =
      some (1, 1) := by decide

theorem election_blocks_proposals :
    ((execute four election).bind (fun s => step four s (.propose 1 1))).isNone = true := by
  decide

theorem stabilization_unblocks_proposals :
    (execute four stabilized).map (fun s =>
      ((s.nodes 1).view, (s.nodes 1).stable, (s.nodes 1).branch)) =
      some (1, true, [0, 1, 2]) := by decide

theorem new_view_votes_use_new_view :
    (execute four (election ++ [.deliver 2 1])).map (fun s => s.network 1 2) =
      some [.vote ⟨2, 1, 1⟩] := by decide

theorem quorum_boundaries :
    (four.commitQuorum, four.auditQuorum, four.fastSupport, four.fastEnabled,
      five.auditQuorum, five.fastSupport, slowOnly.fastEnabled) =
      (3, 3, 2, true, 4, 3, false) := by decide

theorem empty_delivery_disabled :
    (step four (initialState four) (.deliver 1 0)).isNone = true := by decide

theorem follower_proposal_disabled :
    (step four (initialState four) (.propose 1 1)).isNone = true := by decide

theorem honest_adversarial_action_disabled :
    (step four (initialState four) (.byzantineSign 1 (.vote 0 0))).isNone = true := by decide

theorem malformed_message_consumed :
    (execute four [.byzantineSend 3 1 (.appendEntries 999), .deliver 1 3]).map
      (fun s => ((s.nodes 1).branch, s.network 1 3)) = some ([], []) := by decide

theorem forged_vote_rejected :
    (execute four [.propose 0 1, .byzantineSend 3 0 (.vote ⟨1, 0, 0⟩), .deliver 0 3]).map
      (fun s => (s.nodes 0).votes.map Vote.signer) = some [0] := by decide

theorem omission_vote_accepted :
    (execute four [.propose 0 1, .byzantineSign 3 (.vote 0 0),
      .byzantineSend 3 0 (.vote ⟨3, 0, 0⟩), .deliver 0 3]).map
      (fun s => ((s.nodes 3).branch, (s.nodes 0).votes.map Vote.signer)) =
      some ([], [3, 0]) := by decide

theorem arbitrary_faulty_state_is_local :
    (execute four [.byzantineState 3 { branch := [999], commitIndex := 900 }]).map
      (fun s => ((s.nodes 3).branch, (s.nodes 0).branch, s.byzActions)) =
      some ([999], [], 1) := by decide

def equivocation : List Action :=
  [.byzantinePublish 0 { parent := none, view := 0, transactions := [2] },
   .byzantineSend 0 1 (.appendEntries 0), .deliver 1 0,
   .byzantinePublish 0 { parent := none, view := 0, transactions := [1] },
   .byzantineSend 0 2 (.appendEntries 1), .deliver 2 0]

theorem conflicting_branches_are_reachable :
    (execute evilLeader equivocation).map (fun s =>
      ((s.nodes 1).branch, (s.nodes 2).branch, (s.nodes 1).auditIndex, (s.nodes 2).auditIndex)) =
      some ([0], [1], 0, 0) := by decide

theorem replay_does_not_duplicate :
    (execute evilLeader (equivocation ++
      [.byzantineSend 0 1 (.appendEntries 0), .deliver 1 0])).map
      (fun s => (s.nodes 1).branch) = some [0] := by decide

def qc (id : BlockId) : Certificate := ⟨0, id, [⟨0, 0, id⟩, ⟨1, 0, id⟩, ⟨2, 0, id⟩]⟩

def unsignedCommitHint : List Action :=
  [.byzantinePublish 0 { parent := none, view := 0, transactions := [1] },
   .byzantineSign 0 (.vote 0 0),
   .byzantineSend 0 1 (.appendEntries 0), .deliver 1 0,
   .byzantineSend 0 2 (.appendEntries 0), .deliver 2 0,
   .byzantinePublish 0 { parent := some 0, view := 0, transactions := [1], auditQC := some (qc 0) },
   .byzantineSign 0 (.vote 0 1),
   .byzantineSend 0 1 (.appendEntries 1), .deliver 1 0,
   .byzantineSend 0 2 (.appendEntries 1), .deliver 2 0,
   .byzantinePublish 0 { parent := some 1, view := 0, transactions := [1], auditQC := some (qc 1) },
   .byzantineSend 0 1 (.appendEntries 2), .deliver 1 0]

/-- Counterexample to the TLA+ auxiliary auditIndex <= commitIndex claim. -/
theorem audit_can_exceed_unsigned_commit :
    (execute evilLeader unsignedCommitHint).map
      (fun s => ((s.nodes 1).auditIndex, (s.nodes 1).commitIndex)) = some (1, 0) := by decide

theorem duplicate_signers_rejected :
    (execute four majority).map (fun s =>
      validCertificate four s ⟨0, 0, [⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨1, 0, 0⟩]⟩) =
      some false := by decide

theorem fabricated_certificate_rejected :
    (execute four [.propose 0 1]).map (fun s => validCertificate four s (qc 0)) =
      some false := by decide

theorem genuine_certificate_accepted :
    (execute four majority).map (fun s => validCertificate four s (qc 0)) =
      some true := by decide

theorem signatures_cannot_be_rebound :
    (execute four (majority ++ [.propose 0 3])).map (fun s =>
      validCertificate four s (qc 1)) = some false := by decide

theorem new_view_without_evidence_rejected :
    (execute evilLeader
      [.timeout 1, .timeout 1, .timeout 1, .timeout 1,
       .byzantinePublish 0 { parent := none, view := 4, transactions := [], stabilization := true },
       .byzantineSend 0 1 (.newView 0 []), .deliver 1 0]).map
      (fun s => ((s.nodes 1).branch, (s.nodes 1).entered)) = some ([], false) := by decide

theorem fifo_delivery :
    (execute four [.propose 0 1, .propose 0 2, .deliver 1 0]).map
      (fun s => ((s.nodes 1).branch, s.network 1 0)) =
      some ([0], [.appendEntries 1]) := by decide

def transitive : List Action :=
  [.propose 0 1, .deliver 1 0, .deliver 0 1, .propose 0 2,
   .deliver 2 0, .deliver 2 0, .deliver 0 2, .deliver 0 2, .deliver 3 0, .deliver 0 3]

theorem transitive_unanimity_audits :
    (execute four transitive).map (fun s =>
      ((s.nodes 0).auditIndex, ((s.nodes 0).votes.map Vote.block).eraseDups.length)) =
      some (1, 2) := by decide

theorem descendant_support_not_equal_tips :
    possibleFastBlocks five
      [⟨0, 1, [0, 1]⟩, ⟨1, 1, [0, 2]⟩, ⟨2, 1, [0, 3]⟩, ⟨3, 1, [4]⟩] = [0] := by
  decide

theorem nonminimal_support_threshold :
    possibleFastBlocks five
      [⟨0, 1, [0]⟩, ⟨1, 1, [0]⟩, ⟨2, 1, [1]⟩, ⟨3, 1, [1]⟩] = [] := by decide

def allFive : List Action :=
  unanimous ++ [.deliver 4 0, .deliver 0 4]

theorem unsafe_fast_configuration_disabled :
    (execute slowOnly allFive).map (fun s =>
      ((s.nodes 0).commitIndex, (s.nodes 0).auditIndex)) = some (1, 0) := by decide

theorem slow_audit_without_fast_path :
    (execute slowOnly (allFive ++
      [.propose 0 3, .deliver 1 0, .deliver 0 1, .deliver 2 0, .deliver 0 2,
       .deliver 3 0, .deliver 0 3])).map (fun s => (s.nodes 0).auditIndex) =
      some 1 := by decide

def rollbackAttempt : List Action :=
  unanimous ++
    [.timeout 0, .timeout 0, .timeout 0, .timeout 1, .timeout 1, .timeout 1,
     .timeout 2, .timeout 2, .timeout 2,
     .byzantinePublish 3 { parent := none, view := 3, transactions := [], stabilization := true },
     .byzantineSend 3 0 (.newView 1 [⟨0, 3, [0]⟩, ⟨1, 3, [0]⟩, ⟨2, 3, [0]⟩]),
     .deliver 0 3]

theorem wrong_branch_with_genuine_evidence_rejected :
    (execute four rollbackAttempt).map (fun s =>
      ((s.nodes 0).branch, (s.nodes 0).auditIndex, (s.nodes 0).entered,
       validEvidence four s 3 [⟨0, 3, [0]⟩, ⟨1, 3, [0]⟩, ⟨2, 3, [0]⟩],
       validBranch four s [1])) =
      some ([0], 1, false, true, true) := by decide

theorem stuttering_preserves_observations :
    (execute four (majority ++ [.stutter])).map (fun s => (s.nodes 0).commitIndex) =
      some 1 := by decide

theorem singleton_progress :
    (execute {
      replicas := [0], unavailable := 0, fsafe := 0, byzantine := [],
      transactions := [1] } [.propose 0 1]).map
      (fun s => ((s.nodes 0).commitIndex, (s.nodes 0).auditIndex)) = some (1, 1) := by decide

theorem singleton_election_stabilizes :
    (execute {
      replicas := [0], unavailable := 0, fsafe := 0, byzantine := [],
      transactions := [1] }
      [.timeout 0, .deliver 0 0, .becomeLeader 0 [⟨0, 1, []⟩] [], .propose 0 1]).map
      (fun s => ((s.nodes 0).view, (s.nodes 0).stable, (s.nodes 0).branch)) =
      some (1, true, [0, 1]) := by decide

theorem faulty_node_can_erase_audited_state :
    (execute four (twoHop ++ [.deliver 3 0, .deliver 3 0, .deliver 3 0])).map
      (fun s => ((s.nodes 3).auditIndex, (s.nodes 3).commitIndex,
        (step four s (.byzantineState 3 {})).map (fun after => (after.nodes 3).branch))) =
      some (2, 2, some []) := by decide

theorem successful_execution_reachable (c : Config) (valid : c.Valid)
    (actions : List Action) (finish : State)
    (executed : execute c actions = some finish) :
    (transitionSystem c).Reachable finish := by
  exact run_reachable c (initialState c) finish actions (.initial ⟨valid, rfl⟩) executed

theorem nontrivial_audit_witness :
    exists s, (transitionSystem four).Reachable s /\ (s.nodes 0).auditIndex = 1 := by
  have observed := unanimous_audits
  cases h : execute four unanimous with
  | none => simp [h] at observed
  | some s =>
    refine ⟨s, successful_execution_reachable four four_valid unanimous s h, ?_⟩
    simpa [h] using observed

theorem unsigned_commit_counterexample :
    exists s, (transitionSystem evilLeader).Reachable s /\
      ¬ Properties.AuditBelowCommit evilLeader s := by
  have observed := audit_can_exceed_unsigned_commit
  cases h : execute evilLeader unsignedCommitHint with
  | none => simp [h] at observed
  | some s =>
    refine ⟨s, successful_execution_reachable evilLeader evilLeader_valid unsignedCommitHint s h, ?_⟩
    simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    intro bound
    have atOne := bound 1 (by simp [Config.honest, evilLeader, four])
    omega

end PirateShip.Tests
