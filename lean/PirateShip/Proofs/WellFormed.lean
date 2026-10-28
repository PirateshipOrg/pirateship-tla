module

public import PirateShip.Proofs.BranchValidity
public import PirateShip.Proofs.Local
public import PirateShip.Proofs.AuditBounds

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

def NodeInvariant (c : Config) (s : State) (node : LocalState) : Prop :=
  validBranch c s node.branch = true /\
  node.commitIndex <= node.branch.length /\
  (node.entered = true -> forall id, node.branch.getLast? = some id ->
    exists b, s.blocks[id]? = some b /\ b.view = node.view)

theorem NodeInvariant.history {c : Config} {before after : State} {node : LocalState}
    (valid : NodeInvariant c before node)
    (blocks : before.blocks.IsPrefix after.blocks)
    (signatures : before.signatures.IsPrefix after.signatures) :
    NodeInvariant c after node := by
  refine ⟨validBranch_of_prefix c before after blocks signatures node.branch valid.1,
    valid.2.1, ?_⟩
  intro entered id last
  obtain ⟨b, found, view⟩ := valid.2.2 entered id last
  exact ⟨b, lookup_of_prefix blocks found, view⟩

theorem NodeInvariant.refresh {c : Config} {s : State} {node : LocalState}
    (valid : NodeInvariant c s node) : NodeInvariant c s (refresh c s node) := by
  exact ⟨valid.1, refresh_commit_bound c s node valid.1 valid.2.1, valid.2.2⟩

def StateInvariant (c : Config) (s : State) : Prop :=
  forall r, c.honest r -> NodeInvariant c s (s.nodes r)

def EffectInvariant (c : Config) (s : State) (e : Effect) : Prop :=
  forall r, c.honest r ->
    NodeInvariant c (e.apply s) (e.nodes r) /\
    (e.nodes r).auditIndex <= max (s.nodes r).auditIndex (e.nodes r).branch.length

theorem effect_invariant_of_nodes {c : Config} {s : State} (prior : StateInvariant c s)
    (e : Effect) (same : e.nodes = s.nodes) : EffectInvariant c s e := by
  intro r honest
  rw [same]
  exact ⟨(prior r honest).history (effect_blocks_prefix s e) (effect_signatures_prefix s e),
    Nat.le_max_left _ _⟩

theorem EffectInvariant.setLocal {c : Config} {s : State} {e : Effect}
    (valid : EffectInvariant c s e) (r : Replica) (node : LocalState)
    (updated : c.honest r -> NodeInvariant c (e.apply s) node)
    (bounded : c.honest r ->
      node.auditIndex <= max (s.nodes r).auditIndex node.branch.length) :
    EffectInvariant c s (e.setLocal r node) := by
  intro other honest
  by_cases same : other = r
  · subst other
    have moved := (updated honest).history (after := (e.setLocal r node).apply s)
      ⟨[], by simp [Effect.apply, Effect.setLocal]⟩
      ⟨[], by simp [Effect.apply, Effect.setLocal]⟩
    simpa [Effect.setLocal] using And.intro moved (bounded honest)
  · have moved := (valid other honest).1.history (after := (e.setLocal r node).apply s)
      ⟨[], by simp [Effect.apply, Effect.setLocal]⟩
      ⟨[], by simp [Effect.apply, Effect.setLocal]⟩
    simpa [Effect.setLocal, same] using And.intro moved (valid other honest).2

theorem EffectInvariant.append_signatures {c : Config} {s : State} {e : Effect}
    (valid : EffectInvariant c s e) (extra : List Signature) :
    EffectInvariant c s { e with signatures := e.signatures ++ extra } := by
  intro r honest
  exact ⟨(valid r honest).1.history ⟨[], by simp [Effect.apply]⟩
    ⟨extra, by simp [Effect.apply, List.append_assoc]⟩, (valid r honest).2⟩

theorem EffectInvariant.vote {c : Config} {s : State} {e : Effect}
    (valid : EffectInvariant c s e) (r : Replica) (node : LocalState) (id : BlockId)
    (updated : c.honest r -> NodeInvariant c (e.apply s) node)
    (bounded : c.honest r ->
      node.auditIndex <= max (s.nodes r).auditIndex node.branch.length) :
    EffectInvariant c s (voteEffect e r node id) := by
  let vote : Vote := ⟨r, node.view, id⟩
  let next := { addVote node vote with voted := vote :: node.voted }
  have nextValid : c.honest r -> NodeInvariant c (e.apply s) next := by
    intro honest
    simpa only [NodeInvariant, next, addVote] using updated honest
  exact (valid.setLocal r next nextValid bounded).append_signatures [⟨r, .vote node.view id⟩]

theorem EffectInvariant.refresh {c : Config} {s : State} {e : Effect}
    (valid : EffectInvariant c s e) (r : Replica) :
    EffectInvariant c s (e.setLocal r (refresh c (e.apply s) (e.nodes r))) := by
  apply valid.setLocal r _ (fun honest => (valid r honest).1.refresh)
  intro honest
  have bound := refresh_audit_bound c (e.apply s) (e.nodes r) (valid r honest).1.1
  exact bound.trans (Nat.max_le.mpr ⟨(valid r honest).2, Nat.le_max_right _ _⟩)

theorem EffectInvariant.enqueue {c : Config} {s : State} {e : Effect}
    (valid : EffectInvariant c s e) (recipient sender : Replica) (m : Message) :
    EffectInvariant c s (e.enqueue recipient sender m) := valid

theorem EffectInvariant.broadcast {c : Config} {s : State} {e : Effect}
    (valid : EffectInvariant c s e) (sender : Replica) (m : Message) :
    EffectInvariant c s (e.broadcast c sender m) := by
  unfold Effect.broadcast
  generalize c.replicas = replicas
  induction replicas generalizing e with
  | nil => exact valid
  | cons r rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact valid
    · exact valid.enqueue r sender m

theorem NodeInvariant.proposal {c : Config} {before after : State} {node : LocalState}
    (valid : NodeInvariant c before node) (r : Replica) (tx : Nat)
    (entered : node.entered = true) (leader : c.leader node.view = some r)
    (allowed : tx ∈ c.transactions)
    (newBlocks : after.blocks = before.blocks ++
      [{ parent := node.branch.getLast?, view := node.view, transactions := [tx],
         auditQC := certificateFor c before node, commitHint := node.commitIndex }])
    (signatures : before.signatures.IsPrefix after.signatures)
    (signed : issued after r (.proposal before.blocks.length) = true) :
    NodeInvariant c after { node with branch := node.branch ++ [before.blocks.length] } := by
  let b : Block := {
    parent := node.branch.getLast?, view := node.view, transactions := [tx],
    auditQC := certificateFor c before node, commitHint := node.commitIndex }
  have blocks : before.blocks.IsPrefix after.blocks := ⟨[b], newBlocks.symm⟩
  have old := valid.history blocks signatures
  have found : after.blocks[before.blocks.length]? = some b := by simp [newBlocks, b]
  have branchValid : validBranch c after (node.branch ++ [before.blocks.length]) = true := by
    apply valid_branch_append c after node.branch before.blocks.length b old.1 found
    · simp [signedBlock, found, b, leader, signed]
    · rfl
    · apply (Option.all_eq_true _ _).mpr
      intro id last
      obtain ⟨p, parentFound, parentView⟩ := old.2.2 entered id last
      simp [parentFound, parentView, b]
    · have bound := valid.2.1
      dsimp [b]
      omega
    · simp [b, allowed]
    · apply (Option.all_eq_true _ _).mpr
      intro id last
      obtain ⟨p, parentFound, parentView⟩ := old.2.2 entered id last
      simp [parentFound, parentView, b]
    · apply (Option.all_eq_true _ _).mpr
      intro qc formed
      have checked := certificateFor_valid c before node qc formed
      have preserved := validCertificate_of_prefix c before after blocks signatures qc checked.1
      simp [b, preserved, checked.2.1, checked.2.2]
  refine ⟨branchValid, ?_, ?_⟩
  · have bound := valid.2.1
    simp only [List.length_append, List.length_singleton]
    omega
  · intro _ id last
    simp at last
    subst id
    exact ⟨b, found, rfl⟩

theorem new_leader_node_invariant (c : Config) (before after : State) (node : LocalState)
    (r : Replica) (reports : List ViewChange) (chosen : Branch)
    (leader : c.leader node.view = some r)
    (evidence : validEvidence c before node.view reports = true)
    (selected : chosenBranch c before reports chosen = true)
    (newBlocks : after.blocks = before.blocks ++
      [{ parent := chosen.getLast?, view := node.view, transactions := [],
         stabilization := true }])
    (signatures : before.signatures.IsPrefix after.signatures)
    (signed : issued after r (.proposal before.blocks.length) = true) :
    NodeInvariant c after { node with
      branch := chosen ++ [before.blocks.length], entered := true,
      commitIndex := min node.commitIndex (commonLength node.branch chosen) } := by
  let b : Block := {
    parent := chosen.getLast?, view := node.view, transactions := [],
    stabilization := true }
  have blocks : before.blocks.IsPrefix after.blocks := ⟨[b], newBlocks.symm⟩
  have choice := chosen_branch_valid c before node.view reports chosen evidence selected
  have old := validBranch_of_prefix c before after blocks signatures chosen choice.1
  have found : after.blocks[before.blocks.length]? = some b := by simp [newBlocks, b]
  have branchValid : validBranch c after (chosen ++ [before.blocks.length]) = true := by
    apply valid_branch_append c after chosen before.blocks.length b old found
    · simp [signedBlock, found, b, leader, signed]
    · rfl
    · apply (Option.all_eq_true _ _).mpr
      intro id last
      have checked := List.all_eq_true.mp choice.2.2 id (List.mem_of_getLast? last)
      obtain ⟨p, parentFound, parentView⟩ := (Option.any_eq_true _ _).mp checked
      have parentAfter := lookup_of_prefix blocks parentFound
      have order : p.view <= node.view := by simpa using Nat.le_of_lt (of_decide_eq_true parentView)
      simp [parentAfter, b, order]
    · simp [b]
    · simp [b, choice.2.1]
    · simp [b]
    · simp [b]
  refine ⟨branchValid, ?_, ?_⟩
  · have bound := commonLength_le_right node.branch chosen
    simp only [List.length_append, List.length_singleton]
    omega
  · intro _ id last
    simp at last
    subst id
    exact ⟨b, found, rfl⟩

theorem propose_invariant (c : Config) (s : State) (r : Replica) (tx : Nat) (e : Effect)
    (prior : StateInvariant c s) (transition : propose c s r tx = some e) :
    EffectInvariant c s e := by
  simp only [propose, pure] at transition
  split at transition
  · contradiction
  · rename_i enabled
    simp at enabled
    let node := s.nodes r
    let b : Block := {
      parent := node.branch.getLast?, view := node.view, transactions := [tx],
      auditQC := certificateFor c s node, commitHint := node.commitIndex }
    let base : Effect := { Effect.unchanged s with
      blocks := [b], signatures := [⟨r, .proposal s.blocks.length⟩] }
    let next := { node with branch := node.branch ++ [s.blocks.length] }
    have baseValid : EffectInvariant c s base := effect_invariant_of_nodes prior base rfl
    have nextValid : c.honest r -> NodeInvariant c (base.apply s) next := by
      intro honest
      apply NodeInvariant.proposal (prior r honest) r tx enabled.1.1.2
        enabled.1.1.1.1.1.2 enabled.1.2 rfl (effect_signatures_prefix s base)
      simp [issued, base, Effect.apply]
    have result := ((baseValid.vote r next s.blocks.length nextValid
      (fun _ => Nat.le_max_left _ _)).refresh r).broadcast
      r (.appendEntries s.blocks.length)
    simp only [Option.some.injEq] at transition
    subst e
    exact result

theorem becomeLeader_invariant (c : Config) (s : State) (r : Replica)
    (reports : List ViewChange) (chosen : Branch) (e : Effect)
    (prior : StateInvariant c s) (transition : becomeLeader c s r reports chosen = some e) :
    EffectInvariant c s e := by
  simp only [becomeLeader, pure] at transition
  split at transition
  · contradiction
  · rename_i enabled
    simp at enabled
    let node := s.nodes r
    let b : Block := {
      parent := chosen.getLast?, view := node.view, transactions := [], stabilization := true }
    let base : Effect := { Effect.unchanged s with
      blocks := [b], signatures := [⟨r, .proposal s.blocks.length⟩] }
    let next := { node with
      branch := chosen ++ [s.blocks.length], leader := true, stable := false, entered := true,
      votes := [], commitIndex := min node.commitIndex (commonLength node.branch chosen) }
    have baseValid : EffectInvariant c s base := effect_invariant_of_nodes prior base rfl
    have nextValid : c.honest r -> NodeInvariant c (base.apply s) next := by
      intro _
      apply new_leader_node_invariant c s (base.apply s) node r reports chosen
        enabled.1.1.1.1.2 enabled.1.1.2 enabled.2 rfl (effect_signatures_prefix s base)
      simp [issued, base, Effect.apply]
    have result := ((baseValid.vote r next s.blocks.length nextValid
      (fun _ => Nat.le_max_left _ _)).refresh r).broadcast
      r (.newView s.blocks.length reports)
    simp only [Option.some.injEq] at transition
    subst e
    exact result

theorem received_entries_node_invariant (c : Config) (s : State) (node : LocalState)
    (prior : NodeInvariant c s node) (id : BlockId) (b : Block) (branch : Branch)
    (found : s.blocks[id]? = some b) (sameView : node.view = b.view)
    (extension : branch = node.branch ++ [id]) (valid : validBranch c s branch = true) :
    NodeInvariant c s { node with
      branch := branch, commitIndex := max node.commitIndex b.commitHint } := by
  subst branch
  have hint := valid_branch_hint_bound c s (node.branch ++ [id]) valid id b (by simp) found
  refine ⟨valid, ?_, ?_⟩
  · have bound := prior.2.1
    simp only [List.length_append, List.length_singleton] at hint ⊢
    omega
  · intro _ query last
    simp at last
    subst query
    exact ⟨b, found, sameView.symm⟩

theorem received_new_view_node_invariant (c : Config) (s : State) (node : LocalState)
    (id : BlockId) (b : Block) (branch : Branch)
    (found : s.blocks[id]? = some b) (path : chain s id = some branch)
    (valid : validBranch c s branch = true) :
    NodeInvariant c s { node with
      view := b.view, branch := branch, entered := true,
      commitIndex := min node.commitIndex (commonLength node.branch branch.dropLast) } := by
  refine ⟨valid, ?_, ?_⟩
  · have bound := commonLength_le_right node.branch branch.dropLast
    simp only [List.length_dropLast] at bound
    dsimp only
    omega
  · intro _ query last
    have actual := chainAux_last s.blocks (s.blocks.length + 1) id branch path
    have equal := Option.some.inj (last.symm.trans actual)
    subst query
    exact ⟨b, found, rfl⟩

theorem receiveEntries_invariant (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (id : BlockId) (prior : StateInvariant c s) (base : EffectInvariant c s e) :
    EffectInvariant c s (receiveEntries c s e r sender id) := by
  unfold receiveEntries
  split
  · rename_i b branch found path
    dsimp only
    split
    · rename_i enabled
      simp at enabled
      let next := { s.nodes r with
        branch := branch, commitIndex := max (s.nodes r).commitIndex b.commitHint }
      have updated : c.honest r -> NodeInvariant c (e.apply s) next := by
        intro honest
        have checked := received_entries_node_invariant c s (s.nodes r) (prior r honest)
          id b branch found enabled.1.1.1.1.1.2 enabled.1.1.2 enabled.1.2
        exact checked.history (effect_blocks_prefix s e) (effect_signatures_prefix s e)
      exact ((base.vote r next id updated (fun _ => Nat.le_max_left _ _)).refresh r).enqueue
        sender r (.vote ⟨r, b.view, id⟩)
    · exact base
  · exact base

theorem receiveVote_invariant (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (v : Vote) (prior : StateInvariant c s) (base : EffectInvariant c s e) :
    EffectInvariant c s (receiveVote c s e r sender v) := by
  dsimp only [receiveVote]
  split
  · split
    · apply base.setLocal
      · intro honest
        have old : NodeInvariant c s (addVote (s.nodes r) v) := by
          simpa only [NodeInvariant, addVote] using prior r honest
        exact old.refresh.history (effect_blocks_prefix s e) (effect_signatures_prefix s e)
      · intro honest
        exact refresh_audit_bound c s (addVote (s.nodes r) v) (prior r honest).1
    · exact base
  · exact base

theorem receiveChange_invariant (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (report : ViewChange) (prior : StateInvariant c s) (base : EffectInvariant c s e) :
    EffectInvariant c s (receiveChange c s e r sender report) := by
  dsimp only [receiveChange]
  split
  · apply base.setLocal
    · intro honest
      simpa only [NodeInvariant] using
        (prior r honest).history (effect_blocks_prefix s e) (effect_signatures_prefix s e)
    · intro _
      exact Nat.le_max_left _ _
  · exact base

theorem receiveNewView_invariant (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (id : BlockId) (reports : List ViewChange) (base : EffectInvariant c s e) :
    EffectInvariant c s (receiveNewView c s e r sender id reports) := by
  unfold receiveNewView
  split
  · rename_i b branch found path
    dsimp only
    split
    · rename_i enabled
      simp only [Bool.and_eq_true] at enabled
      let next := { s.nodes r with
        view := b.view, branch := branch, leader := false, stable := false,
        entered := true, votes := [], changes := [],
        commitIndex := min (s.nodes r).commitIndex
          (commonLength (s.nodes r).branch branch.dropLast) }
      have updated : c.honest r -> NodeInvariant c (e.apply s) next := by
        intro _
        have checked := received_new_view_node_invariant c s (s.nodes r) id b branch
          found path enabled.1.1.1.2
        simpa only [NodeInvariant, next] using
          checked.history (effect_blocks_prefix s e) (effect_signatures_prefix s e)
      exact (base.vote r next id updated (fun _ => Nat.le_max_left _ _)).enqueue
        sender r (.vote ⟨r, b.view, id⟩)
    · exact base
  · exact base

theorem timeout_invariant (c : Config) (s : State) (r : Replica) (e : Effect)
    (prior : StateInvariant c s) (transition : timeout c s r = some e) :
    EffectInvariant c s e := by
  unfold timeout at transition
  split at transition
  · contradiction
  · cases leader : c.leader ((s.nodes r).view + 1) with
    | none => simp [leader] at transition
    | some target =>
      simp only [leader, bind, pure, Option.bind, Option.some.injEq] at transition
      subst e
      let node := s.nodes r
      let next := { node with
        view := node.view + 1, leader := false, stable := false, entered := false,
        votes := [], changes := [] }
      have base := effect_invariant_of_nodes prior (Effect.unchanged s) rfl
      have updated : c.honest r -> NodeInvariant c ((Effect.unchanged s).apply s) next := by
        intro honest
        have old := (base r honest).1
        exact ⟨old.1, old.2.1, by simp [next]⟩
      exact ((base.setLocal r next updated (fun _ => Nat.le_max_left _ _)).append_signatures
        [⟨r, .viewChange (node.view + 1) node.branch⟩]).enqueue target r
        (.viewChange ⟨r, node.view + 1, node.branch⟩)

theorem deliver_invariant (c : Config) (s : State) (r sender : Replica) (e : Effect)
    (prior : StateInvariant c s) (transition : deliver c s r sender = some e) :
    EffectInvariant c s e := by
  simp only [deliver, pure] at transition
  split at transition
  · contradiction
  · split at transition
    · contradiction
    · rename_i message rest channel
      have base := effect_invariant_of_nodes prior
        ((Effect.unchanged s).setChannel r sender rest) rfl
      cases message with
      | appendEntries id =>
        simp only [Option.some.injEq] at transition
        subst e
        exact receiveEntries_invariant c s _ r sender id prior base
      | vote v =>
        simp only [Option.some.injEq] at transition
        subst e
        exact receiveVote_invariant c s _ r sender v prior base
      | viewChange report =>
        simp only [Option.some.injEq] at transition
        subst e
        exact receiveChange_invariant c s _ r sender report prior base
      | newView id reports =>
        simp only [Option.some.injEq] at transition
        subst e
        exact receiveNewView_invariant c s _ r sender id reports base

theorem dispatch_invariant (c : Config) (s : State) (a : Action) (e : Effect)
    (prior : StateInvariant c s) (transition : dispatch c s a = some e) :
    EffectInvariant c s e := by
  cases a with
  | propose r tx => exact propose_invariant c s r tx e prior transition
  | becomeLeader r reports chosen =>
    exact becomeLeader_invariant c s r reports chosen e prior transition
  | timeout r => exact timeout_invariant c s r e prior transition
  | deliver r sender => exact deliver_invariant c s r sender e prior transition
  | byzantineState actor node =>
    simp only [dispatch] at transition
    split at transition
    · rename_i enabled
      have bad : actor ∈ c.byzantine := List.contains_iff_mem.mp enabled
      simp only [Option.some.injEq] at transition
      subst e
      intro r honest
      have different : r ≠ actor := by
        intro same
        exact honest.2 (same ▸ bad)
      simp only [Effect.setLocal, Effect.unchanged, ite_eq_right different]
      exact ⟨(prior r honest).history (effect_blocks_prefix s _) (effect_signatures_prefix s _),
        Nat.le_max_left _ _⟩
    · contradiction
  | _ =>
    simp only [dispatch] at transition
    repeat' first
      | contradiction
      | split at transition
    all_goals
      simp only [Option.some.injEq] at transition
      subst e
      exact effect_invariant_of_nodes prior _ rfl

theorem state_invariant (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : StateInvariant c s := by
  refine CCF.TransitionSystem.Reachable.rec (system := transitionSystem c)
    (motive := fun state _ => StateInvariant c state) ?_ ?_ reachable
  · intro state initialized
    rcases initialized with ⟨_, rfl⟩
    simp [StateInvariant, NodeInvariant, initialState, validBranch]
  · intro before after a _ transition prior
    obtain ⟨e, dispatched, rfl⟩ := Option.map_eq_some_iff.mp transition
    intro r honest
    exact (dispatch_invariant c before a e prior dispatched r honest).1

theorem audit_index_step_bound (c : Config) (before after : State) (a : Action)
    (reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) :
    forall r, c.honest r ->
      (after.nodes r).auditIndex <= max (before.nodes r).auditIndex (after.nodes r).branch.length := by
  obtain ⟨e, dispatched, rfl⟩ := Option.map_eq_some_iff.mp transition
  intro r honest
  exact (dispatch_invariant c before a e (state_invariant c before reachable)
    dispatched r honest).2

theorem well_formed_branches (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : WellFormedBranches c s := by
  intro r honest
  exact (state_invariant c s reachable r honest).1

theorem commit_index_bounds (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) :
    forall r, c.honest r -> (s.nodes r).commitIndex <= (s.nodes r).branch.length := by
  intro r honest
  exact (state_invariant c s reachable r honest).2.1

theorem view_monotonic (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : ViewMonotonic c s := by
  exact view_monotonic_of_well_formed c s (well_formed_branches c s reachable)

theorem view_stabilization (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : ViewStabilization c s := by
  exact view_stabilization_of_well_formed c s (well_formed_branches c s reachable)

end PirateShip.Proofs
