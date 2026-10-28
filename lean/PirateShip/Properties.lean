module

public import PirateShip.Properties.Defs
public import PirateShip.Proofs.Foundations
public import PirateShip.Proofs.Local
public import PirateShip.Proofs.BranchShape
public import PirateShip.Proofs.History
public import PirateShip.Proofs.BranchValidity
public import PirateShip.Proofs.AuditBounds
public import PirateShip.Proofs.WellFormed
public import PirateShip.Proofs.AuditPreservation

@[expose] public section

namespace PirateShip.Properties

open Model

/-- Valid executions cannot rewrite already published block records. -/
theorem published_blocks_persist (c : Config) (before after : State) (a : Action)
    (transition : (transitionSystem c).step before a = some after) :
    before.blocks.IsPrefix after.blocks := by
  exact Proofs.step_blocks_prefix c before after a transition

/-- Valid executions cannot erase previously issued authentication evidence. -/
theorem signatures_persist (c : Config) (before after : State) (a : Action)
    (transition : (transitionSystem c).step before a = some after) :
    before.signatures.IsPrefix after.signatures := by
  exact Proofs.step_signatures_prefix c before after a transition

/-- A fixed validated branch stays valid even when a step changes local branches. -/
theorem validated_branch_persists (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (branch : Branch)
    (valid : validBranch c before branch = true) : validBranch c after branch = true := by
  exact Proofs.valid_branch_persists c before after a transition branch valid

theorem validated_certificate_persists (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (qc : Certificate)
    (valid : validCertificate c before qc = true) : validCertificate c after qc = true := by
  exact Proofs.validCertificate_of_prefix c before after
    (Proofs.step_blocks_prefix c before after a transition)
    (Proofs.step_signatures_prefix c before after a transition) qc valid

theorem successful_chain_persists (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (id : BlockId) (branch : Branch)
    (found : chain before id = some branch) : chain after id = some branch := by
  exact Proofs.chain_of_prefix before after
    (Proofs.step_blocks_prefix c before after a transition) id branch found

/-- Honest leaders in the same view are the unique designated replica. -/
theorem election_safety (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : OneLeaderPerView c s := by
  exact Proofs.election_safety c s reachable

/-- Every enabled step preserves honest audit indices, even from an arbitrary state. -/
theorem monotonic_audit_index (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) : MonotonicAuditIndex c before after := by
  exact Proofs.monotonic_audit_index c before after a transition

theorem view_monotonic_of_well_formed (c : Config) (s : State)
    (wellFormed : WellFormedBranches c s) : ViewMonotonic c s := by
  exact Proofs.view_monotonic_of_well_formed c s wellFormed

theorem view_stabilization_of_well_formed (c : Config) (s : State)
    (wellFormed : WellFormedBranches c s) : ViewStabilization c s := by
  exact Proofs.view_stabilization_of_well_formed c s wellFormed

theorem well_formed_branches (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : WellFormedBranches c s := by
  exact Proofs.well_formed_branches c s reachable

theorem commit_index_bounds (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) :
    forall r, c.honest r -> (s.nodes r).commitIndex <= (s.nodes r).branch.length := by
  exact Proofs.commit_index_bounds c s reachable

/-- Every step bounds new audits; a retained index still needs branch-installation safety. -/
theorem audit_index_step_bound (c : Config) (before after : State) (a : Action)
    (reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) :
    forall r, c.honest r ->
      (after.nodes r).auditIndex <= max (before.nodes r).auditIndex (after.nodes r).branch.length := by
  exact Proofs.audit_index_step_bound c before after a reachable transition

theorem audit_index_bound_of_no_installation (c : Config) (before after : State) (a : Action)
    (reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r)
    (notInstalling : ¬MayInstallBranch before a r)
    (bound : (before.nodes r).auditIndex <= (before.nodes r).branch.length) :
    (after.nodes r).auditIndex <= (after.nodes r).branch.length := by
  exact Proofs.audit_index_bound_of_no_installation c before after a
    reachable transition r honest notInstalling bound

/-- Includes other replicas' installations and all Byzantine actions, without reachability. -/
theorem audited_append_only_of_no_installation (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r)
    (notInstalling : ¬MayInstallBranch before a r) :
    (audited before r).IsPrefix (audited after r) := by
  exact Proofs.audited_append_only_of_no_installation c before after a
    transition r honest notInstalling

theorem view_monotonic (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : ViewMonotonic c s := by
  exact Proofs.view_monotonic c s reachable

theorem view_stabilization (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : ViewStabilization c s := by
  exact Proofs.view_stabilization c s reachable

theorem well_formed_branches_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : Always (WellFormedBranches c) trace := by
  intro s member
  exact well_formed_branches c s (valid.reachable member)

theorem view_monotonic_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : Always (ViewMonotonic c) trace := by
  intro s member
  exact view_monotonic c s (valid.reachable member)

theorem view_stabilization_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : Always (ViewStabilization c) trace := by
  intro s member
  exact view_stabilization c s (valid.reachable member)

theorem election_safety_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : Always (OneLeaderPerView c) trace := by
  intro s member
  exact election_safety c s (valid.reachable member)

theorem monotonic_audit_index_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : AlwaysStep (MonotonicAuditIndex c) trace := by
  intro i before after current next
  obtain ⟨action, transition⟩ := valid.2 i before after current next
  exact monotonic_audit_index c before after action transition

end PirateShip.Properties
