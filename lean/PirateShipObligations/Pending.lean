module

public import PirateShip.Properties

@[expose] public section

/-!
UNFINISHED PROOFS. This module is not imported by the trusted PirateShip root.
Each `sorry` is an explicit outstanding obligation, not an established safety result.
Completed results below are compatibility wrappers around the checked library.
-/

namespace PirateShipObligations

open PirateShip.Model PirateShip.Properties

/-- Commit bounds are proved; audit bounds across branch replacement remain pending. -/
theorem index_bounds (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : IndexBounds c s := by
  have auditBounds : forall r, c.honest r ->
      (s.nodes r).auditIndex <= (s.nodes r).branch.length := by
    refine CCF.TransitionSystem.Reachable.rec (system := transitionSystem c)
      (motive := fun state _ => forall r, c.honest r ->
        (state.nodes r).auditIndex <= (state.nodes r).branch.length) ?_ ?_ reachable
    · intro state initialized
      rcases initialized with ⟨_, rfl⟩
      intro r _
      simp [initialState]
    · intro before after a prior transition ih r honest
      by_cases installing : MayInstallBranch before a r
      · sorry
      · exact audit_index_bound_of_no_installation c before after a
          prior transition r honest installing (ih r honest)
  intro r honest
  exact ⟨PirateShip.Properties.commit_index_bounds c s reachable r honest, auditBounds r honest⟩

/-- Pending: clean-execution history invariant linking majority votes and stabilization. -/
theorem committed_agreement (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : CommittedAgreement c s := by
  sorry

/-- Pending: authenticated vote histories, QC intersection, and fast/slow branch preservation. -/
theorem audited_agreement (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : AuditedAgreement c s := by
  sorry

/-- Proved in the checked library; retained here for compatibility. -/
theorem election_safety (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : OneLeaderPerView c s := by
  exact PirateShip.Properties.election_safety c s reachable

/-- Proved by the checked coupled branch/commit/installed-view invariant. -/
theorem well_formed_branches (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : WellFormedBranches c s := by
  exact PirateShip.Properties.well_formed_branches c s reachable

/-- Proved in the checked library; retained here for compatibility. -/
theorem view_monotonic (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : ViewMonotonic c s := by
  exact PirateShip.Properties.view_monotonic c s reachable

/-- Proved in the checked library; retained here for compatibility. -/
theorem view_stabilization (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : ViewStabilization c s := by
  exact PirateShip.Properties.view_stabilization c s reachable

/-- Pending: clean view changes preserve committed history, modulo empty control batches. -/
theorem committed_append_only (c : Config) (before after : State) (a : Action)
    (reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) : CommittedAppendOnly c before after := by
  sorry

/-- Pending: slow- and fast-audited history survives validated new-view installation. -/
theorem audited_append_only (c : Config) (before after : State) (a : Action)
    (reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) : AuditedAppendOnly c before after := by
  intro r honest
  by_cases installing : MayInstallBranch before a r
  · sorry
  · exact audited_append_only_of_no_installation c before after a transition r honest installing

/-- Proved for every enabled step, without needing the reachability premise. -/
theorem monotonic_audit_index (c : Config) (before after : State) (a : Action)
    (_reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) : MonotonicAuditIndex c before after := by
  exact PirateShip.Properties.monotonic_audit_index c before after a transition

/-- Conditional on the unfinished reachable-state proof above. -/
theorem audited_agreement_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : Always (AuditedAgreement c) trace := by
  intro s member
  exact audited_agreement c s (valid.reachable member)

/-- Conditional on the unfinished step proof above. -/
theorem audited_append_only_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : AlwaysStep (AuditedAppendOnly c) trace := by
  intro i before after current next
  obtain ⟨action, transition⟩ := valid.2 i before after current next
  exact audited_append_only c before after action
    (valid.reachable (Stream'.Seq.get?_mem current)) transition

/-- Conditional on the unfinished clean-execution step proof above. -/
theorem committed_append_only_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : AlwaysStep (CommittedAppendOnly c) trace := by
  intro i before after current next
  obtain ⟨action, transition⟩ := valid.2 i before after current next
  exact committed_append_only c before after action
    (valid.reachable (Stream'.Seq.get?_mem current)) transition

/-- Proved in the checked library, independently of the unfinished obligations. -/
theorem monotonic_audit_index_on_trace (c : Config) (trace : Trace)
    (valid : trace.Valid (transitionSystem c)) : AlwaysStep (MonotonicAuditIndex c) trace := by
  exact PirateShip.Properties.monotonic_audit_index_on_trace c trace valid

end PirateShipObligations
