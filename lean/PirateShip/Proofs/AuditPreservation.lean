module

public import PirateShip.Proofs.WellFormed

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

@[simp] theorem refresh_branch (c : Config) (s : State) (node : LocalState) :
    (refresh c s node).branch = node.branch := rfl

theorem branch_prefix_of_no_installation (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r)
    (notInstalling : ¬MayInstallBranch before a r) :
    (before.nodes r).branch.IsPrefix (after.nodes r).branch := by
  have notBad : r ∉ c.byzantine := honest.2
  obtain ⟨e, dispatched, rfl⟩ := Option.map_eq_some_iff.mp transition
  change (before.nodes r).branch.IsPrefix (e.nodes r).branch
  cases a <;>
    simp only [dispatch, propose, timeout, becomeLeader, deliver, bind, pure,
      Option.bind] at dispatched
  all_goals
    repeat' first
      | contradiction
      | split at dispatched
  all_goals
    try simp only [Option.some.injEq] at dispatched
    subst e
    simp only [receiveEntries, receiveVote, receiveChange, receiveNewView,
      broadcast_nodes, enqueue_nodes, Effect.setChannel, Effect.setLocal,
      Effect.unchanged, voteEffect, Effect.apply, addVote]
    repeat' split
  all_goals
    simp_all [MayInstallBranch]
    repeat' split
  all_goals simp_all

theorem audited_prefix_of_branch_prefix (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r)
    (growth : (before.nodes r).branch.IsPrefix (after.nodes r).branch) :
    (audited before r).IsPrefix (audited after r) := by
  have monotonic := monotonic_audit_index c before after a transition r honest
  apply List.prefix_take_iff.mpr
  refine ⟨(List.take_prefix _ _).trans growth, ?_⟩
  simp only [audited, List.length_take]
  omega

theorem audited_append_only_of_no_installation (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r)
    (notInstalling : ¬MayInstallBranch before a r) :
    (audited before r).IsPrefix (audited after r) := by
  exact audited_prefix_of_branch_prefix c before after a transition r honest
    (branch_prefix_of_no_installation c before after a transition r honest notInstalling)

theorem audit_index_bound_of_no_installation (c : Config) (before after : State) (a : Action)
    (reachable : (transitionSystem c).Reachable before)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r)
    (notInstalling : ¬MayInstallBranch before a r)
    (bound : (before.nodes r).auditIndex <= (before.nodes r).branch.length) :
    (after.nodes r).auditIndex <= (after.nodes r).branch.length := by
  have growth := branch_prefix_of_no_installation c before after a transition r honest notInstalling
  exact (audit_index_step_bound c before after a reachable transition r honest).trans
    (Nat.max_le.mpr ⟨bound.trans growth.length_le, Nat.le_refl _⟩)

end PirateShip.Proofs
