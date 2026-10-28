module

public import PirateShip.Proofs.Foundations

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

@[simp] theorem enqueue_nodes (e : Effect) (recipient sender : Replica) (m : Message) :
    (e.enqueue recipient sender m).nodes = e.nodes := rfl

@[simp] theorem broadcast_nodes (e : Effect) (c : Config) (sender : Replica) (m : Message) :
    (e.broadcast c sender m).nodes = e.nodes := by
  unfold Effect.broadcast
  generalize c.replicas = replicas
  induction replicas generalizing e with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.foldl_cons, ih]
    split <;> rfl

@[simp] theorem refresh_view (c : Config) (s : State) (node : LocalState) :
    (refresh c s node).view = node.view := rfl

@[simp] theorem refresh_leader (c : Config) (s : State) (node : LocalState) :
    (refresh c s node).leader = node.leader := rfl

def Designated (c : Config) (r : Replica) (node : LocalState) : Prop :=
  node.leader = true -> c.leader node.view = some r

def LocalProgress (c : Config) (r : Replica) (before after : LocalState) : Prop :=
  before.auditIndex <= after.auditIndex /\
  (Designated c r before -> Designated c r after)

theorem dispatch_local_progress (c : Config) (s : State) (a : Action) (e : Effect)
    (transition : dispatch c s a = some e) (r : Replica) (honest : c.honest r) :
    LocalProgress c r (s.nodes r) (e.nodes r) := by
  have notBad : r ∉ c.byzantine := honest.2
  cases a <;>
    simp only [dispatch, propose, timeout, becomeLeader, deliver, bind, pure,
      Option.bind] at transition
  -- Separate enabled handlers from rejected actions before inspecting node updates.
  all_goals
    repeat' first
      | contradiction
      | split at transition
  all_goals
    try simp only [Option.some.injEq] at transition
    subst e
    simp only [receiveEntries, receiveVote, receiveChange, receiveNewView,
      broadcast_nodes, enqueue_nodes, Effect.setChannel, Effect.setLocal,
      Effect.unchanged, voteEffect, Effect.apply, addVote,
      LocalProgress, Designated]
    repeat' split
  all_goals
    simp_all
    repeat' split
  all_goals try simp_all
  all_goals
    change _ <= max _ _
    exact Nat.le_max_left _ _

theorem step_local_progress (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (r : Replica) (honest : c.honest r) :
    LocalProgress c r (before.nodes r) (after.nodes r) := by
  obtain ⟨e, dispatched, rfl⟩ := Option.map_eq_some_iff.mp transition
  exact dispatch_local_progress c before a e dispatched r honest

theorem designated_leaders (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) :
    forall r, c.honest r -> Designated c r (s.nodes r) := by
  refine CCF.TransitionSystem.Reachable.rec (system := transitionSystem c)
    (motive := fun state _ => forall r, c.honest r -> Designated c r (state.nodes r))
    ?_ ?_ reachable
  · intro state initialized
    rcases initialized with ⟨_, rfl⟩
    intro r _
    simp [Designated, initialState]
  · intro before after a _ transition ih r honest
    exact (step_local_progress c before after a transition r honest).2 (ih r honest)

theorem election_safety (c : Config) (s : State)
    (reachable : (transitionSystem c).Reachable s) : OneLeaderPerView c s := by
  intro r t hr ht leaderR leaderT sameView
  have designatedR := designated_leaders c s reachable r hr leaderR
  have designatedT := designated_leaders c s reachable t ht leaderT
  rw [sameView] at designatedR
  exact Option.some.inj (designatedR.symm.trans designatedT)

theorem monotonic_audit_index (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) : MonotonicAuditIndex c before after := by
  intro r honest
  exact (step_local_progress c before after a transition r honest).1

end PirateShip.Proofs
