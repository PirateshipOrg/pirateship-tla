module

public import PirateShip.Properties.Defs
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

theorem audit_quorum_intersection (members left right : Finset Replica) (u f : Nat)
    (size : 2 * u + f + 1 <= members.card)
    (leftMembers : left ⊆ members) (rightMembers : right ⊆ members)
    (leftSize : members.card - u <= left.card)
    (rightSize : members.card - u <= right.card) :
    f < (left ∩ right).card := by
  have unionBound := Finset.card_le_card (Finset.union_subset leftMembers rightMembers)
  have equation := Finset.card_union_add_card_inter left right
  omega

theorem effect_blocks_prefix (s : State) (e : Effect) :
    s.blocks.IsPrefix (e.apply s).blocks := by
  exact ⟨e.blocks, rfl⟩

theorem effect_signatures_prefix (s : State) (e : Effect) :
    s.signatures.IsPrefix (e.apply s).signatures := by
  exact ⟨e.signatures, rfl⟩

theorem step_blocks_prefix (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) :
    before.blocks.IsPrefix after.blocks := by
  unfold step at transition
  cases h : dispatch c before a with
  | none => simp [h] at transition
  | some e =>
    simp only [h, Option.map_some, Option.some.injEq] at transition
    subst after
    exact effect_blocks_prefix before e

theorem step_signatures_prefix (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) :
    before.signatures.IsPrefix after.signatures := by
  unfold step at transition
  cases h : dispatch c before a with
  | none => simp [h] at transition
  | some e =>
    simp only [h, Option.map_some, Option.some.injEq] at transition
    subst after
    exact effect_signatures_prefix before e

theorem attacks_monotonic (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) :
    before.byzActions <= after.byzActions := by
  unfold step at transition
  cases h : dispatch c before a with
  | none => simp [h] at transition
  | some e =>
    simp only [h, Option.map_some, Option.some.injEq] at transition
    subst after
    simp [Effect.apply]

theorem stutter_enabled (c : Config) (s : State) : step c s .stutter = some s := by
  cases s
  simp [step, dispatch, Effect.unchanged, Effect.apply]

theorem initial_index_bounds (c : Config) : IndexBounds c (initialState c) := by
  simp [IndexBounds, initialState]

theorem initial_well_formed (c : Config) : WellFormedBranches c (initialState c) := by
  simp [WellFormedBranches, initialState, validBranch]

theorem initial_audit_agreement (c : Config) : AuditedAgreement c (initialState c) := by
  simp [AuditedAgreement, audited, initialState]

theorem initial_commit_agreement (c : Config) : CommittedAgreement c (initialState c) := by
  simp [CommittedAgreement, committed, initialState, IsPrefixWithoutEmpty]

theorem initial_election_safety (c : Config) : OneLeaderPerView c (initialState c) := by
  intro r t _ _ hr ht _
  simp only [initialState, beq_iff_eq] at hr ht
  exact Option.some.inj (hr.symm.trans ht)

theorem refresh_audit_monotonic (c : Config) (s : State) (node : LocalState) :
    node.auditIndex <= (refresh c s node).auditIndex := by
  change node.auditIndex <= max node.auditIndex _
  exact Nat.le_max_left _ _

theorem byzantine_state_preserves_other_nodes (c : Config) (s : State)
    (attacker other : Replica) (node : LocalState)
    (bad : attacker ∈ c.byzantine) (different : other ≠ attacker) :
    ((step c s (.byzantineState attacker node)).map (fun next => next.nodes other)) =
      some (s.nodes other) := by
  simp [step, dispatch, bad, Effect.unchanged, Effect.apply, Effect.setLocal, different]

/-- A Byzantine signing operation cannot mint a signature under an honest identity. -/
theorem byzantine_sign_no_impersonation (c : Config) (s : State)
    (attacker honest : Replica) (payload query : Payload)
    (bad : attacker ∈ c.byzantine) (good : c.honest honest) :
    ((step c s (.byzantineSign attacker payload)).map
      (fun next => issued next honest query)) = some (issued s honest query) := by
  have different : honest ≠ attacker := by
    intro eq
    exact good.2 (eq ▸ bad)
  simp [step, dispatch, bad, Effect.unchanged, Effect.apply, issued, different]

end PirateShip.Proofs
