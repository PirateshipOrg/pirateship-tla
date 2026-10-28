module

public import PirateShip.Properties.Defs

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

theorem valid_branch_shape_at (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (i : Nat) (id : BlockId) (b : Block)
    (atIndex : branch[i]? = some id) (atBlock : s.blocks[id]? = some b) :
    b.parent = (branch.take i).getLast? /\
    (forall parent p, b.parent = some parent -> s.blocks[parent]? = some p ->
      p.view <= b.view /\ (p.view < b.view -> b.transactions = [])) /\
    (b.transactions = [] -> b.view ≠ 0) := by
  have checked := List.all_eq_true.mp valid (id, i)
    (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)
  simp only [atBlock, Option.any_some, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨_, parent⟩, ordered⟩, _⟩, transactions⟩, stabilized⟩, _⟩
  refine ⟨parent, ?_, ?_⟩
  · intro parent p linked found
    have order := ordered
    have control := stabilized
    simp only [linked, Option.all_some, found, Option.any_some, decide_eq_true_eq] at order
    simp only [linked, Option.all_some, found, Bool.or_eq_true, beq_iff_eq] at control
    refine ⟨order, ?_⟩
    intro increasing
    have stabilization : b.stabilization = true := by
      rcases control with equal | control
      · omega
      · exact control
    simp [stabilization] at transactions
    exact transactions.1
  · intro empty
    cases stabilization : b.stabilization <;>
      simp [stabilization, empty] at transactions
    omega

theorem view_monotonic_of_well_formed (c : Config) (s : State)
    (wellFormed : WellFormedBranches c s) : ViewMonotonic c s := by
  intro r honest i left right a b atLeft atRight foundLeft foundRight
  have shape := valid_branch_shape_at c s (s.nodes r).branch (wellFormed r honest)
    (i + 1) right b atRight foundRight
  have previous : ((s.nodes r).branch.take (i + 1)).getLast? = some left := by
    simp [List.getLast?_take, atLeft]
  exact (shape.2.1 left a (shape.1.trans previous) foundLeft).1

theorem view_stabilization_of_well_formed (c : Config) (s : State)
    (wellFormed : WellFormedBranches c s) : ViewStabilization c s := by
  intro r honest
  constructor
  · intro id b member found empty
    obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
    exact (valid_branch_shape_at c s (s.nodes r).branch (wellFormed r honest)
      i id b atIndex found).2.2 empty
  · intro i left right a b atLeft atRight foundLeft foundRight increasing
    have shape := valid_branch_shape_at c s (s.nodes r).branch (wellFormed r honest)
      (i + 1) right b atRight foundRight
    have previous : ((s.nodes r).branch.take (i + 1)).getLast? = some left := by
      simp [List.getLast?_take, atLeft]
    exact (shape.2.1 left a (shape.1.trans previous) foundLeft).2 increasing

end PirateShip.Proofs
