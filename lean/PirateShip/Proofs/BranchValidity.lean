module

public import PirateShip.Proofs.History
public import PirateShip.Proofs.BranchShape

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

theorem valid_branch_lookup (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (i : Nat) (id : BlockId)
    (atIndex : branch[i]? = some id) : exists b, s.blocks[id]? = some b := by
  have checked := List.all_eq_true.mp valid (id, i)
    (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)
  obtain ⟨b, found, _⟩ := (Option.any_eq_true _ _).mp checked
  exact ⟨b, found⟩

theorem valid_branch_chainAux (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (i : Nat) (id : BlockId)
    (atIndex : branch[i]? = some id) :
    chainAux s.blocks (i + 1) id = some (branch.take (i + 1)) := by
  obtain ⟨b, found⟩ := valid_branch_lookup c s branch valid i id atIndex
  have parent := (valid_branch_shape_at c s branch valid i id b atIndex found).1
  induction i generalizing id b with
  | zero =>
    simp only [List.take_zero, List.getLast?_nil] at parent
    simp [chainAux, found, parent, List.take_add_one, atIndex]
  | succ i ih =>
    have bound := (List.getElem?_eq_some_iff.mp atIndex).1
    have previous : i < branch.length := by omega
    have atPrevious : branch[i]? = some branch[i] := List.getElem?_eq_getElem previous
    obtain ⟨p, previousFound⟩ := valid_branch_lookup c s branch valid i branch[i] atPrevious
    have previousParent :=
      (valid_branch_shape_at c s branch valid i branch[i] p atPrevious previousFound).1
    have path := ih branch[i] atPrevious p previousFound previousParent
    have linked : b.parent = some branch[i] := by
      simpa [List.getLast?_take, atPrevious] using parent
    rw [chainAux, found]
    simp only [bind, pure, Option.bind, linked, path]
    rw [List.take_add_one (i := i + 1), atIndex]
    rfl

theorem valid_branch_nodup (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) : branch.Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj equal
  have pathI := valid_branch_chainAux c s branch valid i branch[i]
    (List.getElem?_eq_getElem hi)
  have pathJ := valid_branch_chainAux c s branch valid j branch[j]
    (List.getElem?_eq_getElem hj)
  have sameI := chainAux_of_prefix (before := s.blocks) (after := s.blocks)
    ⟨[], by simp⟩ (i + 1) (branch.length + 1) (by omega) _ _ pathI
  have sameJ := chainAux_of_prefix (before := s.blocks) (after := s.blocks)
    ⟨[], by simp⟩ (j + 1) (branch.length + 1) (by omega) _ _ pathJ
  rw [equal] at sameI
  have lengths := congrArg List.length (Option.some.inj (sameI.symm.trans sameJ))
  simp only [List.length_take] at lengths
  omega

theorem valid_branch_length (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) : branch.length <= s.blocks.length := by
  have subset : branch ⊆ List.range s.blocks.length := by
    intro id member
    obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨b, found⟩ := valid_branch_lookup c s branch valid i id atIndex
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp found).1
  simpa using (valid_branch_nodup c s branch valid).length_le_of_subset subset

theorem valid_branch_chain (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (i : Nat) (id : BlockId)
    (atIndex : branch[i]? = some id) : chain s id = some (branch.take (i + 1)) := by
  have branchLength := valid_branch_length c s branch valid
  have indexBound := (List.getElem?_eq_some_iff.mp atIndex).1
  exact chainAux_of_prefix (before := s.blocks) (after := s.blocks) ⟨[], by simp⟩
    (i + 1) (s.blocks.length + 1) (by omega) id _
    (valid_branch_chainAux c s branch valid i id atIndex)

theorem valid_branch_height (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (i : Nat) (id : BlockId)
    (atIndex : branch[i]? = some id) : height s id = i + 1 := by
  have path := valid_branch_chain c s branch valid i id atIndex
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  simp [height, path, List.length_take, Nat.min_eq_left (by omega : i + 1 <= branch.length)]

theorem commitHeight_le_branch (c : Config) (s : State) (node : LocalState)
    (valid : validBranch c s node.branch = true) :
    commitHeight c s node <= node.branch.length := by
  have aux : forall ids : Branch, ids ⊆ node.branch -> forall start,
      start <= node.branch.length ->
      ids.foldl (fun n id =>
        if (votesFor s node id).length >= c.commitQuorum then max n (height s id) else n)
        start <= node.branch.length := by
    intro ids
    induction ids with
    | nil => intro _ start bound; exact bound
    | cons id rest ih =>
      intro subset start bound
      simp only [List.foldl_cons]
      apply ih (fun id member => subset (List.mem_cons_of_mem _ member))
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp (subset (List.mem_cons_self))
      have indexBound := (List.getElem?_eq_some_iff.mp atIndex).1
      have idHeight := valid_branch_height c s node.branch valid i id atIndex
      split <;> omega
  exact aux node.branch (fun _ member => member) 0 (Nat.zero_le _)

theorem refresh_commit_bound (c : Config) (s : State) (node : LocalState)
    (valid : validBranch c s node.branch = true)
    (bound : node.commitIndex <= node.branch.length) :
    (refresh c s node).commitIndex <= node.branch.length := by
  have heightBound := commitHeight_le_branch c s node valid
  have choose (condition : Prop) [Decidable condition] :
      (if condition then max node.commitIndex (commitHeight c s node) else node.commitIndex) <=
      node.branch.length := by
    split <;> omega
  exact choose _

theorem certificateFor_valid (c : Config) (s : State) (node : LocalState) (qc : Certificate)
    (formed : certificateFor c s node = some qc) :
    validCertificate c s qc = true /\ qc.block ∈ node.branch /\ qc.view = node.view := by
  obtain ⟨id, member, found⟩ := List.exists_of_findSome?_eq_some formed
  dsimp only at found
  split at found
  · simp only [Option.some.injEq] at found
    subst qc
    exact ⟨by assumption, by simpa using member, rfl⟩
  · contradiction

theorem chosen_branch_valid (c : Config) (s : State) (view : Nat)
    (reports : List ViewChange) (chosen : Branch)
    (evidence : validEvidence c s view reports = true)
    (selected : chosenBranch c s reports chosen = true) :
    validBranch c s chosen = true /\ 0 < view /\
    chosen.all (fun id => (s.blocks[id]?).any (fun b => b.view < view)) = true := by
  simp only [chosenBranch, List.any_eq_true, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq] at selected
  obtain ⟨report, member, chosenEq, _⟩ := selected
  simp only [validEvidence, Bool.and_eq_true, List.all_eq_true] at evidence
  have reportValid := evidence.2 report member.1.1.1
  have sameView : report.view = view := beq_iff_eq.mp reportValid.1
  have changed := reportValid.2
  simp only [validChange, Bool.and_eq_true] at changed
  refine ⟨by simpa [chosenEq] using changed.1.2, ?_, ?_⟩
  · simpa [sameView] using changed.1.1.1.2
  · simpa [sameView, chosenEq] using changed.2

end PirateShip.Proofs
