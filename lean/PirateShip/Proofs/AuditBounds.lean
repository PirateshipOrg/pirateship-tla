module

public import PirateShip.Proofs.BranchValidity

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

theorem valid_branch_member_height (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (id : BlockId) (member : id ∈ branch) :
    height s id <= branch.length := by
  obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [valid_branch_height c s branch valid i id atIndex]
  omega

theorem embedded_certificate_member (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (carrier : BlockId) (b : Block) (qc : Certificate)
    (member : carrier ∈ branch) (found : s.blocks[carrier]? = some b)
    (embedded : b.auditQC = some qc) : qc.block ∈ branch := by
  obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
  have checked := List.all_eq_true.mp valid (carrier, i)
    (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)
  simp only [found, Option.any_some, Bool.and_eq_true] at checked
  have certificate := checked.2
  simp only [embedded, Option.all_some, Bool.and_eq_true, List.contains_iff_mem] at certificate
  exact List.mem_of_mem_take certificate.2

theorem slowAuditHeight_le_branch (c : Config) (s : State) (branch : Branch)
    (valid : validBranch c s branch = true) (qcs : List Certificate) :
    slowAuditHeight s branch qcs <= branch.length := by
  unfold slowAuditHeight
  apply List.foldlRecOn (motive := fun n => n <= branch.length) qcs _ (Nat.zero_le _)
  intro start bound outer _
  apply List.foldlRecOn (motive := fun n => n <= branch.length) branch _ bound
  intro n current carrier member
  split
  · exact current
  · rename_i inner embedded
    obtain ⟨b, found, qc⟩ := Option.bind_eq_some_iff.mp embedded
    have target := embedded_certificate_member c s branch valid carrier b inner member found qc
    have heightBound := valid_branch_member_height c s branch valid inner.block target
    split <;> omega

theorem fastAuditHeight_le_branch (c : Config) (s : State) (node : LocalState)
    (valid : validBranch c s node.branch = true) (qcs : List Certificate) :
    fastAuditHeight c s node qcs <= node.branch.length := by
  dsimp only [fastAuditHeight]
  split
  · exact Nat.zero_le _
  · apply List.foldlRecOn (motive := fun n => n <= node.branch.length)
      node.branch _ (Nat.zero_le _)
    intro n bound id member
    have heightBound := valid_branch_member_height c s node.branch valid id member
    split <;> omega

/-- Refresh can retain an old oversized index, but cannot create a new oversized audit. -/
theorem refresh_audit_bound (c : Config) (s : State) (node : LocalState)
    (valid : validBranch c s node.branch = true) :
    (refresh c s node).auditIndex <= max node.auditIndex node.branch.length := by
  change max node.auditIndex (max _ _) <= max node.auditIndex node.branch.length
  refine Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.max_le.mpr ⟨?_, ?_⟩⟩
  · exact (slowAuditHeight_le_branch c s node.branch valid _).trans (Nat.le_max_right _ _)
  · apply (fastAuditHeight_le_branch c s _ ?_ _).trans (Nat.le_max_right _ _)
    exact valid

theorem refresh_audit_in_bounds (c : Config) (s : State) (node : LocalState)
    (valid : validBranch c s node.branch = true)
    (bound : node.auditIndex <= node.branch.length) :
    (refresh c s node).auditIndex <= node.branch.length := by
  exact (refresh_audit_bound c s node valid).trans (Nat.max_le.mpr ⟨bound, Nat.le_refl _⟩)

end PirateShip.Proofs
