module

public import PirateShip.Proofs.Foundations

@[expose] public section

namespace PirateShip.Proofs

open Model Properties

theorem lookup_of_prefix {before after : List Block} (growth : before.IsPrefix after)
    {id : BlockId} {b : Block} (found : before[id]? = some b) :
    after[id]? = some b := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp found
  exact List.getElem?_eq_some_iff.mpr
    ⟨Nat.lt_of_lt_of_le bound growth.length_le, (growth.getElem bound).symm.trans value⟩

theorem chainAux_of_prefix {before after : List Block} (growth : before.IsPrefix after)
    (fuel more : Nat) (enough : fuel <= more) (id : BlockId) (branch : Branch)
    (found : chainAux before fuel id = some branch) :
    chainAux after more id = some branch := by
  induction fuel generalizing more id branch with
  | zero => simp [chainAux] at found
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      cases block : before[id]? with
      | none => simp [chainAux, block] at found
      | some b =>
        have blockAfter := lookup_of_prefix growth block
        cases parent : b.parent with
        | none =>
          simpa [chainAux, block, blockAfter, parent] using found
        | some parentId =>
          simp only [chainAux, block, blockAfter, parent, bind, pure, Option.bind] at found ⊢
          cases path : chainAux before fuel parentId with
          | none => simp [path] at found
          | some ancestors =>
            have pathAfter := ih more (by omega) parentId ancestors path
            simpa [path, pathAfter] using found

theorem chain_of_prefix (before after : State) (growth : before.blocks.IsPrefix after.blocks)
    (id : BlockId) (branch : Branch) (found : chain before id = some branch) :
    chain after id = some branch := by
  exact chainAux_of_prefix growth _ _ (by have := growth.length_le; omega) id branch found

theorem issued_of_prefix (before after : State)
    (growth : before.signatures.IsPrefix after.signatures) (r : Replica) (p : Payload)
    (signed : issued before r p = true) : issued after r p = true := by
  simp only [issued, List.contains_iff_mem] at signed ⊢
  exact growth.subset signed

theorem supports_of_prefix (before after : State)
    (growth : before.blocks.IsPrefix after.blocks) (view : Nat) (id : BlockId) (v : Vote)
    (supported : supports before view id v = true) : supports after view id v = true := by
  simp only [supports, Bool.and_eq_true, Option.any_eq_true] at supported ⊢
  obtain ⟨⟨⟨sameView, target, targetFound, targetView⟩, vote, voteFound, voteView⟩,
    path, pathFound, member⟩ := supported
  exact ⟨⟨⟨sameView, target, lookup_of_prefix growth targetFound, targetView⟩,
    vote, lookup_of_prefix growth voteFound, voteView⟩,
    path, chain_of_prefix before after growth v.block path pathFound, member⟩

theorem validVote_of_prefix (c : Config) (before after : State)
    (blocks : before.blocks.IsPrefix after.blocks)
    (signatures : before.signatures.IsPrefix after.signatures) (v : Vote)
    (valid : validVote c before v = true) : validVote c after v = true := by
  simp only [validVote, Bool.and_eq_true, Option.any_eq_true] at valid ⊢
  obtain ⟨⟨member, signed⟩, b, found, sameView⟩ := valid
  exact ⟨⟨member, issued_of_prefix before after signatures _ _ signed⟩,
    b, lookup_of_prefix blocks found, sameView⟩

theorem validCertificate_of_prefix (c : Config) (before after : State)
    (blocks : before.blocks.IsPrefix after.blocks)
    (signatures : before.signatures.IsPrefix after.signatures) (qc : Certificate)
    (valid : validCertificate c before qc = true) : validCertificate c after qc = true := by
  simp only [validCertificate, Bool.and_eq_true, List.all_eq_true] at valid ⊢
  refine ⟨valid.1, ?_⟩
  intro v member
  have vote := valid.2 v member
  exact ⟨validVote_of_prefix c before after blocks signatures v vote.1,
    supports_of_prefix before after blocks qc.view qc.block v vote.2⟩

theorem signedBlock_of_prefix (c : Config) (before after : State)
    (blocks : before.blocks.IsPrefix after.blocks)
    (signatures : before.signatures.IsPrefix after.signatures) (id : BlockId)
    (valid : signedBlock c before id = true) : signedBlock c after id = true := by
  simp only [signedBlock, Option.any_eq_true] at valid ⊢
  obtain ⟨b, found, r, leader, signed⟩ := valid
  exact ⟨b, lookup_of_prefix blocks found, r, leader,
    issued_of_prefix before after signatures r (.proposal id) signed⟩

theorem validBranch_of_prefix (c : Config) (before after : State)
    (blocks : before.blocks.IsPrefix after.blocks)
    (signatures : before.signatures.IsPrefix after.signatures) (branch : Branch)
    (valid : validBranch c before branch = true) : validBranch c after branch = true := by
  apply List.all_eq_true.mpr
  intro entry member
  rcases entry with ⟨id, index⟩
  have checked := List.all_eq_true.mp valid (id, index) member
  obtain ⟨b, found, checked⟩ := (Option.any_eq_true _ _).mp checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨signed, parent⟩, ordered⟩, hint⟩, transactions⟩, stabilized⟩, qc⟩
  apply (Option.any_eq_true _ _).mpr
  refine ⟨b, lookup_of_prefix blocks found, ?_⟩
  have parentChecks :
      (b.parent.all fun parent =>
        (after.blocks[parent]?).any (fun p => p.view <= b.view)) = true /\
      (b.parent.all fun parent =>
        (after.blocks[parent]?).all (fun p => p.view == b.view || b.stabilization)) = true := by
    cases linked : b.parent with
    | none => simp
    | some parentId =>
      simp only [linked, Option.all_some, Option.any_eq_true] at ordered
      obtain ⟨p, parentFound, order⟩ := ordered
      have parentAfter := lookup_of_prefix blocks parentFound
      simpa only [linked, parentAfter, Option.all_some, Option.any_some] using
        And.intro order (by simpa only [linked, parentFound, Option.all_some] using stabilized)
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨signedBlock_of_prefix c before after blocks signatures id signed, parent⟩,
    parentChecks.1⟩, hint⟩, transactions⟩, parentChecks.2⟩, ?_⟩
  apply (Option.all_eq_true _ _).mpr
  intro certificate present
  have checked := (Option.all_eq_true _ _).mp qc certificate present
  simp only [Bool.and_eq_true] at checked ⊢
  exact ⟨⟨validCertificate_of_prefix c before after blocks signatures certificate checked.1.1,
    checked.1.2⟩, checked.2⟩

theorem valid_branch_persists (c : Config) (before after : State) (a : Action)
    (transition : step c before a = some after) (branch : Branch)
    (valid : validBranch c before branch = true) : validBranch c after branch = true := by
  exact validBranch_of_prefix c before after (step_blocks_prefix c before after a transition)
    (step_signatures_prefix c before after a transition) branch valid

end PirateShip.Proofs
