module

public import PirateShip.Model.Types

@[expose] public section

namespace PirateShip.Model

/-- Fuel makes lookup total even for malformed references in adversarial inputs. -/
def chainAux (blocks : List Block) : Nat -> BlockId -> Option Branch
  | 0, _ => none
  | fuel + 1, id => do
      let block <- blocks[id]?
      match block.parent with
      | none => pure [id]
      | some parent => return (← chainAux blocks fuel parent) ++ [id]

def chain (s : State) (id : BlockId) : Option Branch :=
  chainAux s.blocks (s.blocks.length + 1) id

def height (s : State) (id : BlockId) : Nat :=
  ((chain s id).map List.length).getD 0

def issued (s : State) (r : Replica) (p : Payload) : Bool :=
  s.signatures.contains ⟨r, p⟩

def supports (s : State) (view : Nat) (target : BlockId) (vote : Vote) : Bool :=
  vote.view == view &&
  (s.blocks[target]?).any (fun b => b.view == view) &&
  (s.blocks[vote.block]?).any (fun b => b.view == view) &&
  (chain s vote.block).any (fun b => b.contains target)

def validVote (c : Config) (s : State) (v : Vote) : Bool :=
  c.replicas.contains v.signer &&
  issued s v.signer (.vote v.view v.block) &&
  (s.blocks[v.block]?).any (fun b => b.view == v.view)

def validCertificate (c : Config) (s : State) (qc : Certificate) : Bool :=
  qc.votes.length >= c.auditQuorum &&
  (qc.votes.map Vote.signer).eraseDups.length == qc.votes.length &&
  qc.votes.all (fun v => validVote c s v && supports s qc.view qc.block v)

def signedBlock (c : Config) (s : State) (id : BlockId) : Bool :=
  (s.blocks[id]?).any fun b =>
    (c.leader b.view).any (fun r => issued s r (.proposal id))

def validBranch (c : Config) (s : State) (branch : Branch) : Bool :=
  branch.zipIdx.all fun (id, index) =>
    (s.blocks[id]?).any fun b =>
      signedBlock c s id &&
      b.parent == (branch.take index).getLast? &&
      (b.parent.all fun parent =>
        (s.blocks[parent]?).any (fun p => p.view <= b.view)) &&
      b.commitHint <= index + 1 &&
      (if b.stabilization then b.transactions.isEmpty && b.view > 0
       else !b.transactions.isEmpty && b.transactions.all c.transactions.contains) &&
      (b.parent.all fun parent =>
        (s.blocks[parent]?).all (fun p => p.view == b.view || b.stabilization)) &&
      (b.auditQC.all fun qc =>
        validCertificate c s qc && qc.view == b.view &&
        (branch.take index).contains qc.block)

def validChange (c : Config) (s : State) (v : ViewChange) : Bool :=
  c.replicas.contains v.signer && v.view > 0 &&
  issued s v.signer (.viewChange v.view v.branch) &&
  validBranch c s v.branch &&
  v.branch.all (fun id => (s.blocks[id]?).any (fun b => b.view < v.view))

def validEvidence (c : Config) (s : State) (view : Nat)
    (evidence : List ViewChange) : Bool :=
  evidence.length == c.auditQuorum &&
  (evidence.map ViewChange.signer).eraseDups.length == evidence.length &&
  evidence.all (fun v => v.view == view && validChange c s v)

def highestQCView (s : State) (branch : Branch) : Nat :=
  branch.foldl (fun acc id =>
    match (s.blocks[id]?).bind Block.auditQC with
    | none => acc
    | some qc => max acc (qc.view + 1)) 0

def lastView (s : State) (branch : Branch) : Nat :=
  ((branch.getLast?.bind fun id => s.blocks[id]?).map Block.view).getD 0

def supportingReports (reports : List ViewChange) (id : BlockId) : Nat :=
  (reports.filter fun r => r.branch.contains id).length

/-- Rule 2 considers supported ancestors, not just identical branch tips. -/
def possibleFastBlocks (c : Config) (reports : List ViewChange) : List BlockId :=
  if c.fastEnabled then
    (reports.flatMap ViewChange.branch).eraseDups.filter
      (fun id => supportingReports reports id >= c.fastSupport)
  else []

def chosenBranch (c : Config) (s : State) (reports : List ViewChange)
    (chosen : Branch) : Bool :=
  let high := reports.foldl (fun v r => max v (highestQCView s r.branch)) 0
  let first := reports.filter (fun r => highestQCView s r.branch == high)
  let possible := possibleFastBlocks c first
  let second := first.filter (fun r => possible.all r.branch.contains)
  let highView := second.foldl (fun v r => max v (lastView s r.branch)) 0
  let third := second.filter (fun r => lastView s r.branch == highView)
  let highLength := third.foldl (fun n r => max n r.branch.length) 0
  third.any (fun r => r.branch == chosen && r.branch.length == highLength)

def commonLength : Branch -> Branch -> Nat
  | a :: as, b :: bs => if a = b then 1 + commonLength as bs else 0
  | _, _ => 0

def votesFor (s : State) (l : LocalState) (id : BlockId) : List Vote :=
  l.votes.filter (supports s l.view id)

def certificateFor (c : Config) (s : State) (l : LocalState) : Option Certificate :=
  l.branch.reverse.findSome? fun id =>
    let qc : Certificate := ⟨l.view, id, votesFor s l id⟩
    if validCertificate c s qc then some qc else none

def commitHeight (c : Config) (s : State) (l : LocalState) : Nat :=
  l.branch.foldl (fun n id =>
    if (votesFor s l id).length >= c.commitQuorum then max n (height s id) else n) 0

def knownCertificates (s : State) (l : LocalState) : List Certificate :=
  l.branch.filterMap fun id => (s.blocks[id]?).bind Block.auditQC

def slowAuditHeight (s : State) (branch : Branch) (qcs : List Certificate) : Nat :=
  qcs.foldl (fun acc outer =>
    branch.foldl (fun n carrier =>
      match (s.blocks[carrier]?).bind Block.auditQC with
      | none => n
      | some inner =>
        if inner.view == outer.view &&
            (chain s outer.block).any (fun path => path.contains carrier)
        then max n (height s inner.block) else n) acc) 0

/-- Signatures on different descendants can jointly supply unanimous support. -/
def fastAuditHeight (c : Config) (s : State) (l : LocalState)
    (qcs : List Certificate) : Nat :=
  if !c.fastEnabled || !l.stable then 0
  else
    let votes := l.votes ++ qcs.flatMap Certificate.votes
    l.branch.foldl (fun n id =>
      if c.replicas.all (fun r =>
        votes.any (fun v => v.signer == r && validVote c s v &&
          supports s l.view id v))
      then max n (height s id) else n) 0

def refresh (c : Config) (s : State) (l : LocalState) : LocalState :=
  let ownQC := if l.leader then (certificateFor c s l).toList else []
  let qcs := knownCertificates s l ++ ownQC
  let stabilized := l.view == 0 || qcs.any (fun qc =>
    qc.view == l.view && l.branch.any (fun id =>
      (s.blocks[id]?).any (fun b => b.stabilization && b.view == l.view) &&
      (chain s qc.block).any (fun path => path.contains id)))
  let l := { l with stable := l.stable || stabilized }
  let audited := max l.auditIndex
    (max (slowAuditHeight s l.branch qcs) (fastAuditHeight c s l qcs))
  { l with
    commitIndex := if l.leader && l.stable then
      max l.commitIndex (commitHeight c s l) else l.commitIndex
    auditIndex := audited }

def addVote (l : LocalState) (v : Vote) : LocalState :=
  { l with votes := v :: l.votes.filter (fun old => old.signer != v.signer) }

def mayVote (s : State) (l : LocalState) (view : Nat) (id : BlockId) : Bool :=
  l.voted.all (fun v =>
    v.view != view || height s v.block != height s id || v.block == id)

end PirateShip.Model
