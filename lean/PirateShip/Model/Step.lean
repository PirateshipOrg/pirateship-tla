module

public import PirateShip.Model.Branches

@[expose] public section

namespace PirateShip.Model

def initialState (c : Config) : State :=
  { nodes := fun r => { leader := c.leader 0 == some r }
    network := fun _ _ => [] }

def voteEffect (e : Effect) (r : Replica) (l : LocalState)
    (id : BlockId) : Effect :=
  let vote : Vote := ⟨r, l.view, id⟩
  let l := { addVote l vote with voted := vote :: l.voted }
  { e.setLocal r l with signatures := e.signatures ++ [⟨r, .vote l.view id⟩] }

def propose (c : Config) (s : State) (r : Replica) (tx : Nat) : Option Effect := do
  let l := s.nodes r
  if !(c.replicas.contains r && c.leader l.view == some r &&
      l.leader && l.stable && l.entered && c.transactions.contains tx &&
      validBranch c s l.branch) then none else do
    let id := s.blocks.length
    let block : Block :=
      { parent := l.branch.getLast?
        view := l.view
        transactions := [tx]
        auditQC := certificateFor c s l
        commitHint := l.commitIndex }
    let e := { Effect.unchanged s with
      blocks := [block], signatures := [⟨r, .proposal id⟩] }
    let next := { l with branch := l.branch ++ [id] }
    let e := voteEffect e r next id
    let preview := e.apply s
    let e := e.setLocal r (refresh c preview (preview.nodes r))
    return e.broadcast c r (.appendEntries id)

def timeout (c : Config) (s : State) (r : Replica) : Option Effect := do
  if !c.replicas.contains r then none else do
    let l := s.nodes r
    let view := l.view + 1
    let leader <- c.leader view
    let report : ViewChange := ⟨r, view, l.branch⟩
    let e := (Effect.unchanged s).setLocal r
      { l with
        view := view, leader := false, stable := false, entered := false,
        votes := [], changes := [] }
    let e := { e with signatures := [⟨r, .viewChange view l.branch⟩] }
    return e.enqueue leader r (.viewChange report)

def becomeLeader (c : Config) (s : State) (r : Replica)
    (reports : List ViewChange) (chosen : Branch) : Option Effect := do
  let l := s.nodes r
  if !(c.replicas.contains r && c.leader l.view == some r &&
      !l.entered && validEvidence c s l.view reports &&
      reports.all l.changes.contains && chosenBranch c s reports chosen)
  then none else do
    let id := s.blocks.length
    let block : Block :=
      { parent := chosen.getLast?, view := l.view, transactions := [],
        stabilization := true }
    let e := { Effect.unchanged s with
      blocks := [block], signatures := [⟨r, .proposal id⟩] }
    let next := { l with
      branch := chosen ++ [id], leader := true, stable := false, entered := true,
      votes := [], commitIndex := min l.commitIndex (commonLength l.branch chosen) }
    let e := voteEffect e r next id
    let preview := e.apply s
    let e := e.setLocal r (refresh c preview (preview.nodes r))
    return e.broadcast c r (.newView id reports)

def receiveEntries (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (id : BlockId) : Effect :=
  let l := s.nodes r
  match s.blocks[id]?, chain s id with
  | some block, some branch =>
    if c.leader block.view == some sender && l.view == block.view && l.entered &&
        !block.stabilization && branch == l.branch ++ [id] &&
        validBranch c s branch && mayVote s l block.view id then
      let next := { l with
        branch := branch,
        commitIndex := max l.commitIndex block.commitHint }
      let e := voteEffect e r next id
      let preview := e.apply s
      let e := e.setLocal r (refresh c preview (preview.nodes r))
      e.enqueue sender r (.vote ⟨r, block.view, id⟩)
    else e
  | _, _ => e

def receiveVote (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (v : Vote) : Effect :=
  let l := s.nodes r
  if l.leader && l.entered && v.signer == sender && v.view == l.view &&
      l.branch.contains v.block && validVote c s v then
    let newer := l.votes.all (fun old =>
      old.signer != sender || height s old.block <= height s v.block)
    if newer then e.setLocal r (refresh c s (addVote l v)) else e
  else e

def receiveChange (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (report : ViewChange) : Effect :=
  let l := s.nodes r
  if c.leader l.view == some r && !l.entered && report.signer == sender &&
      report.view == l.view && validChange c s report then
    e.setLocal r { l with changes := report :: l.changes }
  else e

def receiveNewView (c : Config) (s : State) (e : Effect) (r sender : Replica)
    (id : BlockId) (reports : List ViewChange) : Effect :=
  let l := s.nodes r
  match s.blocks[id]?, chain s id with
  | some block, some branch =>
    let chosen := branch.dropLast
    if block.stabilization && c.leader block.view == some sender &&
        l.view <= block.view && (l.view < block.view || !l.entered) &&
        validBranch c s branch && validEvidence c s block.view reports &&
        chosenBranch c s reports chosen && mayVote s l block.view id then
      let next := { l with
        view := block.view, branch := branch, leader := false, stable := false,
        entered := true, votes := [], changes := [],
        commitIndex := min l.commitIndex (commonLength l.branch chosen) }
      let e := voteEffect e r next id
      e.enqueue sender r (.vote ⟨r, block.view, id⟩)
    else e
  | _, _ => e

/-- Every delivery consumes exactly the FIFO head, including rejected messages. -/
def deliver (c : Config) (s : State) (r sender : Replica) : Option Effect := do
  if !(c.replicas.contains r && c.replicas.contains sender) then none else do
    match s.network r sender with
    | [] => none
    | message :: rest =>
      let e := (Effect.unchanged s).setChannel r sender rest
      return match message with
      | .appendEntries id => receiveEntries c s e r sender id
      | .vote vote => receiveVote c s e r sender vote
      | .viewChange report => receiveChange c s e r sender report
      | .newView id evidence => receiveNewView c s e r sender id evidence

def dispatch (c : Config) (s : State) : Action -> Option Effect
  | .propose r tx => propose c s r tx
  | .timeout r => timeout c s r
  | .becomeLeader r reports chosen => becomeLeader c s r reports chosen
  | .deliver r sender => deliver c s r sender
  | .byzantineSend sender recipient message =>
    if c.byzantine.contains sender && c.replicas.contains recipient then
      some { (Effect.unchanged s).enqueue recipient sender message with attacked := true }
    else none
  | .byzantinePublish r block =>
    if c.byzantine.contains r && block.parent.all (fun id => id < s.blocks.length) then
      some { Effect.unchanged s with
        blocks := [block],
        signatures := [⟨r, .proposal s.blocks.length⟩], attacked := true }
    else none
  | .byzantineSign r payload =>
    if c.byzantine.contains r then
      some { Effect.unchanged s with signatures := [⟨r, payload⟩], attacked := true }
    else none
  | .byzantineState r node =>
    if c.byzantine.contains r then
      some { (Effect.unchanged s).setLocal r node with attacked := true }
    else none
  | .stutter => some (Effect.unchanged s)

def step (c : Config) (s : State) (a : Action) : Option State :=
  (dispatch c s a).map (Effect.apply s)

end PirateShip.Model
