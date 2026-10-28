module

public import Std

@[expose] public section

namespace PirateShip.Model

abbrev Replica := Nat
abbrev BlockId := Nat
abbrev Branch := List BlockId

structure Config where
  replicas : List Replica
  unavailable : Nat
  fsafe : Nat
  byzantine : List Replica
  transactions : List Nat
  deriving DecidableEq, Repr

def Config.Valid (c : Config) : Prop :=
  c.replicas.Nodup /\ c.replicas ≠ [] /\
  c.byzantine.Nodup /\ (forall r, r ∈ c.byzantine -> r ∈ c.replicas) /\
  c.byzantine.length <= c.fsafe /\
  2 * c.unavailable + c.fsafe + 1 <= c.replicas.length /\
  c.transactions ≠ []

def Config.commitQuorum (c : Config) : Nat := c.replicas.length / 2 + 1
def Config.auditQuorum (c : Config) : Nat := c.replicas.length - c.unavailable
def Config.fastSupport (c : Config) : Nat :=
  c.replicas.length - c.unavailable - c.fsafe
def Config.fastEnabled (c : Config) : Bool := c.fsafe < c.fastSupport

def Config.leader (c : Config) (view : Nat) : Option Replica :=
  c.replicas[view % c.replicas.length]?

def Config.honest (c : Config) (r : Replica) : Prop :=
  r ∈ c.replicas /\ r ∉ c.byzantine

structure Vote where
  signer : Replica
  view : Nat
  block : BlockId
  deriving DecidableEq, BEq, Repr

structure Certificate where
  view : Nat
  block : BlockId
  votes : List Vote
  deriving DecidableEq, BEq, Repr

structure Block where
  parent : Option BlockId
  view : Nat
  transactions : List Nat
  stabilization : Bool := false
  auditQC : Option Certificate := none
  commitHint : Nat := 0
  deriving DecidableEq, BEq, Repr

structure ViewChange where
  signer : Replica
  view : Nat
  branch : Branch
  deriving DecidableEq, BEq, Repr

inductive Payload where
  | proposal (block : BlockId)
  | vote (view : Nat) (block : BlockId)
  | viewChange (view : Nat) (branch : Branch)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

structure Signature where
  signer : Replica
  payload : Payload
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

inductive Message where
  | appendEntries (block : BlockId)
  | vote (vote : Vote)
  | viewChange (change : ViewChange)
  | newView (block : BlockId) (evidence : List ViewChange)
  deriving DecidableEq, BEq, Repr

structure LocalState where
  view : Nat := 0
  branch : Branch := []
  leader : Bool := false
  stable : Bool := true
  entered : Bool := true
  votes : List Vote := []
  voted : List Vote := []
  changes : List ViewChange := []
  commitIndex : Nat := 0
  auditIndex : Nat := 0
  deriving DecidableEq, BEq, Repr

structure State where
  nodes : Replica -> LocalState
  network : Replica -> Replica -> List Message
  blocks : List Block := []
  signatures : List Signature := []
  byzActions : Nat := 0

/-- Handlers can extend, but cannot rewrite, published blocks and issued signatures. -/
structure Effect where
  nodes : Replica -> LocalState
  network : Replica -> Replica -> List Message
  blocks : List Block := []
  signatures : List Signature := []
  attacked : Bool := false

def Effect.unchanged (s : State) : Effect :=
  { nodes := s.nodes, network := s.network }

def Effect.apply (s : State) (e : Effect) : State :=
  { nodes := e.nodes
    network := e.network
    blocks := s.blocks ++ e.blocks
    signatures := s.signatures ++ e.signatures
    byzActions := s.byzActions + if e.attacked then 1 else 0 }

def Effect.setLocal (e : Effect) (r : Replica) (l : LocalState) : Effect :=
  { e with nodes := fun n => if n = r then l else e.nodes n }

def Effect.setChannel (e : Effect) (recipient sender : Replica)
    (messages : List Message) : Effect :=
  { e with network := fun r p =>
      if r = recipient && p = sender then messages else e.network r p }

def Effect.enqueue (e : Effect) (recipient sender : Replica) (m : Message) : Effect :=
  e.setChannel recipient sender (e.network recipient sender ++ [m])

def Effect.broadcast (e : Effect) (c : Config) (sender : Replica) (m : Message) : Effect :=
  c.replicas.foldl (fun acc r => if r = sender then acc else acc.enqueue r sender m) e

inductive Action where
  | propose (leader : Replica) (transaction : Nat)
  | timeout (replica : Replica)
  | becomeLeader (replica : Replica) (evidence : List ViewChange) (chosen : Branch)
  | deliver (recipient sender : Replica)
  | byzantineSend (sender recipient : Replica) (message : Message)
  | byzantinePublish (replica : Replica) (block : Block)
  | byzantineSign (replica : Replica) (payload : Payload)
  | byzantineState (replica : Replica) (state : LocalState)
  | stutter
  deriving DecidableEq, Repr

end PirateShip.Model
