module

public import PirateShip.Model
public import CCF.Execution

@[expose] public section

namespace PirateShip.Properties

open Model

def committed (s : State) (r : Replica) : Branch :=
  (s.nodes r).branch.take (s.nodes r).commitIndex

def audited (s : State) (r : Replica) : Branch :=
  (s.nodes r).branch.take (s.nodes r).auditIndex

/-- The TLA+ comparison retains its length check and treats empty batches as wildcards. -/
def IsPrefixWithoutEmpty (s : State) (short branch : Branch) : Prop :=
  short.length <= branch.length /\
  forall (i : Nat) (id : BlockId), short[i]? = some id ->
    exists other, branch[i]? = some other /\
      (id = other \/ exists b : Block, s.blocks[id]? = some b /\ b.transactions = [])

def IndexBounds (c : Config) (s : State) : Prop :=
  forall r, c.honest r ->
    (s.nodes r).commitIndex <= (s.nodes r).branch.length /\
    (s.nodes r).auditIndex <= (s.nodes r).branch.length

/-- Kept separately: unsigned malicious commit hints need not cover an audit. -/
def AuditBelowCommit (c : Config) (s : State) : Prop :=
  forall r, c.honest r -> (s.nodes r).auditIndex <= (s.nodes r).commitIndex

def CommittedAgreement (c : Config) (s : State) : Prop :=
  s.byzActions = 0 ->
  forall r t, r ∈ c.replicas -> t ∈ c.replicas ->
    IsPrefixWithoutEmpty s (committed s r) (committed s t) \/
    IsPrefixWithoutEmpty s (committed s t) (committed s r)

def AuditedAgreement (c : Config) (s : State) : Prop :=
  forall r t, c.honest r -> c.honest t ->
    (audited s r).IsPrefix (audited s t) \/ (audited s t).IsPrefix (audited s r)

def OneLeaderPerView (c : Config) (s : State) : Prop :=
  forall r t, c.honest r -> c.honest t ->
    (s.nodes r).leader = true -> (s.nodes t).leader = true ->
    (s.nodes r).view = (s.nodes t).view -> r = t

def WellFormedBranches (c : Config) (s : State) : Prop :=
  forall r, c.honest r -> validBranch c s (s.nodes r).branch = true

def ViewMonotonic (c : Config) (s : State) : Prop :=
  forall r, c.honest r ->
    forall (i : Nat) (left right : BlockId) (a b : Block),
      (s.nodes r).branch[i]? = some left ->
      (s.nodes r).branch[i + 1]? = some right ->
      s.blocks[left]? = some a -> s.blocks[right]? = some b -> a.view <= b.view

def ViewStabilization (c : Config) (s : State) : Prop :=
  forall r, c.honest r ->
    (forall (id : BlockId) (b : Block), id ∈ (s.nodes r).branch -> s.blocks[id]? = some b ->
      b.transactions = [] -> b.view ≠ 0) /\
    (forall (i : Nat) (left right : BlockId) (a b : Block),
      (s.nodes r).branch[i]? = some left ->
      (s.nodes r).branch[i + 1]? = some right ->
      s.blocks[left]? = some a -> s.blocks[right]? = some b ->
      a.view < b.view -> b.transactions = [])

/-- Commitment guarantees stop at compromise, including arbitrary faulty state erasure. -/
def CommittedAppendOnly (c : Config) (before after : State) : Prop :=
  after.byzActions = 0 ->
  forall r, r ∈ c.replicas ->
    IsPrefixWithoutEmpty after (committed before r) (committed after r)

def AuditedAppendOnly (c : Config) (before after : State) : Prop :=
  forall r, c.honest r -> (audited before r).IsPrefix (audited after r)

def MonotonicAuditIndex (c : Config) (before after : State) : Prop :=
  forall r, c.honest r -> (before.nodes r).auditIndex <= (after.nodes r).auditIndex

/-- A proof-only classification; a new-view delivery may still be rejected. -/
def MayInstallBranch (s : State) (a : Action) (r : Replica) : Prop :=
  match a with
  | .becomeLeader actor _ _ => r = actor
  | .deliver recipient sender =>
    r = recipient /\ match s.network recipient sender with
      | .newView _ _ :: _ => True
      | _ => False
  | _ => False

abbrev Trace := CCF.Execution.Trace State

def Always (property : State -> Prop) (trace : Trace) : Prop :=
  forall s, s ∈ trace -> property s

def AlwaysStep (property : State -> State -> Prop) (trace : Trace) : Prop :=
  forall i before after, trace.get? i = some before ->
    trace.get? (i + 1) = some after -> property before after

end PirateShip.Properties
