----- MODULE TLCpirateship -----
EXTENDS pirateship, TLC

PS == INSTANCE pirateship

TLCInit ==
    \/ PS!Init
    \* Cluster is in a steady state.
    \/ /\ view = [r \in R |-> 0]
       /\ byzActions = 0
       /\ network = [r \in R |-> [s \in R |-> <<>>]]
       /\ auditIndex = [r \in R |-> 2]
       /\ \E p \in R:
             /\ leader = [ r \in R |-> r = p ]
             /\ viewStable = leader \* Identical to leader at startup.
             /\ log = [r \in R |-> 
                    <<[view |-> 0, tx |-> <<1>>, auditQC |-> {},  auditQCVotes |-> {},  commitQC |-> {}],
                      [view |-> 0, tx |-> <<1>>, auditQC |-> {},  auditQCVotes |-> {},  commitQC |-> {}],
                      [view |-> 0, tx |-> <<1>>, auditQC |-> {1}, auditQCVotes |-> R,  commitQC |-> {1}],
                      [view |-> 0, tx |-> <<1>>, auditQC |-> {2}, auditQCVotes |-> R,  commitQC |-> {2}]>>]
             /\ prepareQC = [r \in R |-> [s \in R |-> IF r = p THEN Len(log[r]) ELSE 0]]
             /\ commitIndex = [r \in R |-> Len(log[r])]

-----

\* Add a few monitors/canaries to check if interesting states are reachable.

Monitors == INSTANCE TLCMonitor WITH TLCMonitorMagicNumber <- 0

CommitIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: commitIndex[r] = 1, "CommitIndex@1")

CommitIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: commitIndex[r] = 2, "CommitIndex@2")

CommitIndex1AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: commitIndex[r] = 1, "CommitIndex1AtLevel", TLCGet("level"))

CommitIndex2AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: commitIndex[r] = 2, "CommitIndex2AtLevel", TLCGet("level"))

AuditIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: auditIndex[r] = 1, "AuditIndex@1")

AuditIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: auditIndex[r] = 2, "AuditIndex@2")

AuditIndex1AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: auditIndex[r] = 1, "AuditIndex1AtLevel", TLCGet("level"))

AuditIndex2AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: auditIndex[r] = 2, "AuditIndex2AtLevel", TLCGet("level"))

MonitorPostcondition ==
    Monitors!TLCCheckMonitors

PrintMonitors ==
    Monitors!TLCPrintMonitors

-----

DebugCommitIndex ==
    \* For all replicas, commitIndex is always less than two.
    \E i \in Range(commitIndex): i < 2

DebugAuditIndex ==
    \* For all replicas, auditIndex is always less than two.
    \E i \in Range(auditIndex): i < 2

=====