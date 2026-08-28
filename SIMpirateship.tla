----- MODULE SIMpirateship -----
EXTENDS TLCpirateship, TLC, TLCExt, IOUtils

SIMTimeout(r) ==
    /\ \/ 1 = RandomElement(1..((TLCGet("duration") % 300)+1)) \* Adjust probability of timeouts as a function of the duration of the simulation.
       \* There is no leader in the highest view.
       \/ LET S == { s \in R : view[s] = Max(Range(view))} 
          IN TRUE \notin Range([ s \in S |-> leader[s] ])
    /\ PS!Timeout(r)

-----

SerializeStats ==
    \* Run simulation with -Dtlc2.tool.Simulator.extendedStatistics=true to collect extended statistics.
    Serialize(<<TLCGet("stats")>>, "SIMpirateship.ndjson", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "APPEND">>])

SIMPostCondition ==
    /\ SerializeStats
    /\ MonitorPostcondition

SIMPeriodic ==
    /\ SerializeStats
    /\ PrintMonitors

-----

StatsFastPath ==
    1 + (TLCGet("stats").behavior.id % 3) \* +1 to avoid collision with TLCpirateship!TLCMonitorMagicNumber

StatsHighestUnanimity(l, i, r) ==
    LET fastPath == StatsFastPath IN
    \* No fast path
    IF fastPath = 1 THEN {0}
    \* Non-transitive fast path, i.e, one unanimous QC.
    ELSE IF fastPath = 2 THEN LET idx == SelectLastInSeq(l, LAMBDA e: e.auditQCVotes = R) IN IF idx = 0 THEN {0} ELSE l[idx].auditQC
    \* Transitive fast path, i.e., combined votes from all applicable QCs.
    ELSE HighestUnanimity(l, i, r)

StatsCollect(r, bci) ==
    TLCGetAndSet(StatsFastPath, 
            LAMBDA old, val: [ sum |-> old.sum + val, obs |-> old.obs + 1 ], 
            auditIndex'[r] - Max2(auditIndex[r], bci), 
            [sum |-> 0, obs |-> 0]
    ) \in [sum : Nat, obs : Nat] \* Always evaluate/equal to TRUE.

StatsReceiveVote(p, r) ==
    /\ ReceiveVote(p, r)
    /\ StatsCollect(p, HighestAuditQC(SubSeq(log[p], 1, MaxQuorum(AQ, log[p], prepareQC'[p], 0))))

StatsReceiveEntries(r, p) ==
    /\ ReceiveEntries(r, p)
    /\ StatsCollect(r, HighestQCOverQC(log'[r]))

StatsPostcondition ==
    /\ PrintT(<<"FastPath", TLCGet(2)>>)
    /\ PrintT(<<"FastPath (transitive)", TLCGet(3)>>)

====