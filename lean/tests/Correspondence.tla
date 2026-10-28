---- MODULE Correspondence ----
EXTENDS pirateship

\* The shared, attack-free prefix of the Lean majority and twoHop traces.
VARIABLE pc

ReplayInit ==
    /\ Init
    /\ leader[0]
    /\ pc = 0

ReplayNext ==
    IF pc = 12 THEN UNCHANGED <<vars, pc>>
    ELSE
        /\ CASE pc = 0 -> SendEntries(0) /\ Last(branch'[0]).tx = <<2>>
             [] pc = 1 -> ReceiveEntries(1, 0)
             [] pc = 2 -> ReceiveVote(0, 1)
             [] pc = 3 -> ReceiveEntries(2, 0)
             [] pc = 4 -> ReceiveVote(0, 2)
             [] pc = 5 -> SendEntries(0) /\ Last(branch'[0]).tx = <<3>>
             [] pc = 6 -> ReceiveEntries(1, 0)
             [] pc = 7 -> ReceiveVote(0, 1)
             [] pc = 8 -> ReceiveEntries(2, 0)
             [] pc = 9 -> ReceiveVote(0, 2)
             [] pc = 10 -> SendEntries(0) /\ Last(branch'[0]).tx = <<1>>
             [] pc = 11 -> ReceiveEntries(1, 0)
             [] OTHER -> FALSE
        /\ pc' = pc + 1

Observations ==
    /\ pc = 5 => commitIndex[0] = 1 /\ auditIndex[0] = 0
    /\ pc = 10 => auditIndex[0] = 1
    /\ pc = 12 => auditIndex[0] = 1 /\ auditIndex[1] = 1

====
