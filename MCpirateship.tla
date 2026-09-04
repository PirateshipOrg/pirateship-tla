---- MODULE MCpirateship ----
EXTENDS TLCpirateship, TLC

CONSTANT MCViews

MCTimeout(r) ==
    \* artifact of the spec, check that the view limit is not exceeded
    /\ view[r] + 1 \in MCViews
    /\ PS!Timeout(r)

Symmetry ==
    Permutations(R)

MaxBranchLength ==
    \A r \in R: Len(branch[r]) <= 4

=====