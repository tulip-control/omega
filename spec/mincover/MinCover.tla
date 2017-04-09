------------------------------- MODULE MinCover --------------------------------
(* Definitions of minimal covering, and properties of minimal covers.

Author:  Ioannis Filippidis

--------------------------------------------------------------------------------
Copyright 2017 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
*)
EXTENDS
    Integers,
    Optimization


CONSTANTS Cost

--------------------------------------------------------------------------------
(* Minimal set covering *)


CostLeq[t \in (DOMAIN Cost) \X (DOMAIN Cost)] ==
    LET
        r == t[1]
        u == t[2]
    IN Cost[r] <= Cost[u]
CardinalityAsCost(Z) == Cost = [cover \in SUBSET Z |-> Cardinality(cover)]

(* `C` and `X` suffice to define a cover, because the notion of covering
involves elements from a cover and a target set to cover. `Y` is irrelevant. *)
IsACover(C, X, IsUnder) == \A x \in X:  \E y \in C:  IsUnder[x, y]
IsACoverFrom(C, X, Y, IsUnder) ==
    /\ C \in SUBSET Y
    /\ IsACover(C, X, IsUnder)
CoversOf(X, Y, IsUnder) == { C \in SUBSET Y:  IsACover(C, X, IsUnder) }

(* The set `Y` is irrelevant to the notion of a cover, but is necessary to
define a notion of minimal element.
*)
IsAMinCover(C, X, Y, IsUnder) ==
    LET
        Covers == CoversOf(X, Y, IsUnder)
    IN
        IsMinimal(C, Covers, CostLeq)

MinCost(X, Y, IsUnder) ==
    LET
        Cov == CoversOf(X, Y, IsUnder)
        min == CHOOSE u \in Minima(Cov, CostLeq):  TRUE
    IN
        Cost[min]

(* `IsACover(C, X, Leq) <=> Refines(X, C, Leq)` *)
Refines(A, B, Leq) == \A u \in A:  \E v \in B:  Leq[u, v]
--------------------------------------------------------------------------------

(* The operator Refines from the module Lattices is equivalent to the
operator IsACover from the module MinCover.
*)
PROPOSITION RefinesMeansCover ==
    ASSUME
        NEW A, NEW B, NEW Leq
    PROVE
        Refines(A, B, Leq)  <=>  IsACover(B, A, Leq)
PROOF
<1>1. ASSUME Refines(A, B, Leq)
      PROVE IsACover(B, A, Leq)
    <2>1. \A u \in A:  \E v \in B:  Leq[u, v]
        BY <1>1 DEF Refines
    <2>2. IsACover(B, A, Leq) =
            \A x \in A:  \E y \in B:  Leq[x, y]
        BY DEF IsACover
    <2> QED
        BY <2>1, <2>2
<1>2. ASSUME IsACover(B, A, Leq)
      PROVE Refines(A, B, Leq)
    <2>1. \A x \in A:  \E y \in B:  Leq[x, y]
        BY <1>2 DEF IsACover
    <2>2. Refines(A, B, Leq) =
            \A u \in A:  \E v \in B:  Leq[u, v]
        BY DEF Refines
    <2> QED
        BY <2>1, <2>2
<1> QED
    BY <1>1, <1>2


(* Transitivity of the operator Refines. *)
LEMMA RefinesIsTransitive ==
    ASSUME
        NEW A, NEW B, NEW C, NEW Leq,
        LET
            S == Support(Leq)
        IN
            /\ A \subseteq S
            /\ B \subseteq S
            /\ C \subseteq S
            /\ IsTransitive(Leq)
            /\ Refines(A, B, Leq)
            /\ Refines(B, C, Leq)
    PROVE
        Refines(A, C, Leq)
PROOF
<1> DEFINE
    S == Support(Leq)
<1>1. SUFFICES
        ASSUME NEW p \in A
        PROVE \E r \in C:  Leq[p, r]
    BY <1>1 DEF Refines
<1>2. PICK q \in B:  Leq[p, q]
    <2>1. Refines(A, B, Leq)
        OBVIOUS
    <2> QED
        BY <1>1, <2>1 DEF Refines
<1>3. PICK r \in C:  Leq[q, r]
    <2>1. Refines(B, C, Leq)
        OBVIOUS
    <2> QED
        BY <1>2, <2>1 DEF Refines
<1>4. /\ p \in S
      /\ q \in S
      /\ r \in S
    <2>1. /\ A \subseteq S
          /\ B \subseteq S
          /\ C \subseteq S
        BY DEF S
    <2> QED
        BY <1>1, <1>2, <1>3, <2>1
<1>5. Leq[p, q] /\ Leq[q, r]
    BY <1>2, <1>3
<1> QED
    <2>1. IsTransitive(Leq)
        OBVIOUS
    <2> QED
        BY <1>4, <1>5, <2>1 DEF IsTransitive


(* Transitivity of the operator IsACover. *)
COROLLARY CoveringIsTransitive ==
    ASSUME
        NEW A, NEW B, NEW C, NEW Leq,
        LET
            Z == Support(Leq)
        IN
            /\ A \subseteq Z
            /\ B \subseteq Z
            /\ C \subseteq Z
            /\ IsTransitive(Leq)
            /\ IsACover(A, B, Leq)
            /\ IsACover(B, C, Leq)
    PROVE
        IsACover(A, C, Leq)
PROOF
BY RefinesIsTransitive, RefinesMeansCover


(* If S refines T, then any subset of S refines T. *)
PROPOSITION SubsetRefinesToo ==
    ASSUME
        NEW S, NEW R, NEW T, NEW Leq,
        /\ Refines(S, T, Leq)
        /\ R \in SUBSET S
    PROVE
        Refines(R, T, Leq)
PROOF
<1>1. \A u \in S:  \E v \in T:  Leq[u, v]
    <2>1. Refines(S, T, Leq)
        OBVIOUS
    <2> QED
        BY <2>1 DEF Refines
<1>2. \A u \in R:  u \in S
    OBVIOUS
<1>3. \A u \in R:  \E v \in T:  Leq[u, v]
    BY <1>1, <1>2
<1> QED
    BY <1>3 DEF Refines

--------------------------------------------------------------------------------

(* Auxiliary fact to aid TLAPS. *)
PROPOSITION CostLeqHelper ==
        (DOMAIN CostLeq) = ((DOMAIN Cost) \X (DOMAIN Cost))
PROOF
BY DEF CostLeq


(* Substitution of cardinality in the definition of CostLeq. *)
PROPOSITION CostLeqToCard ==
    ASSUME
        NEW S,
        NEW A \in SUBSET S,
        NEW B \in SUBSET S,
        CardinalityAsCost(S)
    PROVE
        CostLeq[ << A, B >> ] = (Cardinality(A) <= Cardinality(B))
PROOF
<1>1. /\ A \in SUBSET S
      /\ B \in SUBSET S
    OBVIOUS
<1>2. Cost = [c \in SUBSET S |-> Cardinality(c)]
    <2>1. CardinalityAsCost(S)
        OBVIOUS
    <2> QED
        BY <2>1 DEF CardinalityAsCost
<1>3. << A, B >> \in DOMAIN CostLeq
    BY <1>1, <1>2 DEF CostLeq
<1>4. CostLeq[ << A, B >> ] = (Cost[A] <= Cost[B])
    BY <1>3 DEF CostLeq
<1>5. /\ Cost[A] = Cardinality(A)
      /\ Cost[B] = Cardinality(B)
    BY <1>2, <1>1
<1> QED
    BY <1>4, <1>5


PROPOSITION MinCoverProperties ==
    ASSUME
        NEW Leq, NEW C, NEW X, NEW Y,
        IsAMinCover(C, X, Y, Leq)
    PROVE
        /\ C \in SUBSET Y
        /\ IsACover(C, X, Leq)
        /\ \A r \in SUBSET Y:  (* Any other cover from Y *)
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ CostLeq[ << r, C >> ]
            \/ CostLeq[ << C, r >> ]  (* costs no less. *)
PROOF
<1> DEFINE Covers == CoversOf(X, Y, Leq)
<1>1. IsMinimal(C, Covers, CostLeq)
    BY DEF IsAMinCover
<1>2. C \in Covers
    BY <1>1 DEF IsMinimal
<1>3. /\ C \in SUBSET Y
      /\ IsACover(C, X, Leq)
    BY <1>2 DEF CoversOf
<1> HIDE DEF CostLeq
<1>4. \A r \in SUBSET Y:
        \/ ~ /\ IsACover(r, X, Leq)
             /\ CostLeq[ << r, C >> ]
        \/ CostLeq[ << C, r >> ]
    BY <1>1 DEF IsMinimal, CoversOf
<1> QED
    BY <1>3, <1>4


(* The previous proposition when we have Cardinality as Cost. *)
PROPOSITION MinCoverPropertiesCard ==
    ASSUME
        NEW Leq, NEW Z, NEW C, NEW X,
        NEW Y \in SUBSET Z,
        /\ IsAMinCover(C, X, Y, Leq)
        /\ CardinalityAsCost(Z)
    PROVE
        /\ C \in SUBSET Y
        /\ IsACover(C, X, Leq)
        /\ \A r \in SUBSET Y:
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ (Cardinality(r) <= Cardinality(C))
            \/ (Cardinality(C) <= Cardinality(r))
PROOF
<1>1. /\ C \in SUBSET Y
      /\ IsACover(C, X, Leq)
      /\ \A r \in SUBSET Y:
        \/ ~ /\ IsACover(r, X, Leq)
             /\ CostLeq[ << r, C >> ]
        \/ CostLeq[ << C, r >> ]
    <2>1. IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2> QED
        BY <2>1, MinCoverProperties
<1>2. Y \subseteq Z
    OBVIOUS
<1>3. C \subseteq Z
    BY <1>1, <1>2
<1>4. ASSUME NEW r \in SUBSET Y
      PROVE
        /\ CostLeq[ << r, C >> ] = (Cardinality(r) <= Cardinality(C))
        /\ CostLeq[ << C, r >> ] = (Cardinality(C) <= Cardinality(r))
    <2>1. r \in SUBSET Z
        BY <1>4, <1>2
    <2> QED
        <3>1. CardinalityAsCost(Z)
            OBVIOUS
        <3> QED
            BY <1>3, <2>1, CostLeqToCard
<1> QED
    BY <1>1, <1>4


COROLLARY MinCoverHasMinCard ==
    ASSUME
        NEW Leq, NEW Z, NEW C, NEW X,
        NEW Y \in SUBSET Z,
        NEW r \in SUBSET Y,
        /\ CardinalityAsCost(Z)
        /\ Cardinality(C) \in Nat
        /\ Cardinality(r) \in Nat
        /\ IsAMinCover(C, X, Y, Leq)
        /\ IsACover(r, X, Leq)
    PROVE
        Cardinality(C) <= Cardinality(r)
PROOF
<1>1. \/ Cardinality(C) <= Cardinality(r)
      \/ Cardinality(r) <= Cardinality(C)
    OBVIOUS
<1> QED
    BY <1>1, MinCoverPropertiesCard


(* Any two minimal covers C, H have the same cardinality,
because X, Y are subsets of a finite complete lattice.
*)
THEOREM AllMinCoversSameCard ==
    ASSUME
        NEW C, NEW H, NEW Leq, NEW X, NEW Y, NEW Z,
        /\ IsAMinCover(C, X, Y, Leq)
        /\ IsAMinCover(H, X, Y, Leq)
        /\ CardinalityAsCost(Z)
        /\ IsFiniteSet(Y)
        /\ Y \subseteq Z
    PROVE
        Cardinality(C) = Cardinality(H)
PROOF
<1>1. /\ H \in SUBSET Y
      /\ IsACover(H, X, Leq)
      /\ \A r \in SUBSET Y:
        \/ ~ /\ IsACover(r, X, Leq)
             /\ Cardinality(r) <= Cardinality(H)
        \/ Cardinality(H) <= Cardinality(r)
    <2>1. IsAMinCover(H, X, Y, Leq)
        OBVIOUS
    <2> QED
        BY <2>1, MinCoverPropertiesCard
<1>2. /\ C \in SUBSET Y
      /\ IsACover(C, X, Leq)
      /\ \A r \in SUBSET Y:
        \/ ~ /\ IsACover(r, X, Leq)
             /\ Cardinality(r) <= Cardinality(C)
        \/ Cardinality(C) <= Cardinality(r)
    <2>1. IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2> QED
        BY <2>1, MinCoverPropertiesCard
<1>3. (Cardinality(C) <= Cardinality(H))
      => (Cardinality(H) <= Cardinality(C))
    BY <1>1, <1>2  (* r <- C in <1>1 *)
<1>4. (Cardinality(H) <= Cardinality(C))
      => (Cardinality(C) <= Cardinality(H))
    BY <1>1, <1>2  (* r <- H in <1>2 *)
<1>5. /\ Cardinality(C) \in Nat
      /\ Cardinality(H) \in Nat
    <2>1. IsFiniteSet(C) /\ IsFiniteSet(H)
        <3>1. /\ C \subseteq Y
              /\ H \subseteq Y
            <4>1. /\ IsAMinCover(C, X, Y, Leq)
                  /\ IsAMinCover(H, X, Y, Leq)
                OBVIOUS
            <4> QED
                BY <4>1, MinCoverProperties
        <3>2. IsFiniteSet(Y)
            OBVIOUS
        <3> QED
            BY <3>1, <3>2, FS_Subset
    <2> QED
        BY <2>1, FS_CardinalityType
<1>6. CASE Cardinality(C) <= Cardinality(H)
    <2>1. Cardinality(H) <= Cardinality(C)
        BY <1>6, <1>3
    <2> QED
        BY <1>6, <2>1, <1>5
<1>7. ASSUME ~ (Cardinality(C) <= Cardinality(H))
      PROVE FALSE
    <2>1. Cardinality(C) > Cardinality(H)
        BY <1>7, <1>5
    <2>2. Cardinality(C) >= Cardinality(H)
        BY <2>1, <1>5
    <2>3. Cardinality(C) <= Cardinality(H)
        BY <2>2, <1>4
    <2> QED
        BY <1>7, <2>3
<1> QED
    BY <1>6, <1>7


THEOREM MinCoverEquivCoverCard ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW Z,
        NEW C, NEW H,
        /\ IsAMinCover(C, X, Y, Leq)
        /\ IsFiniteSet(Y)
        /\ Y \subseteq Z
        /\ CardinalityAsCost(Z)
    PROVE
        IsAMinCover(H, X, Y, Leq)
            <=> /\ H \in SUBSET Y
                /\ IsACover(H, X, Leq)
                /\ Cardinality(H) <= Cardinality(C)
PROOF
<1> DEFINE
    Props == /\ H \in SUBSET Y
             /\ IsACover(H, X, Leq)
             /\ Cardinality(H) <= Cardinality(C)
    Covers == CoversOf(X, Y, Leq)
<1> USE DEF CoversOf
<1>1. ASSUME IsAMinCover(H, X, Y, Leq)
      PROVE Props
    <2>1. /\ H \in SUBSET Y
          /\ IsACover(H, X, Leq)
        BY <1>1, MinCoverProperties
    <2>2. Cardinality(H) = Cardinality(C)
        BY <1>1, AllMinCoversSameCard
    <2>3. /\ Cardinality(H) \in Nat
          /\ Cardinality(C) \in Nat
        BY <1>1, MinCoverProperties, FS_Subset,
            FS_CardinalityType
    <2> QED
        BY <2>1, <2>2, <2>3
<1>2. ASSUME Props
      PROVE IsAMinCover(H, X, Y, Leq)
    <2>1. SUFFICES IsMinimal(H, Covers, CostLeq)
        BY <1>2 DEF IsAMinCover
    <2>2. SUFFICES
            ASSUME NEW u \in Covers, CostLeq[ << u, H >> ]
            PROVE CostLeq[ << H, u >> ]
        BY <1>2, <2>2 DEF IsMinimal
    <2>7. /\ H \in SUBSET Z
          /\ u \in SUBSET Z
        BY <1>2, <2>2, Y \subseteq Z
    <2>6. SUFFICES Cardinality(H) <= Cardinality(u)
        BY <2>7, CostLeqToCard
    <2>5. /\ Cardinality(H) \in Nat
          /\ Cardinality(C) \in Nat
          /\ Cardinality(u) \in Nat
        <3>1. /\ H \in SUBSET Y
              /\ C \in SUBSET Y
              /\ u \in SUBSET Y
            BY <1>2, MinCoverProperties, <2>2
        <3> QED
            BY <3>1, FS_Subset, FS_CardinalityType
    <2>4. Cardinality(H) <= Cardinality(C)
        BY <1>2
    <2>3. Cardinality(C) <= Cardinality(u)
        <3>1. Cardinality(u) <= Cardinality(H)
            BY <2>2, <2>5, <2>7, CostLeqToCard
        <3>2. Cardinality(u) <= Cardinality(C)
            BY <2>4, <3>1, <2>5
        <3> QED
            BY <3>2, <2>2, MinCoverPropertiesCard, <2>5
    <2> QED
        BY <2>3, <2>4, <2>5
<1> QED
    BY <1>1, <1>2


PROPOSITION CheaperCoverExists ==
    ASSUME
        NEW Leq, NEW X, NEW Y,
        NEW C \in CoversOf(X, Y, Leq),  (* so some cover exists *)
        ~ IsAMinCover(C, X, Y, Leq)
    PROVE
        \E OtherCover \in SUBSET Y:
            /\ OtherCover # C
            /\ IsACover(OtherCover, X, Leq)
            /\ CostLeq[ << OtherCover, C >> ]
            /\ ~ CostLeq[ << C, OtherCover >> ]
PROOF
BY SmallerExists DEF IsAMinCover, CoversOf, IsMinimal


LEMMA SubtractFromBoth ==
    ASSUME
        NEW Leq, NEW X, NEW E, NEW C,
        LET
            Z == Support(Leq)
        IN
            /\ IsAntiSymmetric(Leq)
            /\ E \subseteq X
            /\ X \subseteq Z
            /\ X = Maxima(X, Leq)
            /\ IsACover(C, X, Leq)
    PROVE
        LET
            Xe == X \ E
            Ce == C \ E
        IN
            IsACover(Ce, Xe, Leq)
PROOF
<1> DEFINE
    Xe == X \ E
    Ce == C \ E
<1>1. SUFFICES ASSUME NEW u \in Xe
               PROVE \E v \in Ce:  Leq[u, v]
    BY DEF IsACover
<1>2. PICK v \in C:  Leq[u, v]
    BY DEF IsACover
<1>3. SUFFICES ASSUME v \in E
               PROVE FALSE
    BY <1>2, <1>3 DEF Ce
<1>4. u # v
    BY <1>1, <1>3 DEF Xe
<1> QED
    <2>1. IsAntiChain(X, Leq)
        BY MaximaIsAntiChain
    <2>2. /\ u \in X
          /\ v \in X
        BY <1>1, <1>3
    <2> QED
        BY <2>1, <1>2, <1>4, <2>2 DEF IsAntiChain


LEMMA AddToBoth ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW E, NEW C,
        /\ C \subseteq Y
        /\ E \subseteq Support(Leq)
        /\ IsReflexive(Leq)
        /\ IsACoverFrom(C, X, Y, Leq)
    PROVE
        LET
            XE == X \cup E
            YE == Y \cup E
            CE == C \cup E
        IN
            IsACoverFrom(CE, XE, YE, Leq)
PROOF
<1> DEFINE
    XE == X \cup E
    YE == Y \cup E
    CE == C \cup E
<1>1. IsACover(C, X, Leq)
    BY DEF IsACoverFrom
<1>2. IsACover(CE, XE, Leq)
    <3>1. \A x \in X:  \E y \in C:  Leq[x, y]
        BY <1>1 DEF IsACover
    <3>2. \A x \in XE:  \E y \in CE:  Leq[x, y]
        BY <3>1 DEF IsReflexive
    <3> QED
        BY <3>2 DEF IsACover
<1>3. CE \in SUBSET YE
    OBVIOUS
<1> QED
    BY <1>2, <1>3 DEF IsACoverFrom

================================================================================
(* Proofs checked with TLAPS version 1.4.3 *)
