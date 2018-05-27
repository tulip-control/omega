-------------------- MODULE StrongReduction ------------------------------------
(* An algorithm that takes as input the set of minimal covers made of elements
from Maxima(Y, Leq) and returns the set of minimal covers from Y.
The algorithm is described with Cm as input, which is one minimal cover
made of maxima.

The original cyclic core algorithm yields some minimal covers, but not
necessarily the entire set of minimal covers. Some minimal covers can be
lost with that approach.
Instead, the algorithm described below enumerates covers below Maxima(Y, Leq),
amending the step where the original algorithm could lose covers.


Author:  Ioannis Filippidis

--------------------------------------------------------------------------------
Copyright 2017 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
*)
EXTENDS
    FiniteSetFacts,
    FunctionTheorems,
    Lattices,
    Sequences,
    SequenceTheorems,
    TLAPS
(* In order to ensure independence from builtin support of Sequences by TLAPS,
these modules have been developed and checked by replacing the modules
FiniteSets, FiniteSetTheorems, Sequences, SequencesTheorems
with renamed copies, (FiniteSets_copy etc.), and appropriately adjusting
EXTENDS statements where needed. *)


CONSTANTS Leq, X, Y


Z == Support(Leq)
ASSUMPTION CostIsCard ==
    Cost = [cover \in SUBSET Z |-> Cardinality(cover)]

--------------------------------------------------------------------------------
ASSUMPTION ProblemInput ==
    /\ IsACompleteLattice(Leq)
    /\ IsFiniteSet(Z)
    /\ X \subseteq Z
    /\ Y \subseteq Z


THEOREM XYAreFiniteSets ==
    /\ IsFiniteSet(X)
    /\ IsFiniteSet(Y)
PROOF
<1>1. /\ X \subseteq Z
      /\ Y \subseteq Z
    BY ProblemInput
<1>2. IsFiniteSet(Z)
    BY ProblemInput
<1> QED
    BY <1>1, <1>2, FS_Subset


THEOREM HaveCardAsCost == CardinalityAsCost(Z)
PROOF
BY CostIsCard DEF CardinalityAsCost


THEOREM LeqIsPor == IsAPartialOrder(Leq)
PROOF
BY ProblemInput DEF IsACompleteLattice

--------------------------------------------------------------------------------

Only(ymax, C) == { u \in X:  \A yother \in C \ {ymax}:
    ~ Leq[u, yother] }

BelowAndSuff(ymax, C, V) ==
    { y \in V:
        /\ Leq[y, ymax]
        /\ \A q \in Only(ymax, C):  Leq[q, y] }

(* Cm is a cover of X from Maxima(Y, Leq) *)
AllCandidatesBelow(Cm, V) ==
    { S \in SUBSET V:
        /\ Cardinality(S) = Cardinality(Cm)
            (* unnecessary to consider smaller subsets (they cannot be
            covers), or larger subsets (they cannot be minimal) *)
        /\ Refines(S, Cm, Leq) }

(* If IsFiniteSet(S), then f is a bijection, by FS_NatBijection. *)
Enumerate(S) ==
    LET Dom == 1..Cardinality(S)
    IN CHOOSE f:  f \in Bijection(Dom, S)

Image(f, S) == {f[x]:  x \in S}

MinCoversOf(U, V, IsUnder) ==
    { C \in SUBSET V:  IsAMinCover(C, U, V, IsUnder) }


--------------------------------------------------------------------------------
(* Specification of the procedure EnumerateMincoversBelow. *)
CONSTANTS Cm
VARIABLES stack, MinCoversBelow


Max == Maxima(Y, Leq)
Lm == Enumerate(Cm)
N == Cardinality(Cm)  (* N = Len(Lm) *)
Patch(r) == Image(Lm, r..N)

TypeInv == /\ stack \in Seq(SUBSET Y)
           /\ MinCoversBelow \subseteq SUBSET Y

Init == /\ stack = << {} >>
        /\ MinCoversBelow = {}

(* Terminal case that adds a minimal cover to the set MinCoversBelow. *)
Collect ==
    LET
        end == Len(stack)
        Partial == stack[end]
        i == Cardinality(Partial)
        front == SubSeq(stack, 1, end - 1)
    IN
        /\ i = N
        /\ stack' = front
        /\ MinCoversBelow' = MinCoversBelow \cup {Partial}

(* Branching that generates all minimal covers induced by replacing the
next maximal element ymax with all those below it that suffice (succ).
*)
Expand ==
    LET
        end == Len(stack)
        Partial == stack[end]
        i == Cardinality(Partial)
        k == i + 1
        front == SubSeq(stack, 1, end - 1)

        ymax == Lm[k]  (* element to replace *)
        Q == Partial \cup Patch(k)
        succ == BelowAndSuff(ymax, Q, Y)
        enum == Enumerate(succ)
        more == [r \in 1..Len(enum) |-> Partial \cup {enum[r]}]
    IN
        /\ i < N
        /\ stack' = front \o more
        /\ UNCHANGED MinCoversBelow

Next ==
    /\ stack # << >>
    /\ \/ Collect
       \/ Expand

vars == << stack, MinCoversBelow >>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------------------------------------------------------------
(* Invariants. *)

PartialCoversInStack ==
    \A si \in DOMAIN stack:
        LET
            Partial == stack[si]
            i == Cardinality(Partial)
            k == i + 1
            Q == Partial \cup Patch(k)
        IN
            /\ IsAMinCover(Q, X, Y, Leq)
            /\ (Partial \cap Patch(k)) = {}

LeqToBij(C) == CHOOSE g \in Bijection(1..N, C):
    \A q \in 1..N:  Leq[g[q], Lm[q]]

IsPrefixCov(PartialCover, g) ==
    LET
        i == Cardinality(PartialCover)
    IN
        PartialCover = {g[q]:  q \in 1..i}

InvCompl(C) ==
    LET
        g == LeqToBij(C)
    IN
        \/ \E n \in DOMAIN stack:  IsPrefixCov(stack[n], g)
        \/ ~ IsAMinCover(C, X, Y, Leq)
        \/ C \in MinCoversBelow

InvSound(C) == (C \in MinCoversBelow) => IsAMinCover(C, X, Y, Leq)

--------------------------------------------------------------------------------
(* Auxiliary theorems about expressions used to define the action `Next`. *)


THEOREM SubsetYFinite ==
    ASSUME NEW S \in SUBSET Y
    PROVE /\ IsFiniteSet(S)
          /\ Cardinality(S) \in Nat
PROOF
BY XYAreFiniteSets, FS_Subset, FS_CardinalityType


THEOREM LmIsBijection ==
    ASSUME
        Cm \in SUBSET Y
    PROVE
        Lm \in Bijection(1..N, Cm)
PROOF
<1>1. IsFiniteSet(Cm)
    BY SubsetYFinite
<1>2. PICK n \in Nat:  ExistsBijection(1..n, Cm)
    BY <1>1, FS_NatBijection
<1>3. n = N
    <2>1. Cardinality(Cm) = n
        BY <1>2, FS_CountingElements
    <2>2. N = Cardinality(Cm)
        BY DEF N
    <2> QED
        BY <2>1, <2>2
<1>4. ExistsBijection(1..N, Cm)
    BY <1>2, <1>3
<1>5. Bijection(1..N, Cm) # {}
    BY <1>4 DEF ExistsBijection
<1> QED
    BY <1>5 DEF Lm, Enumerate, N


THEOREM NType ==
    ASSUME
        Cm \in SUBSET Y
    PROVE
        N \in Nat
PROOF
BY SubsetYFinite DEF N


THEOREM PatchProperties ==
    ASSUME
        NEW k \in 1..(N + 1),
        Cm \in SUBSET Y
    PROVE
        LET Pc == Patch(k)
        IN /\ Pc \in SUBSET Y
           /\ Pc \in SUBSET Cm
           /\ IsFiniteSet(Pc)
           /\ Cardinality(Pc) = N - k + 1
PROOF
<1> DEFINE
    Pc == Patch(k)
    R == k..N
<1>5. /\ k \in Nat
      /\ N \in Nat
    BY NType
<1>1. Pc = {Lm[x]:  x \in R}
    BY DEF Pc, Patch, Image, R
<1>9. Lm \in Bijection(1..N, Cm)
    BY LmIsBijection
<1>2. /\ R \subseteq DOMAIN Lm
      /\ DOMAIN Lm = 1..N
    <2>1. DOMAIN Lm = 1..N
        BY <1>9 DEF Bijection, Injection
    <2> QED
        BY <2>1, <1>5 DEF R
<1>3. Lm \in [1..N -> Cm]
    BY <1>9 DEF Bijection, Injection
<1>6. Pc \subseteq Cm
    BY <1>1, <1>2, <1>3
<1>4. IsFiniteSet(Cm)
    <2>1. Cm \in SUBSET Y
        OBVIOUS
    <2> QED
        BY <2>1, SubsetYFinite
<1>7. IsFiniteSet(Pc)
    BY <1>6, <1>4, FS_Subset
<1>8. Cardinality(Pc) = N - k + 1
    <2> DEFINE
        q == N - k + 1
        S == 1..q
        f == [n \in S |-> n - 1 + k]
        g == Restrict(Lm, R)
    <2>1. g \in Bijection(R, Pc)
        <3>1. Range(g) = Pc
            BY <1>1 DEF g, Range, Restrict
        <3>2. R \in SUBSET 1..N
            BY <1>2
        <3> QED
            BY <1>1, <1>9, <3>1, <3>2, Fun_BijRestrict
    <2>2. q \in 0..N
        BY <1>5
    <2>3. f \in Bijection(S, R)
        <3> USE <2>2, <1>5 DEF f
        <3>1. f \in Injection(S, R)
            BY DEF Injection
        <3>2. f \in Surjection(S, R)
            BY DEF Surjection
        <3> QED
            BY <3>1, <3>2 DEF Bijection
    <2>4. Cardinality(R) = q
        BY <2>3, <2>2, FS_CountingElements DEF ExistsBijection
    <2>5. Cardinality(R) = Cardinality(Pc)
        <3>1. IsFiniteSet(R) /\ IsFiniteSet(Pc)
            <4>1. IsFiniteSet(R)
                BY <2>2, <2>3, FS_NatBijection DEF ExistsBijection
            <4>2. IsFiniteSet(Pc)
                BY <1>6, Cm \subseteq Y, XYAreFiniteSets, FS_Subset
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <2>1, <3>1, FS_Bijection DEF ExistsBijection
    <2> QED
        BY <2>4, <2>5 DEF q
<1> QED
    BY <1>6, <1>7, <1>8


THEOREM PatchSplit ==
    ASSUME
        NEW k \in 1..N,
        /\ N \in Nat
        /\ Cm \in SUBSET Y
    PROVE
        /\ Patch(k) = {Lm[k]} \cup Patch(k + 1)
        /\ Lm[k] \notin Patch(k + 1)
PROOF
<1> DEFINE
    kp == k + 1
    S == k..N
    Sp == kp..N
<1>1. Patch(k) = Image(Lm, S)
    BY DEF Patch, S
<1>2. Patch(kp) = Image(Lm, Sp)
    BY DEF Patch, Sp, Image
<1>3. Image(Lm, S) = Image(Lm, Sp) \cup {Lm[k]}
    <2>1. Image(Lm, S) = {Lm[x]:  x \in S}
        BY DEF Image, S
    <2>2. Image(Lm, Sp) = {Lm[x]:  x \in Sp}
        BY DEF Image, Sp
    <2>3. {Lm[x]:  x \in S} = {Lm[k]} \cup {Lm[x]:  x \in Sp}
        <3>1. /\ k \in 1..N
              /\ N \in Nat
            OBVIOUS
        <3> QED
            BY <3>1 DEF kp, S, Sp
    <2> QED
        BY <2>1, <2>2, <2>3
<1>4. Lm[k] \notin Patch(k + 1)
    BY LmIsBijection DEF Patch, Bijection, Injection, Image
<1> QED
    BY <1>1, <1>2, <1>3, <1>4


THEOREM BelowAndSuffIsFinite ==
    ASSUME
        NEW R, NEW C, NEW ymax,
        IsFiniteSet(R)
    PROVE
        LET S == BelowAndSuff(ymax, C, R)
        IN IsFiniteSet(S)
PROOF
<1> DEFINE
    S == BelowAndSuff(ymax, C, R)
<1>1. S \subseteq R
    BY DEF BelowAndSuff
<1>2. IsFiniteSet(R)
    OBVIOUS
<1> QED
    BY <1>1, <1>2, FS_Subset


THEOREM EnumerateProperties ==
    ASSUME
        NEW S, IsFiniteSet(S)
    PROVE
        LET
            enum == Enumerate(S)
            Dom == 1..Cardinality(S)
        IN
            /\ enum \in Bijection(Dom, S)
            /\ Len(enum) = Cardinality(S)
            /\ Len(enum) \in Nat
PROOF
<1>2. PICK n \in Nat:  ExistsBijection(1..n, S)
    <2>1. IsFiniteSet(S)
        OBVIOUS
    <2> QED
        BY <2>1, FS_NatBijection
<1>3. n = Cardinality(S)
    BY <1>2, FS_CountingElements
<1>5. Bijection(1..n, S) # {}
    <2>1. ExistsBijection(1..n, S)
        BY <1>2, <1>3
    <2> QED
        BY <2>1 DEF ExistsBijection
<1> DEFINE enum == Enumerate(S)
<1>6. enum \in Bijection(1..n, S)
    BY <1>5, <1>3 DEF Enumerate, enum
<1>7. enum \in Seq(S)
    BY <1>2, <1>6 DEF Bijection, Injection, Seq
<1>8. /\ DOMAIN enum = 1..Len(enum)
      /\ Len(enum) \in Nat
    BY <1>7, LenProperties
<1>9. enum \in Bijection(1..Cardinality(S), S)
    BY <1>3, <1>6
<1>10. Len(enum) = Cardinality(S)
    <2>1. 1..Len(enum) = 1..Cardinality(S)
        BY <1>9, <1>8 DEF Bijection, Injection
    <2>2. enum \in Bijection(1..Len(enum), S)
        BY <1>9, <2>1
    <2> QED
        BY <2>2, <1>8, FS_CountingElements  DEF ExistsBijection
<1> QED
    BY <1>9, <1>8, <1>10 DEF enum


--------------------------------------------------------------------------------
(* Auxiliary theorems about minimal covers. *)


(* Application of MinCoversFromMaxSuffice to current context. *)
LEMMA MinCoverFromMaxYIsMinCoverFromY ==
    ASSUME
        NEW C,
        IsAMinCover(C, X, Max, Leq)
    PROVE
        IsAMinCover(C, X, Y, Leq)
PROOF
<1>1. /\ IsAPartialOrder(Leq)
      /\ IsFiniteSet(Z)
      /\ X \subseteq Z
      /\ Y \subseteq Z
    BY LeqIsPor, ProblemInput
<1>2. CardinalityAsCost(Z)
    BY HaveCardAsCost
<1> QED
    BY <1>1, <1>2, MinCoversFromMaxSuffice DEF Z, Max


(* A minimal cover C contains only essential elements. Otherwise, some
element y \in C would be redundant, so (C \ {y}) a cover, thus C not minimal.
*)
THEOREM MinimalHasAllEssential ==
    ASSUME
        NEW C,
        IsAMinCover(C, X, Y, Leq)
    PROVE
        \A y \in C:  Only(y, C) # {}
PROOF
<1>1. SUFFICES
        ASSUME
            NEW y \in C,
            Only(y, C) = {}
        PROVE FALSE
    OBVIOUS
<1> DEFINE Cy == C \ {y}
<1>5. Cy \in SUBSET Y
    BY MinCoverProperties DEF Cy
<1>2. IsACover(Cy, X, Leq)
    <2>1. SUFFICES ASSUME NEW x \in X
                   PROVE \E q \in Cy:  Leq[x, q]
        BY <2>1 DEF IsACover
    <2>2. SUFFICES ASSUME \A q \in Cy:  ~ Leq[x, q]
                   PROVE FALSE
        BY <2>2
    <2>3. x \in Only(y, C)
        BY <2>2 DEF Only, Cy
    <2> QED
        BY <2>3, <1>1
<1>3. /\ Cardinality(Cy) < Cardinality(C)
      /\ Cardinality(Cy) \in Nat
      /\ Cardinality(C) \in Nat
    <2>1. IsFiniteSet(C)
        BY MinCoverProperties, SubsetYFinite
    <2>2. Cy \subseteq C
        BY DEF Cy
    <2>3. Cy # C
        <3>1. y \in C
            OBVIOUS
        <3> QED
            BY <3>1 DEF Cy
    <2> QED
        BY <2>1, <2>2, <2>3, FS_Subset, FS_CardinalityType
<1>4. Cardinality(C) <= Cardinality(Cy)
    <2>1. /\ Y \in SUBSET Z
          /\ IsAMinCover(C, X, Y, Leq)
          /\ CardinalityAsCost(Z)
        BY ProblemInput, HaveCardAsCost
    <2>2. /\ Cy \in SUBSET Y
          /\ IsACover(Cy, X, Leq)
          /\ Cardinality(Cy) <= Cardinality(C)
        BY <1>5, <1>2, <1>3
    <2> QED
        BY <2>1, <2>2, MinCoverPropertiesCard
<1> QED
    BY <1>3, <1>4


(* Any minimal cover C from Y refines some minimal cover Cm from Maxima(Y, Leq),
and they have the same cardinality. So

MinCoversOf(X, Y, Leq) \subseteq UNION {
    AllCandidatesBelow(Cm, Y):  Cm \in MinCoversOf(X, Maxima(Y, Leq), Leq) }

Also, MinCoversOf(X, Maxima(Y), Leq) induces a partition of
MinCoversOf(X, Y, Leq).
*)
THEOREM MinCoversSubseteqUnionCandidatesBelow ==
    ASSUME
        NEW C,
        IsAMinCover(C, X, Y, Leq)
    PROVE
        \E M:  /\ IsAMinCover(M, X, Max, Leq)
               /\ C \in AllCandidatesBelow(M, Y)
PROOF
<1> DEFINE
    M == MaxHat(C, Y, Leq)
<1>1. IsAMinCover(M, X, Max, Leq)
    <2>1. Z = Support(Leq)
        BY DEF Z
    <2>2. IsAPartialOrder(Leq)
        BY LeqIsPor
    <2>3. /\ IsFiniteSet(Z)
          /\ X \subseteq Z
          /\ Y \subseteq Z
        BY ProblemInput
    <2>4. IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2>5. CardinalityAsCost(Z)
        BY HaveCardAsCost
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, MaxHatOfMinCoverIsAMinCover
            DEF Max, M
<1>2. /\ C \in SUBSET Y
      /\ IsACover(C, X, Leq)
    <2>1. IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2>2. C \in CoversOf(X, Y, Leq)
        BY <2>1 DEF IsAMinCover, IsMinimal
    <2> QED
        BY <2>2 DEF CoversOf
<1>3. /\ Refines(C, M, Leq)
      /\ Cardinality(M) <= Cardinality(C)
    <2>1. Z = Support(Leq)
        BY DEF Z
    <2>2. IsAPartialOrder(Leq)
        BY LeqIsPor
    <2>3. /\ IsFiniteSet(Z)
          /\ Y \subseteq Z
        BY ProblemInput
    <2>4. C \subseteq Y
        BY <1>2
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, MaxHatProperties, CostIsCard DEF M
            (* S <- C, H <- M *)
<1>4. Cardinality(C) = Cardinality(M)
    <2>1. IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2>2. IsAMinCover(M, X, Y, Leq)
        <3>1. IsAMinCover(M, X, Max, Leq)
            BY <1>1
        <3> QED
            BY <3>1, MinCoversFromMaxSuffice, ProblemInput, LeqIsPor,
                HaveCardAsCost DEF Max, Z
    <2> QED
        BY <2>1, <2>2, AllMinCoversSameCard, HaveCardAsCost,
            XYAreFiniteSets, ProblemInput
            (* C <- C, H <- M *)
<1>5. C \in AllCandidatesBelow(M, Y)
    <2>1. C \in SUBSET Y
        BY <1>2
    <2>2. Cardinality(C) = Cardinality(M)
        BY <1>4
    <2>3. Refines(C, M, Leq)
        BY <1>3
    <2> QED
        BY <2>1, <2>2, <2>3 DEF AllCandidatesBelow
<1> QED
    <2>1. IsAMinCover(M, X, Max, Leq)
        BY <1>1
    <2>2. C \in AllCandidatesBelow(M, Y)
        BY <1>5
    <2> QED
        BY <2>1, <2>2 DEF Max


(* Any minimal cover from Y is a finite set, because the lattice Leq has
a finite domain.
*)
THEOREM MinCoverIsFinite ==
    ASSUME
        NEW C,
        IsAMinCover(C, X, Y, Leq)
    PROVE
        /\ IsFiniteSet(C)
        /\ Cardinality(C) \in Nat
PROOF
<1>1. IsFiniteSet(C)
    <2>1. IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2>2. C \in SUBSET Y
        BY <2>1, MinCoverProperties
    <2>3. IsFiniteSet(Y)
        BY XYAreFiniteSets
    <2> QED
        BY <2>2, <2>3, FS_Subset
<1>2. Cardinality(C) \in Nat
    BY <1>1, FS_CardinalityType
<1> QED
    BY <1>1, <1>2


(* If a cover C refines a minimal cover Cm,
then each ym \in Cm has some y \in C below it.
In other words, Cm refines C with respect to Geq.
*)
THEOREM MinCoverRefinementHasBelow ==
    ASSUME
        NEW C \in SUBSET Y,
        NEW ym \in Cm,
        /\ IsAMinCover(Cm, X, Y, Leq)
        /\ IsACover(C, X, Leq)
        /\ Refines(C, Cm, Leq)
    PROVE
        \E y \in C:  Leq[y, ym]
PROOF
<1>1. SUFFICES
        ASSUME \A y \in C:  ~ Leq[y, ym]
        PROVE FALSE
    BY <1>1
<1> DEFINE
    H == Cm \ {ym}
<1>2. /\ Cm \in SUBSET Y
      /\ IsFiniteSet(Cm)
      /\ Cardinality(Cm) \in Nat
    <2>1. IsAMinCover(Cm, X, Y, Leq)
        OBVIOUS
    <2> QED
        BY <2>1, MinCoverProperties, MinCoverIsFinite
<1>3. H \in SUBSET Y
    <2>1. H \subseteq Cm
        BY DEF H
    <2> QED
        BY <2>1, <1>2
<1>4. IsACover(H, X, Leq)
        (* This proof reminds of MaxHatIsCoverToo *)
    <2>1. Refines(C, Cm, Leq)
        OBVIOUS
    <2>2. \A u \in C:  \E v \in Cm:  Leq[u, v]
        BY <2>1 DEF Refines
    <2>3. ASSUME NEW u \in C, NEW v \in Cm, Leq[u, v]
          PROVE v # ym
        <3>1. SUFFICES ASSUME v = ym
                       PROVE FALSE
            BY <3>1
        <3>2. Leq[u, ym]
            BY <2>3, <3>1
        <3>3. ~ Leq[u, ym]
            BY <1>1, <2>3  (* y <- u *)
        <3> QED  (* goal from <3>1 *)
            BY <3>2, <3>3
    <2>4. \A u \in C:  \E v \in Cm \ {ym}:  Leq[u, v]
        BY <2>2, <2>3
    <2>5. IsACover(C, X, Leq)
        OBVIOUS
    <2>6. \A x \in X:  \E u \in C:  Leq[x, u]
        BY <2>5 DEF IsACover
    <2>7. ASSUME NEW x \in X
          PROVE \E v \in H:  Leq[x, v]
        <3>1. PICK u \in C:  Leq[x, u]
            BY <2>6, <2>7
        <3>2. PICK v \in Cm \ {ym}:  Leq[u, v]
            BY <2>4, <3>1
        <3>3. v \in H
            BY <3>2 DEF H
        <3>4. Leq[x, v]
            <4>1. IsTransitive(Leq)
                BY LeqIsPor DEF IsAPartialOrder
            <4>2. Z = Support(Leq)
                BY DEF Z
            <4>3. Leq[x, u] /\ Leq[u, v]
                BY <3>1, <3>2
            <4>4. (x \in Z) /\ (u \in Z) /\ (v \in Z)
                <5>1. x \in Z
                    <6>1. x \in X
                        BY <2>7
                    <6>2. X \subseteq Z
                        BY ProblemInput
                    <6> QED
                        BY <6>1, <6>2
                <5>2. u \in Z
                    <6>1. u \in C
                        BY <3>1
                    <6>2. C \subseteq Z
                        <7>1. C \subseteq Y
                            OBVIOUS
                        <7>2. Y \subseteq Z
                            BY ProblemInput
                        <7> QED
                            BY <7>1, <7>2
                    <6> QED
                        BY <6>1, <6>2
                <5>3. v \in Z
                    <6>1. v \in H
                        BY <3>3
                    <6>2. H \subseteq Z
                        <7>1. H \subseteq Y
                            BY <1>3
                        <7>2. Y \subseteq Z
                            BY ProblemInput
                        <7> QED
                            BY <7>1, <7>2
                    <6> QED
                        BY <6>1, <6>2
                <5> QED
                    BY <5>1, <5>2, <5>3
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4 DEF IsTransitive
        <3> QED
            BY <3>3, <3>4
    <2> QED
        BY <2>7 DEF IsACover
<1>5. /\ IsFiniteSet(Cm) /\ Cardinality(Cm) \in Nat
      /\ IsFiniteSet(H) /\ Cardinality(H) \in Nat
    <2>1. IsFiniteSet(H) /\ Cardinality(H) \in Nat
        <3>1. IsFiniteSet(H)
            <4>1. H \in SUBSET Y
                BY <1>3
            <4>2. IsFiniteSet(Y)
                BY XYAreFiniteSets
            <4> QED
                BY <4>1, <4>2, FS_Subset
        <3>2. Cardinality(H) \in Nat
            BY <3>1, FS_CardinalityType
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <1>2
<1>6. Cardinality(H) < Cardinality(Cm)
    BY <1>5, FS_Subset DEF H
<1>7. Cardinality(Cm) <= Cardinality(H)
    <2>1. /\ Cm \in SUBSET Y
          /\ IsACover(Cm, X, Leq)
          /\ \A r \in SUBSET Y:
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ Cardinality(r) <= Cardinality(Cm)
            \/ Cardinality(Cm) <= Cardinality(r)
        <3>1. IsAMinCover(Cm, X, Y, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, HaveCardAsCost, ProblemInput, MinCoverPropertiesCard
    <2>3. IsACover(H, X, Leq)
        BY <1>4
    <2>4. Cardinality(H) <= Cardinality(Cm)
        BY <1>6, <1>5
    <2> QED
        BY <2>1, <1>3, <2>3, <2>4  (* r <- H *)
<1> QED  (* goal from <1>1 *)
    BY <1>5, <1>6, <1>7


(* Analogous to `HasMaxHat`. *)
LEMMA HasHat ==
    ASSUME
        NEW S, NEW T,
        /\ S \subseteq Z
        /\ T \subseteq Z
        /\ Refines(S, T, Leq)
    PROVE
        LET
            H == Hat(S, T, Leq)
        IN
            (* IsAHat(H, S, T, Leq) *)
            /\ H \in SUBSET T
            /\ Refines(S, H, Leq)
            /\ Cardinality(H) <= Cardinality(S)
PROOF
<1> DEFINE
    H == Hat(S, T, Leq)
<1>1. /\ H \in SUBSET T
      /\ Refines(S, H, Leq)
    <2>1. Refines(S, T, Leq)
        OBVIOUS
    <2> QED
        BY <2>1 DEF H, Hat, SomeAbove, Refines
<1>2. Cardinality(H) <= Cardinality(S)
    <2>1. IsFiniteSet(S)
        <3>1. IsFiniteSet(Z)
            BY ProblemInput
        <3>2. S \subseteq Z
            OBVIOUS
        <3> QED
            BY <3>1, <3>2, FS_Subset
    <2> QED
        BY <2>1, ImageOfFinite DEF H, Hat
<1> QED
    BY <1>1, <1>2

--------------------------------------------------------------------------------
(* Theorems establishing a bijection using Leq. *)


(* If a minimal cover C refines a minimal cover Cm,
then no ym \in Cm can cover two elements a, b \in C.
*)
THEOREM AtMostOneBelow ==
    ASSUME
        NEW C,
        NEW ym \in Cm,
        NEW a \in C, NEW b \in C,
        /\ IsAMinCover(Cm, X, Y, Leq)
        /\ IsAMinCover(C, X, Y, Leq)
        /\ Refines(C, Cm, Leq)
        /\ a # b
        /\ Leq[a, ym]
        /\ Leq[b, ym]
    PROVE
        FALSE
PROOF
<1> DEFINE
    Rest == C \ {a, b}
    H == Hat(Rest, Cm, Leq)
    Q == H \cup {ym}
    k == Cardinality(C)
<1>1. /\ C \in SUBSET Y
      /\ Cm \in SUBSET Y
      /\ IsFiniteSet(C)
      /\ IsFiniteSet(Cm)
      /\ Cardinality(Cm) \in Nat
      /\ Cardinality(C) \in Nat
      /\ k \in Nat
    <2>1. /\ C \in SUBSET Y
          /\ Cm \in SUBSET Y
        <3>1. /\ IsAMinCover(Cm, X, Y, Leq)
              /\ IsAMinCover(C, X, Y, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, MinCoverProperties
    <2>2. IsFiniteSet(Y)
        BY XYAreFiniteSets
    <2>3. IsFiniteSet(C) /\ IsFiniteSet(Cm)
        BY <2>1, <2>2, FS_Subset
    <2> QED
        BY <2>1, <2>3, FS_CardinalityType
<1>2. /\ H \in SUBSET Cm
      /\ H \in SUBSET Y
      /\ IsFiniteSet(H)
      /\ Cardinality(H) \in Nat
    <2>1. Refines(Rest, Cm, Leq)
        <3>1. Refines(C, Cm, Leq)
            OBVIOUS
        <3>2. Rest \in SUBSET C
            BY DEF Rest
        <3> QED
            BY SubsetRefinesToo
                (* S <- C, R <- Rest, T <- Cm *)
    <2>2. /\ Rest \in SUBSET Z
          /\ Cm \in SUBSET Z
        <3>1. Rest \in SUBSET C
            BY DEF Rest
        <3>2. Rest \in SUBSET Y
            BY <3>1, <1>1
        <3> QED
            BY <1>1, <3>2, ProblemInput
    <2>3. /\ H \in SUBSET Cm
          /\ Refines(Rest, H, Leq)
          /\ Cardinality(H) <= Cardinality(Rest)
        BY <2>1, <2>2, HasHat DEF H
            (* S <- Rest, T <- Cm *)
    <2>4. /\ IsFiniteSet(H)
          /\ Cardinality(H) \in Nat
        <3>1. H \in SUBSET Cm
            BY <2>3
        <3>2. IsFiniteSet(Cm)
            BY <1>1
        <3> QED
            BY <3>1, <3>2, FS_Subset, FS_CardinalityType
    <2> QED
        <3>1. (H \subseteq Cm) /\ (Cm \subseteq Y)
            BY <2>3, <1>1
        <3> QED
            BY <3>1, <2>4
<1>3. /\ Q \in SUBSET Cm
      /\ IsFiniteSet(Q)
      /\ Cardinality(Q) \in Nat
      /\ Cardinality(Q) <= Cardinality(H) + 1
    <2>1. Q \in SUBSET Cm
        <3>1. Q = H \cup {ym}
            BY DEF Q
        <3>2. H \subseteq Cm
            BY <1>2
        <3>3. ym \in Cm
            OBVIOUS
        <3> QED
            BY <3>1, <3>2, <3>3
    <2>2. /\ IsFiniteSet(Q)
          /\ Cardinality(Q) <= Cardinality(H) + 1
        BY <1>2, FS_AddElementUpperBound DEF Q
            (* S <- H, x <- ym *)
    <2>3. Cardinality(Q) \in Nat
        BY <2>2, FS_CardinalityType
    <2> QED
        BY <2>2, <2>3, <2>1
<1>4. /\ IsFiniteSet(Rest)
      /\ Cardinality(Rest) \in Nat
    <2>1. Rest \in SUBSET C
        BY DEF Rest
    <2>2. IsFiniteSet(C)
        BY <1>1
    <2> QED
        BY <2>1, <2>2, FS_Subset, FS_CardinalityType
<1>5. IsACover(Q, X, Leq)
    <2>1. IsACover(H, Rest, Leq)
        <3>1. \A u \in C:  \E v \in Cm:  Leq[u, v]
            <4>1. Refines(C, Cm, Leq)
                OBVIOUS
            <4> QED
                BY <4>1 DEF Refines
        <3>2. \A u \in Rest:  \E v \in Cm:  Leq[u, v]
            BY <3>1 DEF Rest
        <3>3. \A u \in Rest:  LET r == SomeAbove(u, Cm, Leq)
                              IN Leq[u, r]
            BY <3>2 DEF SomeAbove
        <3>4. \A u \in Rest:  \E r \in Hat(Rest, Cm, Leq):  Leq[u, r]
            BY <3>3 DEF Hat
        <3>5. \A u \in Rest:  \E r \in H:  Leq[u, r]
            BY <3>4 DEF H
        <3> QED
            BY <3>5 DEF IsACover
    <2>2. IsACover(Q, C, Leq)
        <3>1. SUFFICES
                ASSUME NEW u \in C
                PROVE \E v \in Q:  Leq[u, v]
            BY <3>1 DEF IsACover
        <3>2. CASE u \in {a, b}
            <4>1. Leq[u, ym]
                <5>1. /\ Leq[a, ym]
                      /\ Leq[b, ym]
                    OBVIOUS
                <5> QED
                    BY <3>2, <5>1
            <4>2. ym \in Q
                BY DEF Q
            <4> QED
                BY <4>1, <4>2
        <3>3. CASE u \notin {a, b}
            <4>1. u \in C \ {a, b}
                BY <3>1, <3>3
            <4>2. u \in Rest
                BY <4>1 DEF Rest
            <4>3. PICK v \in H:  Leq[u, v]
                BY <2>1, <4>2 DEF IsACover
            <4>4. v \in Q
                BY <4>3 DEF Q
            <4> QED
                BY <4>3, <4>4
        <3> QED  (* goal from <3>1 *)
            BY <3>2, <3>3
    <2>3. IsACover(C, X, Leq)
        <3>1. IsAMinCover(C, X, Y, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, MinCoverProperties
    <2>4. /\ Q \subseteq Z
          /\ C \subseteq Z
          /\ X \subseteq Z
        <3>1. Y \subseteq Z
            BY ProblemInput
        <3>2. C \subseteq Z
            <4>1. C \subseteq Y
                BY <1>1
            <4> QED
                BY <4>1, <3>1
        <3>3. Q \subseteq Z
            <4>1. Q \subseteq Cm
                BY <1>3
            <4>2. Cm \subseteq Y
                BY <1>1
            <4> QED
                BY <4>1, <4>2, <3>1
        <3>4. X \subseteq Z
            BY ProblemInput
        <3> QED
            BY <3>2, <3>3, <3>4
    <2> QED
        BY <2>2, <2>3, <2>4, ProblemInput, LatticeProperties,
            CoveringIsTransitive DEF Z
<1>6. Cardinality(Q) <= k - 1
    <2>1. Cardinality(H) <= k - 2
        <3>1. Cardinality(C \ {a, b}) = k - 2
            <4>1. a \in C
                OBVIOUS
            <4>2. IsFiniteSet(C)
                BY <1>1
            <4>3. /\ IsFiniteSet(C \ {a})
                  /\ Cardinality(C \ {a}) = Cardinality(C) - 1
                BY <4>1, <4>2, FS_RemoveElement
            <4>4. Cardinality(C \ {a}) = k - 1
                BY <4>3 DEF k
            <4>5. b \in (C \ {a})
                <5>1. /\ a # b
                      /\ b \in C
                    OBVIOUS
                <5> QED
                    BY <5>1
            <4>6. Cardinality(C \ {a, b}) = Cardinality(C \ {a}) - 1
                BY <4>3, <4>5, FS_RemoveElement
            <4> QED
                BY <1>1, <4>4, <4>6
        <3>2. Cardinality(Rest) = k - 2
            BY <3>1 DEF Rest
        <3>3. Cardinality(H) <= Cardinality(Rest)
            BY <1>4, ImageOfFinite DEF H, Hat
        <3> QED
            BY <3>2, <3>3
    <2>2. Cardinality(Q) <= Cardinality(H) + 1
        <3>1. \/ Cardinality(Q) = Cardinality(H)
              \/ Cardinality(Q) = Cardinality(H) + 1
            <4>1. IsFiniteSet(H)
                BY <1>2
            <4>2. Q = H \cup {ym}
                BY DEF Q
            <4> QED
                BY <4>1, <4>2, FS_AddElement
        <3> QED
            BY <3>1, <1>2, <1>3
    <2> QED
        <3>1. Cardinality(H) \in Nat
            BY <1>2
        <3>2. Cardinality(Q) \in Nat
            BY <1>3
        <3>3. k \in Nat
            BY <1>1
        <3> QED
            BY <2>1, <2>2, <3>1, <3>2, <3>3
<1>7. k <= Cardinality(Q)
    <2>1. Q \in SUBSET Y
        <3>1. Q \subseteq Cm
            BY <1>3
        <3>2. Cm \subseteq Y
            BY <1>1
        <3> QED
            BY <3>1, <3>2
    <2>2. IsACover(Q, X, Leq)
        BY <1>5
    <2>3. Cardinality(Q) <= Cardinality(C)
        BY <1>6, <1>1, <1>3 DEF k
    <2>4. \A r \in SUBSET Y:
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ (Cardinality(r) <= Cardinality(C))
            \/ (Cardinality(C) <= Cardinality(r))
        <3>1. IsAMinCover(C, X, Y, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, HaveCardAsCost, ProblemInput,
                MinCoverPropertiesCard
    <2>5. Cardinality(C) <= Cardinality(Q)
        BY <2>1, <2>2, <2>3, <2>4
    <2> QED
        BY <2>5 DEF k
<1> QED
    BY <1>1, <1>3, <1>6, <1>7


(* If a minimal cover C refines a minimal cover Cm,
then no two elements a, b \in Cm can cover the same element y \in C.
*)
THEOREM AtMostOneAbove ==
    ASSUME
        NEW C,
        NEW y \in C,
        NEW a \in Cm, NEW b \in Cm,
        /\ IsAMinCover(Cm, X, Y, Leq)
        /\ IsAMinCover(C, X, Y, Leq)
        /\ Refines(C, Cm, Leq)
        /\ a # b
        /\ Leq[y, a]
        /\ Leq[y, b]
    PROVE
        FALSE
PROOF
<1> DEFINE
    S == C \ {y}
    H == Hat(S, Cm, Leq)
    Q == H \cup {y}
    k == Cardinality(Cm)
<1>1. /\ C \in SUBSET Y
      /\ Cm \in SUBSET Y
    <2>1. /\ IsAMinCover(Cm, X, Y, Leq)
          /\ IsAMinCover(C, X, Y, Leq)
        OBVIOUS
    <2> QED
        BY <2>1, MinCoverProperties
<1>2. /\ IsFiniteSet(C)
      /\ IsFiniteSet(Cm)
      /\ Cardinality(Cm) \in Nat
    <2>1. IsFiniteSet(Y)
        BY XYAreFiniteSets
    <2> QED
        BY <1>1, <2>1, FS_Subset, FS_CardinalityType
<1>3. /\ \A u \in C \ {y}:  ~ Leq[u, a]
      /\ \A u \in C \ {y}:  ~ Leq[u, b]
    <2>1. ASSUME
            NEW r \in Cm,
            NEW u \in C \ {y},
            Leq[y, r]
          PROVE
            ~ Leq[u, r]
        <3>1. SUFFICES
                ASSUME Leq[u, r]
                PROVE FALSE
            BY <3>1
        <3>2. u # y
            BY <2>1
        <3>3. /\ IsAMinCover(Cm, X, Y, Leq)
              /\ IsAMinCover(C, X, Y, Leq)
              /\ Refines(C, Cm, Leq)
            OBVIOUS
        <3> QED  (* goal from <3>1 *)
            BY <2>1, <3>1, <3>2, <3>3, AtMostOneBelow
                (* a <- y, b <- u, ym <- r *)
    <2>2. /\ a \in Cm
          /\ b \in Cm
        OBVIOUS
    <2> QED
        BY <2>1, <2>2
<1>4. /\ a \notin H
      /\ b \notin H
    <2>1. a \notin H
        <3>1. SUFFICES
                ASSUME a \in H
                PROVE FALSE
            BY <3>1
        <3>2. PICK u \in S:  a = SomeAbove(u, Cm, Leq)
            BY <3>1 DEF H, Hat
        <3>3. u \in C
            BY <3>2 DEF S
        <3>4. \E r \in Cm:  Leq[u, r]
            <4>1. Refines(C, Cm, Leq)
                OBVIOUS
            <4> QED
                BY <4>1, <3>3 DEF Refines
        <3>5. Leq[u, a]
            <4>1. a = SomeAbove(u, Cm, Leq)
                BY <3>2
            <4> QED
                BY <4>1, <3>4 DEF SomeAbove
        <3>6. ~ Leq[u, a]
            BY <1>3, <3>2 DEF S
        <3> QED
            BY <3>5, <3>6
    <2>2. b \notin H
        <3>1. SUFFICES
                ASSUME b \in H
                PROVE FALSE
            BY <3>1
        <3>2. PICK u \in S:  b = SomeAbove(u, Cm, Leq)
            BY <3>1 DEF H, Hat
        <3>3. u \in C
            BY <3>2 DEF S
        <3>4. \E r \in Cm:  Leq[u, r]
            <4>1. Refines(C, Cm, Leq)
                OBVIOUS
            <4> QED
                BY <4>1, <3>3 DEF Refines
        <3>5. Leq[u, b]
            <4>1. b = SomeAbove(u, Cm, Leq)
                BY <3>2
            <4> QED
                BY <4>1, <3>4 DEF SomeAbove
        <3>6. ~ Leq[u, b]
            BY <1>3, <3>2 DEF S
        <3> QED
            BY <3>5, <3>6
    <2> QED
        BY <2>1, <2>2
<1>5. /\ H \in SUBSET Cm
      /\ Refines(S, H, Leq)
      /\ Cardinality(H) <= Cardinality(S)
    <2>1. /\ S \subseteq Z
          /\ Cm \subseteq Z
        <3>1. S \subseteq Z
            <4>1. S \subseteq C
                BY DEF S
            <4>2. C \subseteq Y
                BY <1>1
            <4>3. Y \subseteq Z
                BY ProblemInput
            <4> QED
                BY <4>1, <4>2, <4>3
        <3>2. Cm \subseteq Z
            <4>1. Cm \subseteq Y
                BY <1>1
            <4>2. Y \subseteq Z
                BY ProblemInput
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <3>1, <3>2
    <2>2. Refines(S, Cm, Leq)
        <3>1. S \subseteq C
            BY DEF S
        <3>2. Refines(C, Cm, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, <3>2, SubsetRefinesToo
                (* S <- C, T <- Cm, R <- S *)
    <2> QED
        BY <2>1, <2>2, HasHat DEF H  (* T <- Cm *)
<1>6. /\ IsFiniteSet(H)
      /\ Cardinality(H) \in Nat
      /\ Cardinality(H) <= k - 2
    <2>1. H \subseteq Cm \ {a, b}
        BY <1>5, <1>4
    <2>2. /\ IsFiniteSet(Cm \ {a, b})
          /\ Cardinality(Cm \ {a, b}) = k - 2
        <3>1. a \in Cm
            OBVIOUS
        <3>2. IsFiniteSet(Cm)
            BY <1>2
        <3>3. /\ IsFiniteSet(Cm \ {a})
              /\ Cardinality(Cm \ {a}) = Cardinality(Cm) - 1
            BY <3>1, <3>2, FS_RemoveElement
        <3>4. b \in (Cm \ {a})
            <4>1. /\ b \in Cm
                  /\ a # b
                OBVIOUS
            <4> QED
                BY <4>1
        <3>5. /\ IsFiniteSet(Cm \ {a, b})
              /\ Cardinality(Cm \ {a, b}) = Cardinality(Cm \ {a}) - 1
            BY <3>3, <3>4, FS_RemoveElement
        <3>6. Cardinality(Cm) \in Nat
            BY <1>2
        <3> QED
            BY <3>3, <3>5, <3>6 DEF k
    <2> QED
        BY <2>1, <2>2, FS_Subset, FS_CardinalityType
<1>7. IsACover(Q, C, Leq)
    <2>1. SUFFICES
            ASSUME NEW u \in C
            PROVE \E v \in Q:  Leq[u, v]
        BY <2>1 DEF IsACover
    <2>2. CASE u = y
        <3> DEFINE v == y
        <3>1. v \in Q
            <4>1. v \in H \cup {y}
                BY DEF v
            <4> QED
                BY <4>1 DEF Q
        <3>2. Leq[u, v]
            <4>1. Leq[y, y]
                <5>1. y \in Z
                    <6>1. y \in C
                        OBVIOUS
                    <6>2. C \subseteq Y
                        BY <1>1
                    <6>3. Y \subseteq Z
                        BY ProblemInput
                    <6> QED
                        BY <6>1, <6>2, <6>3
                <5>2. IsReflexive(Leq)
                    BY ProblemInput DEF IsACompleteLattice,
                        IsAPartialOrder
                <5> QED
                    BY <5>1, <5>2 DEF IsReflexive, Z
            <4> QED
                BY <4>1, <2>2 DEF v
        <3> QED  (* goal from <2>1 *)
            BY <3>1, <3>2
    <2>3. CASE u # y
        <3>1. u \in C \ {y}
            BY <2>1, <2>3
        <3>2. u \in S
            BY <3>1 DEF S
        <3>3. Refines(S, H, Leq)
            BY <1>5
        <3>4. \A p \in S:  \E q \in H:  Leq[p, q]
            BY <3>3 DEF Refines
        <3>5. PICK v \in H:  Leq[u, v]
            BY <3>4, <3>2
        <3>6. v \in Q
            BY <3>5 DEF Q
        <3> QED  (* goal from <2>1 *)
            BY <3>5, <3>5
    <2> QED
        BY <2>2, <2>3
<1>8. IsACover(Q, X, Leq)
    <2>1. IsACover(Q, C, Leq)
        BY <1>7
    <2>2. IsACover(C, X, Leq)
        <3>1. IsAMinCover(C, X, Y, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, MinCoverProperties
    <2>3. IsTransitive(Leq)
        BY ProblemInput DEF IsACompleteLattice, IsAPartialOrder
    <2>4. /\ X \subseteq Z
          /\ C \subseteq Z
          /\ Q \subseteq Z
        <3>1. X \subseteq Z
            BY ProblemInput
        <3>2. C \subseteq Z
            <4>1. C \subseteq Y
                BY <1>1
            <4>2. Y \subseteq Z
                BY ProblemInput
            <4> QED
                BY <4>1, <4>2
        <3>3. Q \subseteq Z
            <4>1. Q = H \cup {y}
                BY DEF Q
            <4>2. Y \subseteq Z
                BY ProblemInput
            <4>3. H \subseteq Z
                <5>1. H \subseteq Cm
                    BY <1>5
                <5>2. Cm \subseteq Y
                    BY <1>1
                <5> QED
                    BY <5>1, <5>2, <4>2
            <4>4. y \in Z
                <5>1. y \in C
                    OBVIOUS
                <5>2. C \subseteq Y
                    BY <1>1
                <5> QED
                    BY <5>1, <5>2, <4>2
            <4> QED
                BY <4>1, <4>3, <4>4
        <3> QED
            BY <3>1, <3>2, <3>3
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, CoveringIsTransitive DEF Z
            (* A <- X, B <- C, C <- Q *)
<1>9. /\ IsFiniteSet(Q)
      /\ Cardinality(Q) \in Nat
      /\ Cardinality(Q) <= k - 1
    <2>1. /\ IsFiniteSet(Q)
          /\ Cardinality(Q) <= Cardinality(H) + 1
        <3>1. IsFiniteSet(H)
            BY <1>6
        <3>2. Q = H \cup {y}
            BY DEF Q
        <3> QED
            BY <3>1, <3>2, FS_AddElementUpperBound
    <2>2. /\ Cardinality(H) \in Nat
          /\ Cardinality(H) <= k - 2
        BY <1>6
    <2>3. k \in Nat
        BY <1>2 DEF k
    <2>4. Cardinality(Q) \in Nat
        BY <2>1, FS_CardinalityType
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4
<1>10. k <= Cardinality(Q)
    <2>1. Q \in SUBSET Y
        <3>1. Q = H \cup {y}
            BY DEF Q
        <3>2. H \subseteq Y
            <4>1. H \subseteq Cm
                BY <1>5
            <4>2. Cm \subseteq Y
                BY <1>1
            <4> QED
                BY <4>1, <4>2
        <3>3. y \in Y
            <4>1. y \in C
                OBVIOUS
            <4>2. C \subseteq Y
                <5>1. IsAMinCover(C, X, Y, Leq)
                    OBVIOUS
                <5> QED
                    BY <5>1, MinCoverProperties
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <3>1, <3>2, <3>3
    <2>2. IsACover(Q, X, Leq)
        BY <1>8
    <2>3. Cardinality(Q) <= Cardinality(Cm)
        <3>1. Cardinality(Q) \in Nat
            BY <1>9
        <3>2. Cardinality(Cm) \in Nat
            BY <1>2
        <3>3. Cardinality(Q) <= k - 1
            BY <1>9
        <3>4. k = Cardinality(Cm)
            BY DEF k
        <3> QED
            BY <2>1, <3>1, <3>2, <3>3, <3>4
    <2>4. \A r \in SUBSET Y:
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ Cardinality(r) <= Cardinality(Cm)
            \/ Cardinality(Cm) <= Cardinality(r)
        <3>1. IsAMinCover(Cm, X, Y, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, HaveCardAsCost, ProblemInput,
                MinCoverPropertiesCard
    <2>5. Cardinality(Cm) <= Cardinality(Q)
        BY <2>1, <2>2, <2>3, <2>4
    <2> QED
        BY <2>5 DEF k
<1> QED
    <2>1. /\ Cardinality(Q) \in Nat
          /\ k \in Nat
        BY <1>9, <1>2 DEF k
    <2>2. Cardinality(Q) <= k - 1
        BY <1>9
    <2>3. k <= Cardinality(Q)
        BY <1>10
    <2> QED
        BY <2>1, <2>2, <2>3


(* If a minimal cover C refines another minimal cover Cm, then Leq
induces a unique bijection between them.
*)
THEOREM MinCoverRefinementInducesBijection ==
    ASSUME
        NEW C,
        /\ IsAMinCover(C, X, Y, Leq)
        /\ IsAMinCover(Cm, X, Y, Leq)
        /\ Refines(C, Cm, Leq)
    PROVE
        LET g == LeqToBij(C)
        IN  /\ g \in Bijection(1..N, C)
            /\ \A q \in 1..N:
                /\ Leq[g[q], Lm[q]]
                /\ \A p \in 1..N \ {q}:
                        (* Lm[q] is above only g[q] *)
                    /\ ~ Leq[g[p], Lm[q]]
                        (* g[q] is below only Lm[q] *)
                    /\ ~ Leq[g[q], Lm[p]]
PROOF
<1> DEFINE
    g == LeqToBij(C)
    f == [ym \in Cm |-> CHOOSE y \in C:  Leq[y, ym]]
    h == [q \in 1..N |-> f[Lm[q]]]
    R == Range(h)
<1>1. /\ IsAMinCover(C, X, Y, Leq)
      /\ IsAMinCover(Cm, X, Y, Leq)
      /\ Refines(C, Cm, Leq)
      /\ C \in SUBSET Y
      /\ IsACover(C, X, Leq)
      /\ Cm \in SUBSET Y
    <2>1. /\ IsAMinCover(Cm, X, Y, Leq)
          /\ IsAMinCover(C, X, Y, Leq)
          /\ Refines(C, Cm, Leq)
        OBVIOUS
    <2>2. /\ C \in SUBSET Y
          /\ IsACover(C, X, Leq)
        BY <2>1, MinCoverProperties
    <2>3. /\ Cm \in SUBSET Y
        BY <2>1, MinCoverProperties
    <2> QED
        BY <2>1, <2>2, <2>3
<1>2. \A ym \in Cm:  /\ f[ym] \in C
                     /\ Leq[f[ym], ym]
    <2>1. SUFFICES ASSUME NEW ym \in Cm
                   PROVE /\ f[ym] \in C
                         /\ Leq[f[ym], ym]
        BY <2>1
    <2>2. f[ym] = CHOOSE y \in C:  Leq[y, ym]
        <3>1. ym \in DOMAIN f
            <4>1. ym \in Cm
                BY <2>1
            <4>2. Cm = DOMAIN f
                BY DEF f
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <3>1 DEF f
    <2>3. \A yq \in Cm:  \E y \in C:  Leq[y, yq]
        BY <1>1, MinCoverRefinementHasBelow
    <2>4. \E y \in C:  Leq[y, ym]
        <3>1. ym \in Cm
            BY <2>1
        <3> QED
            BY <2>3, <3>1  (* yq <- ym *)
    <2> QED  (* goal from <2>1 *)
        BY <2>2, <2>4
<1>3. /\ h \in Bijection(1..N, C)
      /\ \A q \in 1..N:  Leq[h[q], Lm[q]]
    <2>1. h \in [1..N -> C]
        <3>1. ASSUME NEW q \in 1..N
              PROVE h[q] \in C
            <4> DEFINE
                ym == Lm[q]
                y == f[ym]
            <4>1. Lm \in [1..N -> Cm]
                BY <1>1, LmIsBijection DEF Bijection, Injection
            <4>2. ym \in Cm
                BY <4>1, <3>1 DEF ym
            <4>3. y \in C
                <5>1. f[ym] \in C
                    BY <1>2, <4>2
                <5> QED
                    BY <5>1 DEF y
            <4>4. h[q] = y
                <5>1. h[q] = f[Lm[q]]
                    BY <3>1 DEF h
                <5>2. h[q] = f[ym]
                    BY <5>1 DEF ym
                <5> QED
                    BY <5>2 DEF y
            <4> QED
                BY <4>3, <4>4
        <3> QED
            BY <3>1 DEF h
    <2>2. h \in Injection(1..N, C)
        <3>1. SUFFICES
                ASSUME
                    NEW qa \in 1..N, NEW qb \in 1..N,
                    /\ qa # qb
                    /\ h[qa] = h[qb]
                PROVE FALSE
            BY <3>1, <2>1 DEF Injection
        <3>2. /\ h[qa] = f[Lm[qa]]
              /\ h[qb] = f[Lm[qb]]
            BY <3>1 DEF h
        <3> DEFINE
            a == Lm[qa]
            b == Lm[qb]
            y == f[a]
        <3>3. y = f[b]
            <4>1. h[qa] = h[qb]
                BY <3>1
            <4>2. f[Lm[qa]] = f[Lm[qb]]
                BY <4>1, <3>2
            <4>3. f[a] = f[b]
                BY <4>2 DEF a, b
            <4> QED
                BY <4>3 DEF y
        <3>4. /\ a # b
              /\ y \in C
              /\ a \in Cm
              /\ b \in Cm
              /\ Leq[y, a] /\ Leq[y, b]
            <4>1. /\ Lm \in [1..N -> Cm]
                  /\ \A a1, b1 \in 1..N:
                    (Lm[a1] = Lm[b1])  =>  (a1 = b1)
                BY <1>1, LmIsBijection DEF Bijection, Injection
                    (* M <- Lm, S <- 1..N, T <- Cm *)
            <4>2. /\ qa \in 1..N
                  /\ qb \in 1..N
                  /\ qa # qb
                BY <3>1
            <4>3. a # b
                <5>1. Lm[qa] # Lm[qb]
                    BY <4>1, <4>2
                <5> QED
                    BY <5>1 DEF a, b
            <4>4. /\ y \in C
                  /\ a \in Cm
                  /\ b \in Cm
                  /\ Leq[y, a] /\ Leq[y, b]
                <5>1. /\ a \in Cm
                      /\ b \in Cm
                    <6>1. /\ Lm[qa] \in Cm
                          /\ Lm[qb] \in Cm
                        BY <4>1, <4>2
                    <6> QED
                        BY <6>1 DEF a, b
                <5>2. /\ f[a] \in C
                      /\ Leq[f[a], a]
                      /\ Leq[f[b], b]
                    BY <1>2, <5>1
                <5>3. /\ y \in C
                      /\ Leq[y, a]
                      /\ Leq[y, b]
                    BY <5>2, <3>3 DEF y
                <5> QED
                    BY <5>1, <5>3
            <4> QED
                BY <4>3, <4>4
        <3> QED  (* goal from <3>1 *)
            BY <3>4, <1>1, AtMostOneAbove

    <2>3. h \in Surjection(1..N, C)
            (* An alternative proof for this step is via AtMostOneBelow *)
        <3>1. SUFFICES
                ASSUME NEW t \in C,
                    \A s \in 1..N:  h[s] # t
                PROVE FALSE
            BY <3>1, <2>1 DEF Surjection
        <3>2. h \in Injection(1..N, C)
            BY <2>2
        <3>3. /\ R \subseteq C
              /\ R # C
            <4>1. R \subseteq C
                BY <3>2 DEF R, Range, Injection
            <4>2. t \notin R
                <5>1. SUFFICES
                        ASSUME t \in R
                        PROVE FALSE
                    BY <5>1
                <5>2. PICK s \in 1..N:  h[s] = t
                    <6>1. h \in [1..N -> C]
                        BY <3>2 DEF Injection
                    <6>2. (DOMAIN h) = (1..N)
                        BY <6>1
                    <6>3. t \in {h[x]:  x \in DOMAIN h}
                        BY <5>1 DEF R, Range
                    <6>4. t \in {h[x]:  x \in 1..N}
                        BY <6>2, <6>3
                    <6> QED
                        BY <6>4
                <5> QED  (* goal from <5>1 *)
                    BY <5>2, <3>1
            <4> QED
                BY <4>1, <4>2
        <3>4. h \in Surjection(1..N, R)
                (* h is a surjection on its range *)
            BY <2>1, Fun_RangeProperties DEF R
                (* f <- h, S <- 1..N, T <- C *)
        <3>5. N \in Nat
            <4>1. N = Cardinality(Cm)
                BY DEF N
            <4>2. IsFiniteSet(Cm)
                <5>1. Cm \in SUBSET Y
                    BY <1>1
                <5>2. IsFiniteSet(Y)
                    BY XYAreFiniteSets
                <5> QED
                    BY <5>1, <5>2, FS_Subset
            <4> QED
                BY <4>1, <4>2, FS_CardinalityType
        <3>6. /\ IsFiniteSet(1..N)
              /\ Cardinality(1..N) = N
            <4> DEFINE bij == [x \in 1..N |-> x]
            <4>1. bij \in Bijection(1..N, 1..N)
                BY DEF bij, Bijection, Injection, Surjection
            <4> QED
                BY <4>1, <3>5, FS_NatBijection, FS_CountingElements
                    DEF ExistsBijection
        <3>7. /\ IsFiniteSet(R)
              /\ Cardinality(R) = N
            <4>1. h \in Injection(1..N, R)
                BY <3>2, <3>4 DEF Surjection, Injection
            <4> QED
                BY <3>4, <3>6, <4>1, FS_Surjection
                    (* S <- 1..N, T <- R *)
        <3>8. Cardinality(R) < N
            <4>1. IsFiniteSet(C)
                <5>1. C \in SUBSET Y
                    BY <1>1
                <5>2. IsFiniteSet(Y)
                    BY XYAreFiniteSets
                <5> QED
                    BY <5>1, <5>2, FS_Subset
            <4>2. Cardinality(R) < Cardinality(C)
                BY <4>1, <3>3, FS_Subset, FS_CardinalityType
            <4>3. Cardinality(C) = N
                <5>1. N = Cardinality(Cm)
                    BY DEF N
                <5>2. Cardinality(C) = Cardinality(Cm)
                    BY <1>1, AllMinCoversSameCard,
                        HaveCardAsCost, ProblemInput,
                        XYAreFiniteSets
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>2, <4>3
        <3>9. /\ Cardinality(R) \in Nat
              /\ Cardinality(R) < N
              /\ Cardinality(R) = N
            BY <3>7, <3>8, FS_CardinalityType
        <3> QED
            BY <3>9, <3>5

    <2>4. ASSUME NEW q \in 1..N
          PROVE Leq[h[q], Lm[q]]
        <3> DEFINE
            ym == Lm[q]
            y == f[ym]
        <3>1. h[q] = y
            <4>1. h[q] = f[Lm[q]]
                <5>1. q \in DOMAIN h
                    <6>1. q \in 1..N
                        BY <2>4
                    <6>2. (DOMAIN h) = (1..N)
                        BY DEF h
                    <6> QED
                        BY <6>1, <6>2
                <5> QED
                    BY <5>1 DEF h
            <4> QED
                BY <4>1 DEF y, ym
        <3>2. Leq[y, ym]
            <4>1. ym \in Cm
                <5>1. q \in 1..N
                    BY <2>4
                <5>2. Lm \in [1..N -> Cm]
                    BY <1>1, LmIsBijection DEF Bijection, Injection
                <5>3. Lm[q] \in Cm
                    BY <5>1, <5>2
                <5> QED
                    BY <5>3 DEF ym
            <4>2. Leq[f[ym], ym]
                BY <1>2, <4>1
            <4> QED
                BY <4>2 DEF y
        <3> QED
            BY <3>1, <3>2 DEF ym
    <2> QED
        BY <2>2, <2>3, <2>4 DEF Bijection
<1>4. /\ g \in Bijection(1..N, C)
      /\ \A q \in 1..N:  Leq[g[q], Lm[q]]
    BY <1>3 DEF g, LeqToBij
<1>5. ASSUME
        NEW q \in 1..N,
        NEW p \in 1..N \ {q}
      PROVE
        /\ ~ Leq[g[p], Lm[q]]
        /\ ~ Leq[g[q], Lm[p]]
    <2>1. /\ p # q
          /\ p \in 1..N
          /\ q \in 1..N
        <3>1. p # q
            BY <1>5
        <3>2. /\ p \in 1..N
              /\ q \in 1..N
            BY <1>5
        <3> QED
            BY <3>1, <3>2
    <2>2. Leq[g[q], Lm[q]]
        BY <1>4, <1>5
    <2>3. ASSUME Leq[g[p], Lm[q]]
          PROVE FALSE
        <3> DEFINE
            a == g[p]
            b == g[q]
            ym == Lm[q]
        <3>1. a # b
            <4>3. g \in Bijection(1..N, C)
                BY <1>4
            <4>4. g[p] # g[q]
                BY <2>1, <4>3 DEF Bijection, Injection
            <4> QED
                BY <4>4 DEF a, b
        <3>2. /\ Leq[a, ym]
              /\ Leq[b, ym]
            BY <2>3, <2>2 DEF a, b, ym
        <3>3. /\ a \in C
              /\ b \in C
              /\ ym \in Cm
            <4>1. /\ a \in C
                  /\ b \in C
                <5>1. g \in [1..N -> C]
                    BY <1>4 DEF Bijection, Injection
                <5>2. /\ p \in 1..N
                      /\ q \in 1..N
                    BY <1>5
                <5> QED
                    BY <5>1, <5>2 DEF a, b
            <4>2. ym \in Cm
                <5>1. Lm \in [1..N -> Cm]
                    BY <1>1, LmIsBijection DEF Bijection, Injection
                <5>2. q \in 1..N
                    BY <1>5
                <5> QED
                    BY <5>1, <5>2 DEF ym
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <1>1, <3>1, <3>2, <3>3, AtMostOneBelow
    <2>4. ASSUME Leq[g[q], Lm[p]]
          PROVE FALSE
        <3> DEFINE
            a == Lm[p]
            b == Lm[q]
            y == g[q]
        <3>1. a # b
            BY <2>1, <1>1, LmIsBijection DEF Bijection, Injection, a, b
        <3>2. /\ Leq[y, a]
              /\ Leq[y, b]
            BY <2>2, <2>4 DEF a, b, y
        <3>3. /\ a \in Cm
              /\ b \in Cm
              /\ y \in C
            <4>1. /\ a \in Cm
                  /\ b \in Cm
                <5>1. Lm \in [1..N -> Cm]
                    BY <1>1, LmIsBijection DEF Bijection, Injection
                <5>2. /\ Lm[p] \in Cm
                      /\ Lm[q] \in Cm
                    BY <5>1, <2>1
                <5> QED
                    BY <5>2 DEF a, b
            <4>2. y \in C
                <5>1. g \in [1..N -> C]
                    BY <1>4 DEF Bijection, Injection
                <5>2. g[q] \in C
                    BY <5>1, <2>1
                <5> QED
                    BY <5>2 DEF y
            <4> QED
                BY <4>1, <4>2
        <3> QED
            <4> QED
                BY <3>1, <3>2, <3>3, <1>1, AtMostOneAbove
    <2> QED
        BY <2>3, <2>4
<1> QED
    BY <1>4, <1>5 DEF g


(* Type formula for the operator `more` that appears in the definition
of the action `Expand`.
*)
THEOREM MoreInSeqSubsetY ==
    ASSUME
        /\ TypeInv
        /\ stack # << >>
    PROVE
        LET
            end == Len(stack)
            PartialCover == stack[end]
            i == Cardinality(PartialCover)
            k == i + 1
            ymax == Lm[k]
            Q == PartialCover \cup Patch(k)
            succ == BelowAndSuff(ymax, Q, Y)
            enum == Enumerate(succ)
            more == [r \in 1..Len(enum) |-> PartialCover \cup {enum[r]}]
        IN
            more \in Seq(SUBSET Y)
PROOF
<1> DEFINE
    S == SUBSET Y
    end == Len(stack)
    PartialCover == stack[end]
    i == Cardinality(PartialCover)
    k == i + 1
    ymax == Lm[k]
    Q == PartialCover \cup Patch(k)
    succ == BelowAndSuff(ymax, Q, Y)
    enum == Enumerate(succ)
    more == [r \in 1..Len(enum) |-> PartialCover \cup {enum[r]}]
<1> HIDE DEF S, end, PartialCover, i, k, ymax, Q, succ, enum, more
<1>1. SUFFICES more \in Seq(S)
    BY <1>1 DEF S, end, PartialCover, i, k, ymax, Q, succ, enum, more
<1> DEFINE
    n == Len(enum)
<1>2. more = [r \in 1..n |-> PartialCover \cup {enum[r]}]
    BY DEF more, n
<1>3. IsFiniteSet(succ)
    <2>1. IsFiniteSet(Y)
        BY XYAreFiniteSets
    <2> QED
        BY <2>1, BelowAndSuffIsFinite DEF succ
<1>4. n \in Nat
    <2>2. Len(enum) \in Nat
        BY <1>3, EnumerateProperties DEF enum
    <2> QED
        BY <2>2 DEF n
<1>5. SUFFICES
        ASSUME NEW r \in 1..n
        PROVE (PartialCover \cup {enum[r]}) \in S
    <2> DEFINE F(r) == PartialCover \cup {enum[r]}
    <2> HIDE DEF F
    <2>1. \A r \in 1..n:  F(r) \in S
        BY <1>5 DEF F
    <2>2. [r \in 1..n |-> F(r)] \in Seq(S)
        BY <2>1, <1>4, IsASeq
    <2> QED  (* goal from <1>1 *)
        BY <2>2, <1>2 DEF F
<1>6. succ \subseteq Y
    BY DEF succ, BelowAndSuff
<1>7. enum \in Bijection(1..n, succ)
    BY <1>3, EnumerateProperties DEF enum, n
<1>8. enum[r] \in succ
    BY <1>5, <1>7 DEF Bijection, Injection
<1>9. enum[r] \in Y
    BY <1>6, <1>8
<1>10. PartialCover \in SUBSET Y
    <2>1. TypeInv
        OBVIOUS
    <2>2. stack \in Seq(S)
        BY <2>1 DEF TypeInv, S
    <2>3. /\ end \in Nat
          /\ stack \in [1..end -> S]
          /\ (DOMAIN stack) = (1..end)
        BY <2>2, LenProperties DEF end
    <2>4. end \in (1..end)
        BY <2>3, stack # << >> DEF end, EmptySeq
    <2>5. end \in (DOMAIN stack)
        BY <2>3, <2>4
    <2>6. stack[end] \in S
        BY <2>3, <2>5
    <2> QED
        BY <2>6 DEF PartialCover, S
<1>11. (PartialCover \cup {enum[r]}) \in SUBSET Y
    BY <1>9, <1>10
<1> QED  (* goal from <1>5 *)
    BY <1>11 DEF S

--------------------------------------------------------------------------------
(* Invariance theorems. *)


THEOREM TypeOK ==
    Spec => [] TypeInv
PROOF
<1>1. ASSUME Init
      PROVE TypeInv
    <2>1. /\ stack = << {} >>
          /\ MinCoversBelow = {}
        BY <1>1 DEF Init
    <2>2. stack \in Seq(SUBSET Y)
        <3>1. stack \in [1..1 -> SUBSET Y]
            BY <2>1
        <3> QED
            BY <3>1, SeqDef DEF Seq
    <2>3. MinCoversBelow \subseteq SUBSET Y
        BY <2>1
    <2> QED
        BY <2>2, <2>3 DEF TypeInv
<1>2. ASSUME TypeInv /\ Next
      PROVE TypeInv'
    <2> DEFINE
        end == Len(stack)
        Partial == stack[end]
        i == Cardinality(Partial)
        k == i + 1
        front == SubSeq(stack, 1, end - 1)
        ymax == Lm[k]
        Q == Partial \cup Patch(k)
        succ == BelowAndSuff(ymax, Q, Y)
        enum == Enumerate(succ)
        more == [r \in 1..Len(enum) |-> Partial \cup {enum[r]}]
    <2>1. /\ stack \in Seq(SUBSET Y)
          /\ MinCoversBelow \subseteq SUBSET Y
        BY <1>2 DEF TypeInv, Next
    <2>2. SUFFICES /\ stack' \in Seq(SUBSET Y)
                   /\ MinCoversBelow' \subseteq SUBSET Y
        BY <2>2 DEF TypeInv
    <2>3. front \in Seq(SUBSET Y)
        BY <2>1, FrontProperties DEF Front
    <2>4. more \in Seq(SUBSET Y)
        BY <1>2, MoreInSeqSubsetY DEF Next
    <2>5. CASE Collect
        <3>1. stack' \in Seq(SUBSET Y)
            BY <2>5, <2>3 DEF Collect
        <3>2. MinCoversBelow' \subseteq SUBSET Y
            <4>1. SUFFICES Partial \in SUBSET Y
                BY <2>1, <4>1, <2>5 DEF Collect
            <4>2. end \in 1..end
                <5>1. end \in Nat
                    BY <2>1, LenProperties
                <5>2. end # 0
                    BY <2>1, <1>2, EmptySeq DEF Next
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <2>1, <4>2, ElementOfSeq
        <3> QED
            BY <3>1, <3>2
    <2>6. CASE Expand
        <3>1. stack' \in Seq(SUBSET Y)
            BY <2>6, <2>3, <2>4, ConcatProperties DEF Expand
        <3>2. MinCoversBelow' \subseteq SUBSET Y
            BY <2>1, <2>6 DEF Expand
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>5, <2>6, <1>2 DEF Next
<1> DEFINE
    Nx == Next
<1>3. ASSUME TypeInv /\ [Nx]_vars
      PROVE TypeInv'
    BY <1>2, <1>3 DEF TypeInv, vars
<1> QED
    <2>1. (TypeInv /\ [][Nx]_vars)  =>  []TypeInv
        BY <1>3, PTL
    <2>2. (Init /\ [][Next]_vars)  =>  []TypeInv
        BY <2>1, <1>1
    <2> QED
        BY <2>2, PTL DEF Spec


(* We now show that:

    MinCoversOf(X, Y, Leq) \subseteq UNION {
        MinCoversBelow(Cm):  Cm \in MinCoversOf(X, Maxima(Y, Leq), Leq) }

Note that upon termination Len(stack) = 0
*)
THEOREM StrongReductionCompleteness ==
    ASSUME
        NEW C \in SUBSET Y,
            (* The assumption `C \in AllCandidatesBelow(Cm, Y)`,
            too, implies this domain formula. *)
        /\ IsAMinCover(Cm, X, Max, Leq)
        /\ C \in AllCandidatesBelow(Cm, Y)
    PROVE
        Spec  =>  [] InvCompl(C)
PROOF
<1> DEFINE
    g == LeqToBij(C)
    end == Len(stack)
    PartialCover == stack[end]
    i == Cardinality(PartialCover)
    k == i + 1
    front == SubSeq(stack, 1, end - 1)

    y == g[k]
    ymax == Lm[k]
    Q == PartialCover \cup Patch(k)
    succ == BelowAndSuff(ymax, Q, Y)
    enum == Enumerate(succ)
    more == [r \in 1..Len(enum) |-> PartialCover \cup {enum[r]}]
    After == {g[t]:  t \in (k + 1)..N}

<1> HIDE DEF g, end, i, PartialCover, k, front,
            y, ymax, Q, succ, enum, more, After

<1>1. ASSUME Init
      PROVE InvCompl(C)
    <2>1. stack = << {} >>
        BY <1>1 DEF Init
    <2>2. end = 1
        BY <2>1 DEF Len, end
    <2>3. /\ i = 0
          /\ PartialCover = {}
        <3>1. PartialCover = {}
            BY <2>1, <2>2 DEF PartialCover
        <3>2. i = 0
            BY <3>1, FS_EmptySet DEF i
        <3> QED
            BY <3>1, <3>2
    <2>4. \E t \in DOMAIN stack:  IsPrefixCov(stack[t], g)
        <3>1. end \in DOMAIN stack
            BY <2>1, <2>2
        <3>2. IsPrefixCov(PartialCover, g)
            <4>1. PartialCover = {g[q]:  q \in 1..i}
                BY <2>3
            <4> QED
                BY <4>1 DEF IsPrefixCov, i
        <3>3. PartialCover = stack[end]
            BY DEF PartialCover
        <3> QED
            BY <3>1, <3>2, <3>3
    <2> QED
        BY <2>4 DEF g, InvCompl

<1>2. /\ Cm \subseteq Y
      /\ Cm \subseteq Max
    <2>1. Cm \subseteq Maxima(Y, Leq)
        <3>1. IsAMinCover(Cm, X, Max, Leq)
            OBVIOUS
        <3> QED
            BY <3>1, MinCoverProperties DEF Max
    <2> QED
        BY <2>1, MaxIsSubset DEF Max

<1>3. ASSUME TypeInv /\ TypeInv' /\ Next /\ InvCompl(C)
      PROVE InvCompl(C)'
    <2>1. N \in Nat
        <3>1. N = Cardinality(Cm)
            BY DEF N
        <3>2. Cardinality(Cm) \in Nat
            <4>2. Y \subseteq Z
                BY ProblemInput
            <4>3. Cm \subseteq Z
                BY <1>2, <4>2
            <4>4. IsFiniteSet(Z)
                BY ProblemInput
            <4> QED
                BY <4>3, <4>4, FS_Subset, FS_CardinalityType
        <3> QED
            BY <3>1, <3>2
    <2>2. SUFFICES
            ASSUME IsAMinCover(C, X, Y, Leq)
            PROVE
                \/ \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
                \/ C \in MinCoversBelow'
        <3>1. InvCompl(C)'
                <=> \/ \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
                    \/ ~ IsAMinCover(C, X, Y, Leq)
                    \/ C \in MinCoversBelow'
            BY DEF InvCompl, IsPrefixCov, g,
                IsAMinCover, CoversOf, IsMinimal, IsACover
        <3>2. \/ \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
              \/ ~ IsAMinCover(C, X, Y, Leq)
              \/ C \in MinCoversBelow'
            BY <2>2
        <3> QED  (* goal from <1>3 *)
            BY <3>1, <3>2

    (* Expand the invariant. *)
    <2>3. \/ \E n \in DOMAIN stack:  IsPrefixCov(stack[n], g)
          \/ C \in MinCoversBelow
        <3>1. InvCompl(C)
            BY <1>3
        <3>2. \/ \E n \in DOMAIN stack:  IsPrefixCov(stack[n], g)
              \/ ~ IsAMinCover(C, X, Y, Leq)
              \/ C \in MinCoversBelow
            BY <3>1 DEF InvCompl, g
        <3> QED
            BY <3>2, <2>2

    (* Monotonicity of MinCoversBelow. *)
    <2>4. ASSUME C \in MinCoversBelow
          PROVE C \in MinCoversBelow'
        <3>1. /\ stack # << >>
              /\ \/ Collect
                 \/ Expand
            BY <1>3 DEF Next
        <3>2. MinCoversBelow \subseteq MinCoversBelow'
            <4>1. ASSUME Collect
                  PROVE MinCoversBelow \subseteq MinCoversBelow'
                BY <4>1 DEF Collect
            <4>2. ASSUME Expand
                  PROVE MinCoversBelow \subseteq MinCoversBelow'
                <5>1. UNCHANGED MinCoversBelow
                    BY <4>2 DEF Expand
                <5> QED
                    BY <5>1
            <4> QED
                BY <3>1, <4>1, <4>2
        <3> QED
            BY <2>4, <3>2

    <2>5. SUFFICES
            ASSUME C \notin MinCoversBelow
            PROVE
                \/ \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
                \/ C \in MinCoversBelow'
        <3>1. ASSUME C \in MinCoversBelow
              PROVE \/ \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
                    \/ C \in MinCoversBelow'
            BY <2>4
        <3> QED  (* goal from <2>2 *)
            BY <2>5, <3>1  (* which are exhaustive cases *)

    <2>6. /\ stack \in Seq(SUBSET Y)
          /\ stack \in [1..Len(stack) -> SUBSET Y]
          /\ (DOMAIN stack) = (1..Len(stack))
          /\ Len(stack) \in Nat
        <3>1. stack \in Seq(SUBSET Y)
            BY <1>3 DEF TypeInv
        <3> QED
            BY <3>1, LenProperties

    <2>7. end \in Nat
        BY <2>6 DEF end

    <2>8. /\ stack' \in [1..Len(stack') -> SUBSET Y]
          /\ (DOMAIN stack') = (1..Len(stack'))
          /\ Len(stack') \in Nat
        <3>1. stack' \in Seq(SUBSET Y)
            BY <1>3 DEF TypeInv
        <3> QED
            BY <3>1, LenProperties

    <2>9. /\ stack # << >>
          /\ \/ Collect
             \/ Expand
        BY <1>3 DEF Next

    <2>10. /\ end \in (Nat \ {0})
           /\ (end - 1) \in Nat
        <4>1. end \in Nat
            BY <2>7
        <4>2. end # 0
            <5>1. stack # << >>
                BY <2>9
            <5> QED
                BY <2>6, <5>1, EmptySeq DEF end
        <4> QED
            BY <4>1, <4>2

    (* This is almost theorem FrontProperties from
    the module SequenceTheorems, for the case of end # 0. *)
    <2>11. LET sub == SubSeq(stack, 1, end - 1)
           IN /\ sub \in Seq(SUBSET Y)
              /\ Len(sub) = (end - 1)
              /\ \A n \in 1..(end - 1):
                    /\ n \in DOMAIN sub
                    /\ sub[n] = stack[n]
        <3> DEFINE
            a == 1
            b == end - 1
            sub == SubSeq(stack, a, b)
        <3>1. stack \in Seq(SUBSET Y)
            BY <2>6
        <3>2. a \in (1..(Len(stack) + 1))
            BY <2>10 DEF end, a
        <3>3. b \in ((a - 1)..Len(stack))
            BY <2>10 DEF end, a, b
        <3>4. /\ sub \in Seq(SUBSET Y)
              /\ Len(sub) = b - a + 1
            BY <3>1, <3>2, <3>3, SubSeqProperties DEF sub
        <3>5. /\ (DOMAIN sub) = 1..(end - 1)
              /\ Len(sub) = (end - 1)
            <4>1. (DOMAIN sub) = 1..Len(sub)
                BY <3>4, LenProperties
            <4>2. Len(sub) = (end - 1)
                BY <3>4, <2>10 DEF a, b
            <4> QED
                BY <4>1, <4>2, <2>10
        <3>7. SUFFICES
                ASSUME NEW n \in 1..(end - 1)
                PROVE /\ n \in DOMAIN sub
                      /\ sub[n] = stack[n]
            BY <3>4, <3>5, <3>7 DEF sub, a, b
        <3>6. n \in DOMAIN sub
            BY <3>7, <3>5 DEF sub, a, b
        <3>8. sub[n] = stack[n]
            <4>1. \A j \in 1..(b - a + 1):
                    sub[j] = stack[a + j - 1]
                BY <3>1, <3>2, <3>3, SubSeqProperties DEF sub
            <4>2. \A j \in 1..(b - a + 1):
                    sub[j] = stack[j]
                BY <4>1, <2>10 DEF a
            <4>3. DOMAIN sub = 1..(b - a + 1)
                BY <3>4, LenProperties
            <4> QED
                BY <3>6, <4>2, <4>3
        <3> QED
            BY <3>6, <3>8
    <2>12. PICK q \in DOMAIN stack:  IsPrefixCov(stack[q], g)
        BY <2>3, <2>5
    <2>13. q \in 1..Len(stack)
        <3>1. q \in DOMAIN stack
            BY <2>12
        <3> QED
            BY <3>1, <2>6

    (* If the partial cover that is a prefix of C is not in the last element
    on the stack, then it remains where it is in stack'. *)
    <2>14. ASSUME q < Len(stack)
           PROVE \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)

        <3>1. q \in 1..(end - 1)
            <4>1. q \in 1..end
                BY <2>13 DEF end
            <4>2. q < end
                BY <2>14 DEF end
            <4> QED
                BY <4>1, <4>2, <2>7

        <3>2. /\ stack[q]' = stack[q]
              /\ q \in DOMAIN stack'
            <4>1. CASE Collect
                <5>1. stack' = SubSeq(stack, 1, end - 1)
                    BY <4>1 DEF Collect, end
                <5> QED
                    BY <5>1, <3>1, <2>11
            <4>2. CASE Expand
                <5>1. stack' = front \o more
                    BY <4>2 DEF Expand, front, more, enum, succ, ymax, Q,
                        k, i, PartialCover, end
                <5>2. /\ stack[q]' = front[q]
                      /\ q \in DOMAIN stack'
                    <6>1. /\ front \in Seq(SUBSET Y)
                          /\ Len(front) = (end - 1)
                        BY <2>11 DEF front
                    <6>2. more \in Seq(SUBSET Y)
                        BY <1>3, <2>9, MoreInSeqSubsetY DEF
                            end, PartialCover, i, k, ymax, Q,
                            succ, enum, more
                    <6>3. q \in 1..(Len(front) + Len(more))
                        <7>1. Len(more) \in Nat
                            BY <6>2, LenProperties
                        <7>2. Len(front) = (end - 1)
                            BY <6>1
                        <7> QED
                            BY <7>1, <7>2, <2>10, <3>1
                    <6>4. q <= Len(front)
                        <7>1. Len(front) \in Nat
                            BY <6>1, LenProperties
                        <7> QED
                            BY <7>1, <3>1, <2>10, <6>1
                    <6>5. /\ stack' \in Seq(SUBSET Y)
                          /\ stack[q]' = front[q]
                          /\ Len(stack') = Len(front) + Len(more)
                        BY <6>1, <6>2, <6>3, <6>4, <5>1, ConcatProperties
                    <6>6. DOMAIN stack' = 1..(Len(front) + Len(more))
                        BY <6>5, LenProperties
                    <6>7. q \in DOMAIN stack'
                        BY <6>3, <6>6
                    <6> QED
                        BY <6>5, <6>7
                <5>3. front[q] = stack[q]
                    BY <3>1, <2>11 DEF front
                <5> QED
                    BY <5>2, <5>3
            <4> QED
                BY <4>1, <4>2, <2>9
                    (* <4>1, <4>2 are exhaustive by <2>9 *)
        <3>3. IsPrefixCov(stack[q]', g)
            <4>1. IsPrefixCov(stack[q], g)
                BY <2>12
            <4>2. stack[q] = stack[q]'
                BY <3>2
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <3>2, <3>3

    (* So it suffices to consider only the case of q as last element. *)
    <2>15. SUFFICES
            ASSUME
                q = Len(stack)
            PROVE
                \/ \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
                \/ C \in MinCoversBelow'
        <3> QED  (* goal from <2>5 *)
            BY <2>13, <2>14, <2>15, <2>7 DEF end
    <2>16. PartialCover = stack[q]
        <3>1. q = end
            BY <2>15 DEF end
        <3> QED
            BY <3>1 DEF PartialCover

    <2>17. /\ i \in 0..N
           /\ PartialCover \in SUBSET Y

        <3>1. stack \in Seq(SUBSET Y)
            BY <1>3 DEF TypeInv
        <3>2. /\ Len(stack) \in Nat
              /\ (DOMAIN stack) = 1..Len(stack)
              /\ stack \in [1..Len(stack) -> SUBSET Y]
            BY <3>1, LenProperties
        <3>3. q \in DOMAIN stack
            BY <2>15, <3>2
        <3>4. stack[q] \in SUBSET Y
            BY <3>2, <3>3
        <3>5. PartialCover \in SUBSET Y
            BY <2>16, <3>4
        <3>6. IsFiniteSet(Y)
            BY XYAreFiniteSets
        <3>7. IsFiniteSet(PartialCover)
            BY <3>5, <3>6, FS_Subset
        <3>8. Cardinality(PartialCover) \in Nat
            BY <3>7, FS_CardinalityType
        <3>9. i \in Nat
            BY <3>8 DEF i
        <3>10. (i < N) \/ (i = N)
            BY <1>3 DEF Next, Collect, Expand, i, PartialCover, end
        <3>11. i \in 0..N
            BY <3>9, <3>10, <2>1
        <3> QED
            BY <3>11, <3>5

    <2>18. PartialCover = {g[t]:  t \in 1..i}
        <3>1. IsPrefixCov(stack[q], g)
            BY <2>12
        <3>2. PartialCover = stack[q]
            BY <2>16
        <3> QED
            BY <3>1, <3>2 DEF IsPrefixCov, i, PartialCover
    <2> USE <2>1  (* N \in Nat *)

        (* The below step asserts that Leq establishes
        a unique bijection between C and Cm. *)
    <2>19. /\ g \in Bijection(1..N, C)
           /\ \A q1 \in 1..N:
                /\ Leq[g[q1], Lm[q1]]
                /\ \A p \in 1..N \ {q1}:
                    /\ ~ Leq[g[p], Lm[q1]]
                    /\ ~ Leq[g[q1], Lm[p]]

        <3>1. IsAMinCover(C, X, Y, Leq)
            BY <2>2
        <3>2. IsAMinCover(Cm, X, Y, Leq)
            <4>1. IsAMinCover(Cm, X, Max, Leq)
                OBVIOUS
            <4> QED
                BY <4>1, MinCoverFromMaxYIsMinCoverFromY DEF Max
        <3>3. Refines(C, Cm, Leq)
            <4>1. C \in AllCandidatesBelow(Cm, Y)
                OBVIOUS
            <4> QED
                BY <4>1 DEF AllCandidatesBelow  (* S <- C *)
        <3> QED
            BY MinCoverRefinementInducesBijection,
                <3>1, <3>2, <3>3 DEF g

    <2>20. C = {g[t]:  t \in 1..N}
        BY <2>19 DEF Bijection, Surjection
    <2>21. ASSUME i = N
           PROVE C \in MinCoversBelow'

        <3>1. Collect
            <4>1. /\ stack # << >>
                  /\ \/ Collect
                     \/ Expand
                BY <1>3 DEF Next
            <4>2. ~ Expand
                <5>1. ~ (i < N)
                    BY <2>21, <2>17
                <5> QED
                    BY <5>1 DEF Expand, i, PartialCover, end
            <4> QED
                BY <4>1, <4>2
        <3>2. PartialCover = C
            <4>1. PartialCover = {g[t]:  t \in 1..N}
                BY <2>18, <2>21
            <4> QED
                BY <4>1, <2>20
        <3>3. PartialCover \in MinCoversBelow'
            <4>1. MinCoversBelow' = MinCoversBelow \cup {PartialCover}
                BY <3>1 DEF Collect, PartialCover, end
            <4> QED
                BY <4>1
        <3> QED
            BY <3>2, <3>3

    <2>22. SUFFICES  (* Case of action Expand. *)
            ASSUME i < N
            PROVE \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)

        <3>1. i \in 0..N
            BY <2>17
        <3>2. (i < N) \/ (i = N)
            BY <3>1
        <3> QED  (* goal from <2>15 *)
            BY <2>21, <2>22, <3>2
            (* <2>21, <2>22 are exhaustive by <3>2 *)

    <2>23. k \in 1..N
        <3>1. N \in Nat
            BY <2>1
        <3>2. i \in 0..(N - 1)
            BY <2>17, <2>22
        <3>3. k = i + 1
            BY DEF k
        <3> QED
            BY <3>1, <3>2, <3>3

    <2>24. /\ y \in C
           /\ y \in Y

        <3>1. y \in C
            <4>1. k \in 1..N
                BY <2>22, <2>17 DEF k
            <4> QED
                BY <2>19, <4>1 DEF y, Bijection, Surjection
        <3>2. C \subseteq Y
            BY <2>2 DEF IsAMinCover
        <3> QED
            BY <3>1, <3>2

    <2>25. ASSUME y \notin succ
           PROVE FALSE  (* C cannot be a cover in this case. *)
        <3>1. k \in 1..N
            <4>1. i \in 0..(N - 1)
                BY <2>17, <2>22
            <4>2. k = i + 1
                BY DEF k
            <4> QED
                BY <4>1, <4>2, <2>1
        <3>2. PICK x \in Only(ymax, Q):  ~ Leq[x, y]
            <4>1. y \in Y
                BY <2>24
            <4>2. Leq[y, ymax]
                <5>1. k = i + 1
                    BY DEF k
                <5>2. i \in 0..(N - 1)
                    BY <2>17, <2>22
                <5>3. k \in 1..N
                    BY <5>1, <5>2, <2>1
                <5>4. Leq[g[k], Lm[k]]
                    BY <2>19, <5>3
                <5> QED
                    BY <5>4 DEF y, ymax
            <4>3. y \notin {
                    y1 \in Y:  /\ Leq[y1, ymax]
                               /\ \A q1 \in Only(ymax, Q):  Leq[q1, y1] }
                BY <2>25 DEF succ, BelowAndSuff
            <4>4. ~ \A q1 \in Only(ymax, Q):  Leq[q1, y]
                BY <4>1, <4>2, <4>3
            <4>5. \E q1 \in Only(ymax, Q):  ~ Leq[q1, y]
                BY <4>4
            <4> QED
                BY <4>5
        <3>3. PICK yc \in C:  Leq[x, yc]
            <4>1. ASSUME NEW u \in X
                  PROVE \E yc \in C:  Leq[u, yc]
                <5>1. IsAMinCover(C, X, Y, Leq)
                    BY <2>2
                <5>2. IsACover(C, X, Leq)
                    BY <5>1, MinCoverProperties
                <5> QED
                    BY <5>2 DEF IsACover
            <4>2. x \in X
                BY <3>2 DEF Only
            <4> QED
                BY <4>1, <4>2
        <3>4. yc # y
            <4>1. SUFFICES
                    ASSUME yc = y
                    PROVE FALSE
                BY <4>1
            <4>2. ~ Leq[x, y]
                BY <3>2
            <4>3. ~ Leq[x, yc]
                BY <4>1, <4>2
            <4> QED  (* goal from <4>1 *)
                BY <3>3, <4>3
        <3>5. ASSUME yc \in PartialCover
              PROVE FALSE
            <4>1. yc \in Q \ {ymax}
                <5>1. yc \in Q
                    BY <3>5 DEF Q
                <5>2. yc # ymax
                    <6>1. SUFFICES ASSUME yc = ymax
                                   PROVE FALSE
                        BY <6>1
                    <6>2. Leq[yc, ymax]
                        <7>1. yc \in C
                            BY <3>3
                        <7>2. C \in SUBSET Y
                            OBVIOUS
                        <7>3. yc \in Z
                            BY <7>1, <7>2, ProblemInput
                        <7> QED
                            BY <6>1, <7>3, LeqIsPor
                                DEF IsAPartialOrder, IsReflexive, Z
                    <6>3. i \in 0..(N - 1)
                        BY <2>17, <2>22
                    <6>4. PICK t \in 1..i:  yc = g[t]
                        <7>1. PartialCover = {g[t]:  t \in 1..i}
                            BY <2>18
                        <7> QED
                            BY <3>5, <7>1
                    <6>5. k \in 1..N \ {t}
                        <7> USE <2>1  (* N \in Nat *)
                        <7>1. k = i + 1
                            BY DEF k
                        <7>3. k \in (i + 1)..N
                            BY <7>1, <6>3
                        <7>4. t \in 1..i
                            BY <6>4
                        <7>5. k # t
                            BY <6>3, <7>3, <7>4
                        <7> QED
                            BY <7>5, <3>1
                    <6>6. ~ Leq[g[t], Lm[k]]
                        <7>1. t \in 1..N
                            BY <6>4, <6>3
                        <7> QED
                            BY <2>19, <7>1, <6>5  (* q <- t, p <- k *)
                    <6>7. ~ Leq[yc, ymax]
                        <7>1. yc = g[t]
                            BY <6>4
                        <7>2. ymax = Lm[k]
                            BY DEF ymax
                        <7> QED
                            BY <6>6, <7>1, <7>2
                    <6> QED  (* goal from <6>1 *)
                        BY <6>2, <6>7
                <5> QED
                    BY <5>1, <5>2
            <4>2. \A yother \in Q \ {ymax}:  ~ Leq[x, yother]
                BY <3>2 DEF Only
            <4>3. ~ Leq[x, yc]
                BY <4>1, <4>2
            <4> QED
                BY <3>3, <4>3
        <3>6. ASSUME yc \in After
              PROVE FALSE
            <4>1. PICK t \in (k + 1)..N:  yc = g[t]
                <5>1. After = {g[t]:  t \in (k + 1)..N}
                    BY DEF After
                <5>2. yc \in {g[t]:  t \in (k + 1)..N}
                    BY <3>6, <5>1
                <5> QED
                    BY <5>2
            <4>2. DEFINE yt == Lm[t]
            <4>3. t \in 1..N
                <5>1. t \in (k + 1)..N
                    BY <4>1
                <5>2. k \in 1..N
                    BY <3>1
                <5> QED
                    BY <5>1, <5>2
            <4>4. Leq[yc, yt]
                <5>2. Leq[g[t], Lm[t]]
                    BY <2>19, <4>3
                <5>3. yc = g[t]
                    BY <4>1
                <5>4. yt = Lm[t]
                    BY DEF yt
                <5> QED
                    BY <5>2, <5>3, <5>4
            <4>5. Leq[x, yt]
                <5>1. Leq[x, yc]
                    BY <3>3
                <5>2. Leq[yc, yt]
                    BY <4>4
                <5>3. IsTransitive(Leq)
                    BY ProblemInput DEF IsACompleteLattice,
                        IsAPartialOrder
                <5>4. /\ x \in Z
                      /\ yc \in Z
                      /\ yt \in Z
                    <6>1. x \in Z
                        <7>1. x \in X
                            BY <3>2 DEF Only
                        <7>2. X \subseteq Z
                            BY ProblemInput
                        <7> QED
                            BY <7>1, <7>2
                    <6>2. yc \in Z
                        <7>1. yc \in C
                            BY <3>3
                        <7>2. C \subseteq Y
                            BY <2>2 DEF IsAMinCover
                        <7>3. Y \subseteq Z
                            BY ProblemInput
                        <7> QED
                            BY <7>1, <7>2, <7>3
                    <6>3. yt \in Z
                        <7>1. Lm[t] \in Cm
                            <8>1. t \in 1..N
                                BY <4>3
                            <8> QED
                                BY <8>1, <1>2, LmIsBijection DEF Bijection,
                                    Injection
                        <7>2. Cm \subseteq Y
                            BY <1>2
                        <7>3. Y \subseteq Z
                            BY ProblemInput
                        <7> QED
                            BY <7>1, <7>2, <7>3 DEF yt
                    <6> QED
                        BY <6>1, <6>2, <6>3
                <5> QED
                    BY <5>1, <5>2, <5>3, <5>4 DEF IsTransitive, Z
            <4>6. yt \in Q \ {ymax}
                <5>1. yt \in Q
                    <6>1. yt \in Patch(k)
                        <7>1. t \in (k + 1)..N
                            BY <4>1
                        <7>2. Patch(k) = Image(Lm, k..N)
                            BY DEF Patch
                        <7>3. Patch(k) = {Lm[j]:  j \in k..N}
                            BY <7>2 DEF Image
                        <7>4. t \in k..N
                            BY <7>1, <3>1
                        <7>5. Lm[t] \in Patch(k)
                            BY <7>3, <7>4
                        <7> QED
                            BY <7>5 DEF yt
                    <6> QED
                        BY <6>1 DEF Q
                <5>2. yt # ymax
                    <6> USE <2>1  (* N \in Nat *)
                    <6>1. Lm \in Injection(1..N, Cm)
                        BY <1>2, LmIsBijection DEF Bijection
                    <6>2. t \in (k + 1)..N
                        BY <4>1
                    <6>3. k \in 1..N
                        BY <3>1
                    <6>4. /\ k \in DOMAIN Lm
                          /\ t \in DOMAIN Lm
                        <7>1. (1..N) = (DOMAIN Lm)
                            BY <6>1 DEF Injection
                        <7>2. k \in DOMAIN Lm
                            BY <7>1, <6>3
                        <7>3. t \in 1..N
                            BY <6>2, <6>3, <2>1
                        <7> QED
                            BY <7>1, <7>2, <7>3
                    <6>5. k # t
                        BY <6>2, <6>3
                    <6>6. Lm[k] # Lm[t]
                        BY <6>1, <6>4, <6>5 DEF Injection
                    <6> QED
                        <7>1. ymax = Lm[k]
                            BY DEF ymax
                        <7>2. yt = Lm[t]
                            BY DEF yt
                        <7> QED
                            BY <6>6, <7>1, <7>2
                <5> QED
                    BY <5>1, <5>2
            <4>7. \A yother \in Q \ {ymax}:  ~ Leq[x, yother]
                BY <3>2 DEF Only
            <4>8. ~ Leq[x, yt]
                BY <4>6, <4>7  (* yother <- yt *)
            <4> QED
                BY <4>5, <4>8
        <3>7. yc \notin (PartialCover \cup {y} \cup After)
            BY <3>4, <3>5, <3>6
        <3>8. C = (PartialCover \cup {y} \cup After)
            <4>1. PartialCover = {g[t]:  t \in 1..i}
                BY <2>18
            <4>2. i \in 0..(N - 1)
                BY <2>17, <2>22
            <4>3. k = i + 1
                BY DEF k
            <4>4. k \in 1..N
                BY <4>2, <4>3, <2>1
            <4>5. After = {g[t]:  t \in (k + 1)..N}
                BY DEF After
            <4>6. PartialCover = {g[t]:  t \in 1..(k - 1)}
                BY <4>1, <4>3, <4>2
            <4>7. y = g[k]
                BY DEF y
            <4>8. (1..N) = ((1..(k - 1)) \cup {k} \cup ((k + 1)..N))
                BY <4>4, <2>1
            <4>9. {g[t]:  t \in 1..N} = (PartialCover \cup {y} \cup After)
                BY <4>5, <4>6, <4>7, <4>8
            <4>10. C = {g[t]:  t \in 1..N}
                BY <2>20
            <4> QED
                BY <4>9, <4>10
        <3>9. yc \notin C
            BY <3>7, <3>8
        <3> QED
            BY <3>3, <3>9

    <2>26. ASSUME y \in succ
           PROVE \E n \in DOMAIN stack':  IsPrefixCov(stack[n]', g)
        <3> DEFINE
            Ns == Cardinality(succ)
        <3>1. enum \in Bijection(1..Ns, succ)
            <4>1. enum = CHOOSE f:  f \in Bijection(1..Ns, succ)
                BY DEF enum, Enumerate, Ns
            <4>2. Bijection(1..Ns, succ) # {}
                <5>1. PICK n \in Nat:  ExistsBijection(1..n, succ)
                    <6>1. IsFiniteSet(succ)
                        <7>1. BelowAndSuff(ymax, Q, Y) \subseteq Y
                            BY DEF BelowAndSuff
                        <7>2. succ \subseteq Y
                            BY <7>1 DEF succ
                        <7>3. IsFiniteSet(Y)
                            BY XYAreFiniteSets
                        <7> QED
                            BY <7>2, <7>3, FS_Subset
                    <6> QED
                        BY <6>1, FS_NatBijection
                <5>2. n = Cardinality(succ)
                    BY <5>1, FS_CountingElements
                <5>3. ExistsBijection(1..Ns, succ)
                    BY <5>1, <5>2 DEF Ns
                <5> QED
                    BY <5>3 DEF ExistsBijection
            <4> QED
                BY <4>1, <4>2
        <3>2. PICK r \in DOMAIN enum:  enum[r] = y
            <4>1. y \in succ
                BY <2>26
            <4>2. \E r \in (1..Ns):  enum[r] = y
                BY <3>1, <4>1 DEF Bijection, Surjection
            <4>3. (DOMAIN enum) = (1..Ns)
                BY <3>1 DEF Bijection, Surjection
            <4> QED
                BY <4>2, <4>3
        <3>3. /\ r \in DOMAIN more
              /\ r \in Nat
            <4>1. /\ (DOMAIN enum) = (1..Len(enum))
                  /\ Len(enum) \in Nat
                <5>1. enum \in [1..Ns -> succ]
                    BY <3>1 DEF Bijection, Surjection
                <5>2. Ns \in Nat
                    <6>1. IsFiniteSet(succ)
                        BY BelowAndSuffIsFinite, XYAreFiniteSets DEF succ
                    <6> QED
                        BY <6>1, FS_CardinalityType
                <5>3. enum \in Seq(succ)
                    BY <5>1, <5>2 DEF Seq
                <5> QED
                    BY <5>3, LenProperties
            <4>2. (DOMAIN more) = (1..Len(enum))
                BY DEF more
            <4>3. /\ (DOMAIN enum) = (DOMAIN more)
                  /\ (DOMAIN enum) \subseteq Nat
                BY <4>1, <4>2
            <4> QED
                BY <3>2, <4>3
        <3>4. more[r] = PartialCover \cup {enum[r]}
            BY <3>3 DEF more
        <3> DEFINE
            W == PartialCover \cup {enum[r]}
        <3> HIDE DEF W
        <3>5. /\ W = {g[t]:  t \in 1..(i + 1)}
              /\ y \in W
            <4>1. W = PartialCover \cup {y}
                BY <3>2 DEF W
            <4>2. PartialCover = {g[t]:  t \in 1..i}
                BY <2>18
            <4>3. y = g[i + 1]
                <5>1. y = g[k]
                    BY DEF y
                <5>2. k = i + 1
                    BY DEF k
                <5> QED
                    BY <5>1, <5>2
            <4>4. W = {g[t]:  t \in 1..i} \cup {g[i + 1]}
                BY <4>1, <4>2, <4>3
            <4>5. (i \in 0..N) /\ (N \in Nat)
                BY <2>17, <2>1
            <4> QED
                BY <4>1, <4>4, <4>5
        <3>6. Cardinality(W) = k
            <4>1. g \in Bijection(1..N, C)
                BY <2>19
            <4> DEFINE gW == Restrict(g, 1..k)
            <4>2. gW \in Bijection(1..k, W)
                <5>1. 1..k \subseteq 1..N
                    BY <2>23, <2>1
                <5>2. gW \in Bijection(1..k, Range(gW))
                    BY <4>1, <5>1, Fun_BijRestrict DEF gW
                <5>3. Range(gW) = W
                    BY <3>5 DEF W, Range, gW, Restrict, k
                <5> QED
                    BY <5>2, <5>3
            <4> QED
                BY <2>23, <4>2, FS_CountingElements DEF ExistsBijection
        <3>7. stack' = front \o more
            <4>1. \/ Collect
                  \/ Expand
                BY <1>3 DEF Next
            <4>2. i \in 0..(N - 1)
                <5>1. i \in 0..N
                    BY <2>17
                <5>2. N \in Nat
                    BY <2>1
                <5>3. i < N
                    BY <2>22
                <5> QED
                    BY <5>1, <5>2, <5>3
            <4>3. ~ (i = N)
                BY <4>2, <2>1
            <4>4. ~ Collect
                BY <4>3 DEF Collect, i, PartialCover, end
            <4>5. Expand
                BY <4>1, <4>4
            <4> QED
                BY <4>5 DEF Expand, front, more, end,
                    enum, succ, Q, ymax, k, i, PartialCover
        <3>8. PICK n \in DOMAIN stack':  stack[n]' = more[r]
            <4> DEFINE
                fm == Len(front) + Len(more)
                j == r + Len(front)
            <4> HIDE DEF fm, j
            <4>1. stack' = front \o more
                BY <3>7
            <4>2. /\ r \in DOMAIN more
                  /\ r \in Nat
                BY <3>3
            <4>3. more \in Seq(SUBSET Y)
                BY <1>3, MoreInSeqSubsetY DEF Next, end, PartialCover,
                    i, k, ymax, Q, succ, enum, more
            <4>4. front \in Seq(SUBSET Y)
                BY <2>11 DEF front
            <4>5. /\ Len(more) \in Nat
                  /\ Len(front) \in Nat
                BY <4>3, <4>4, LenProperties
            <4>6. /\ DOMAIN stack' = 1..fm
                  /\ \A d \in 1..fm:
                    \/ ~ (d > Len(front))
                    \/ stack[d]' = more[d - Len(front)]
                BY <4>1, <4>3, <4>4, ConcatProperties, LenProperties
                    DEF fm
            <4>7. /\ j \in 1..fm
                  /\ j > Len(front)
                <5>1. r \in 1..Len(more)
                    BY <4>2, <4>3, LenProperties
                <5> QED
                    BY <5>1, <4>5 DEF j, fm
            <4>8. \E n \in 1..fm:
                    /\ n = j
                    /\ stack[n]' = more[n - Len(front)]
                BY <4>6, <4>7
                    (* Tricky point: cannot use `j` in place of `n` here,
                    because the operator `j` is defined as an expression
                    that contains a variable. So it does not necessarily
                    hold that `stack[j]' = more[j - Len(front)]`, due to
                    the priming operator.
                    *)
            <4>9. (j - Len(front)) = r
                BY <4>5, <4>2 DEF j
            <4>10. j \in DOMAIN stack'
                BY <4>6, <4>7
            <4> QED
                BY <4>8, <4>9, <4>10
        <3>9. IsPrefixCov(stack[n]', g)
            <4>1. stack[n]' = more[r]
                BY <3>8
            <4>2. more[r] = PartialCover \cup {enum[r]}
                BY <3>4
            <4>3. stack[n]' = W
                BY <4>1, <4>2 DEF W
            <4>4. stack[n]' = {g[t]:  t \in 1..k}
                BY <4>3, <3>5 DEF k
            <4>5. Cardinality(stack[n]') = k
                BY <4>3, <3>6
            <4> QED
                BY <4>5, <4>4 DEF IsPrefixCov
        <3> QED
            BY <3>8, <3>9
    <2> QED  (* goal from <2>22 *)
        BY <2>25, <2>26

<1>4. ASSUME InvCompl(C) /\ UNCHANGED vars
      PROVE InvCompl(C)'
    BY <1>4 DEF InvCompl, vars
<1>5. ASSUME [TypeInv /\ TypeInv' /\ Next]_vars /\ InvCompl(C)
      PROVE InvCompl(C)'
    BY <1>3, <1>4, <1>5
<1> DEFINE
    Inv == InvCompl(C)
    Nx == TypeInv /\ TypeInv' /\ Next
<1>6. ASSUME Inv /\ [Nx]_vars
      PROVE Inv'
    BY <1>5, <1>6 DEF Inv, Nx, vars, InvCompl
<1> QED
    <2>1. \/ ~ /\ Inv
               /\ [][Nx]_vars
          \/ [] Inv
        BY <1>6, PTL  (* RuleINV1 *)
    <2>2. \/ ~ /\ Init
               /\ [][TypeInv /\ TypeInv' /\ Next]_vars
          \/ [] InvCompl(C)
        BY <1>1, <2>1 DEF Inv, Nx
    <2>3. \/ ~ /\ Init
               /\ []TypeInv
               /\ [][Next]_vars
          \/ [] InvCompl(C)
        BY <2>2, PTL  (* RuleINV2 *)
    <2> QED
        BY <2>3, TypeOK DEF Spec


(* The theorem StackContainsPartialCovers proves that PartialCoversInStack
is an inductive invariant. That PartialCoversInStack is an inductive invariant
is used in the theorem StrongReductionSoundness to prove that InvSound is
an invariant.
*)
THEOREM StackContainsPartialCovers ==
    ASSUME
        NEW C,
        IsAMinCover(Cm, X, Max, Leq)
    PROVE
        Spec => [] PartialCoversInStack
PROOF
<1>3. /\ IsAMinCover(Cm, X, Y, Leq)
      /\ Cm \in SUBSET Y
    <2>1. IsAMinCover(Cm, X, Max, Leq)
        OBVIOUS
    <2> QED
        BY <2>1, MinCoverFromMaxYIsMinCoverFromY,
            MinCoverProperties DEF Max
<1>4. N \in Nat
    BY <1>3, XYAreFiniteSets, FS_Subset, FS_CardinalityType DEF N

<1>1. ASSUME Init
      PROVE PartialCoversInStack
    <2> DEFINE
        Partial == stack[1]
        i == Cardinality(Partial)
        k == i + 1
        Q == Partial \cup Patch(k)
    <2> HIDE DEF Partial, i, k, Q
    <2>1. stack = << {} >>
        BY <1>1 DEF Init
    <2>5. Partial = {}
        BY <2>1 DEF Partial
    <2>2. SUFFICES IsAMinCover(Q, X, Y, Leq)
        BY <2>1, <2>2, <2>5 DEF Q, k, i, Partial, PartialCoversInStack
    <2>3. Q = Patch(1)
        <3>2. k = 1
            BY <2>5, FS_EmptySet DEF i, k
        <3> QED
            BY <2>5, <3>2 DEF Q
    <2>4. Q = Cm
        <3>1. Patch(1) = Image(Lm, 1..N)
            BY <2>3 DEF Patch
        <3>2. Image(Lm, 1..N) = Cm
            BY <1>3, LmIsBijection DEF Image, Bijection, Surjection
        <3> QED
            BY <2>3, <3>1, <3>2
    <2> QED  (* goal from <2>2 *)
        BY <1>3, <2>4

<1>2. ASSUME TypeInv /\ TypeInv' /\ Next /\ PartialCoversInStack
      PROVE PartialCoversInStack'
    <2>1. SUFFICES
            ASSUME
                NEW siNext \in DOMAIN stack'
            PROVE
                LET
                    PartialNext == stack[siNext]'
                    iNext == Cardinality(PartialNext)
                    kNext == iNext + 1
                    QNext == PartialNext \cup Patch(kNext)
                IN
                    /\ IsAMinCover(QNext, X, Y, Leq)
                    /\ PartialNext \cap Patch(kNext) = {}
        BY <2>1 DEF PartialCoversInStack

    <2>6. ASSUME
            NEW si \in DOMAIN stack
          PROVE
            LET
                Partial == stack[si]
                i == Cardinality(Partial)
                k == i + 1
                Q == Partial \cup Patch(k)
            IN
                /\ IsAMinCover(Q, X, Y, Leq)
                /\ Partial \cap Patch(k) = {}
        <3>1. PartialCoversInStack
            BY <1>2
        <3> QED
            BY <3>1, <2>6 DEF PartialCoversInStack

    <2> DEFINE
        end == Len(stack)
        front == SubSeq(stack, 1, end - 1)
        (* Definitions pertaining to PartialCoversInStack. *)
        si == IF siNext < Len(stack) THEN siNext ELSE Len(stack)
        Partial == stack[si]
        i == Cardinality(Partial)
        k == i + 1
        Q == Partial \cup Patch(k)
        (* Definitions pertaining to Expand. *)
        PartialE == stack[end]
        iE == Cardinality(PartialE)
        kE == iE + 1
        ymax == Lm[kE]
        QE == PartialE \cup Patch(kE)
        succ == BelowAndSuff(ymax, QE, Y)
        enum == Enumerate(succ)
        more == [r \in 1..Len(enum) |-> PartialE \cup {enum[r]}]
        (* Definitions pertaining to PartialCoversInStack'. *)
        PartialNext == stack[siNext]'
        iNext == Cardinality(PartialNext)
        kNext == iNext + 1
        QNext == PartialNext \cup Patch(kNext)
    <2> HIDE DEF end, si, Partial, i, k, Q, PartialNext, iNext, kNext, QNext,
        PartialE, ymax, QE, iE, kE, succ, enum, more

    <2>13. /\ stack \in Seq(SUBSET Y)
           /\ stack \in [1..Len(stack) -> SUBSET Y]
           /\ (DOMAIN stack) = (1..Len(stack))
           /\ Len(stack) \in Nat \ {0}  (* so end # 0 *)
        <3>1. stack \in Seq(SUBSET Y)
            BY <1>2 DEF TypeInv
        <3>2. stack # << >>
            BY <1>2 DEF Next
        <3> QED
            BY <3>1, <3>2, LenProperties, EmptySeq
    <2>15. /\ stack' \in Seq(SUBSET Y)
           /\ stack' \in [1..Len(stack') -> SUBSET Y]
           /\ Len(stack') \in Nat
        <3>1. stack' \in Seq(SUBSET Y)
            BY <1>2 DEF TypeInv
        <3> QED
            BY <3>1, LenProperties

    <2>14. /\ siNext \in 1..Len(stack')
           /\ siNext \in Nat
        BY <2>1, <2>15

    <2>16. /\ si \in DOMAIN stack
           /\ si \in 1..Len(stack)

        <3>1. si \in 1..Len(stack)
            <4>1. CASE siNext < Len(stack)
                <5>1. si = siNext
                    BY <4>1 DEF si
                <5>2. /\ si \in 1..Len(stack')
                      /\ si < Len(stack)
                      /\ Len(stack) \in Nat
                    BY <4>1, <5>1, <2>14, <2>13
                <5> QED
                    BY <5>2
            <4>2. CASE ~ (siNext < Len(stack))
                <5>1. si = Len(stack)
                    BY <4>2 DEF si
                <5>2. Len(stack) \in Nat \ {0}
                    BY <2>13
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>2
        <3>2. (DOMAIN stack) = (1..Len(stack))
            BY <2>13
        <3> QED
            BY <3>1, <3>2

    (* Expanding the invariant PartialCoversInStack. *)
    <2>12. /\ IsAMinCover(Q, X, Y, Leq)
           /\ Q \in SUBSET Y
           /\ IsACover(Q, X, Leq)
           /\ IsFiniteSet(Q)
           /\ Cardinality(Q) = N
           /\ Cardinality(Q) \in Nat
        <3>1. IsAMinCover(Q, X, Y, Leq)
            <4>1. PartialCoversInStack
                BY <1>2
            <4>2. si \in DOMAIN stack
                BY <2>16
            <4> QED
                BY <4>1, <4>2, <2>6 DEF PartialCoversInStack,
                    si, Partial, i, k, Q
        <3>2. /\ Q \in SUBSET Y
              /\ IsACover(Q, X, Leq)
            BY <3>1, MinCoverProperties
        <3>3. /\ IsFiniteSet(Q)
              /\ Cardinality(Q) \in Nat
            BY <3>2, XYAreFiniteSets, FS_Subset, FS_CardinalityType
        <3>4. Cardinality(Q) = N
            BY <3>1, <1>3, AllMinCoversSameCard, HaveCardAsCost,
                XYAreFiniteSets, ProblemInput DEF N
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4

    <2>20. /\ front \in Seq(SUBSET Y)
           /\ Len(front) = end - 1
           /\ Len(front) \in Nat
           /\ \A j \in 1..(end - 1):  front[j] = stack[j]
        BY <2>13, FrontProperties, LenProperties DEF Front, front, end

    <2>21. /\ more \in Seq(SUBSET Y)
           /\ Len(more) \in Nat
           /\ DOMAIN more = 1..Len(more)
        <3>1. more \in Seq(SUBSET Y)
            BY <1>2, MoreInSeqSubsetY DEF Next, end, PartialE,
                iE, kE, ymax, QE, succ, enum, more
        <3> QED
            BY <3>1, LenProperties

    (* siNext \in front *)
    <2>7. ASSUME siNext < Len(stack)
          PROVE /\ IsAMinCover(QNext, X, Y, Leq)
                /\ PartialNext \cap Patch(kNext) = {}
        <3>1. si = siNext
            BY <2>7 DEF si
        <3>2. stack[si] = stack[siNext]'
            <4>5. PICK r:  r = si  (* r has constant level, unlike si *)
                OBVIOUS
            <4>1. SUFFICES stack[r] = stack[r]'
                BY <4>1, <3>1, <4>5
            <4>6. r \in 1..(end - 1)
                BY <4>5, <3>1, <2>7, <2>13, <2>16 DEF end
            <4>2. Collect \/ Expand
                BY <1>2 DEF Next
            <4>3. CASE Collect
                <5>1. stack' = front
                    BY <4>3 DEF Collect, front, end
                <5> QED
                    BY <5>1, <4>6, <2>20
            <4>4. CASE Expand
                <5>1. stack[r]' = front[r]
                    <6>1. stack' = front \o more
                        BY <4>4 DEF Expand, front, end,
                            more, enum, succ, ymax, QE, kE, iE, PartialE
                    <6>2. r \in 1..(Len(front) + Len(more))
                        <7>1. r \in 1..Len(front)
                            BY <2>20, <4>6
                        <7>2. ASSUME NEW lf \in Nat, NEW lm \in Nat
                              PROVE 1..lf \subseteq 1..(lf + lm)
                            BY <7>2
                        <7>3. (1..Len(front)) \subseteq
                                (1..(Len(front) + Len(more)))
                            BY <2>20, <2>21, <7>2
                        <7> QED
                            BY <7>1, <7>3
                    <6>3. r <= Len(front)
                        BY <4>6, <2>20
                    <6> QED
                        BY <2>20, <2>21, <6>1, <6>2, <6>3,
                            ConcatProperties
                <5>2. front[r] = stack[r]
                    BY <4>6, <2>20
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>2, <4>3, <4>4
        <3>3. Q = QNext
            BY <3>2 DEF Partial, i, k, Q,
                PartialNext, iNext, kNext, QNext
        <3>4. IsAMinCover(QNext, X, Y, Leq)
            BY <3>3, <2>12
        <3>5. PartialNext \cap Patch(kNext) = {}
            <4>1. Partial \cap Patch(k) = {}
                BY <2>6, <2>16 DEF Partial, k, i
            <4>2. PartialNext = Partial
                BY <3>2 DEF Partial, PartialNext
            <4>3. k = kNext
                BY <4>2 DEF i, k, iNext, kNext
            <4> QED
                BY <4>1, <4>2, <4>3
        <3> QED
            BY <3>4, <3>5

    (* siNext \in more *)
    <2>8. SUFFICES
            ASSUME siNext >= Len(stack)
            PROVE /\ IsAMinCover(QNext, X, Y, Leq)
                  /\ PartialNext \cap Patch(kNext) = {}
        <3>1. siNext \in Nat
            BY <2>15
        <3>2. Len(stack) \in Nat
            BY <2>13
        <3> QED  (* goal from <2>1 *)
            BY <2>7, <2>8, <3>1, <3>2
                DEF QNext, kNext, iNext, PartialNext

    <2>18. si = Len(stack)
        BY <2>8, <2>13, <2>14 DEF si

    <2>17. i \in Nat
        <3>1. stack \in [1..Len(stack) -> SUBSET Y]
            BY <2>13
        <3>2. si \in DOMAIN stack
            BY <2>16
        <3>3. stack[si] \in SUBSET Y
            BY <3>1, <3>2, ElementOfSeq
        <3>4. IsFiniteSet(Y)
            BY XYAreFiniteSets
        <3>5. IsFiniteSet(Partial)
            BY <3>3, <3>4, FS_Subset DEF Partial
        <3> QED
            BY <3>5, FS_CardinalityType DEF i

    <2>19. /\ Collect \/ Expand
           /\ Partial = stack[end]
        <3>1. Collect \/ Expand
            BY <1>2 DEF Next
        <3>2. Partial = stack[end]
            BY <2>18 DEF Partial, end
        <3> QED
            BY <3>1, <3>2

    <2>9. ASSUME i = N
          PROVE FALSE
        <3>1. Collect
            <4>1. ~ (i < N)
                BY <2>9, <2>17, <1>4
            <4> QED
                BY <4>1, <2>19 DEF Expand, i, end
        <3>4. siNext >= end
            BY <2>8 DEF end
        <3>5. siNext \in 1..(end - 1)
            <4>1. stack' = SubSeq(stack, 1, end - 1)
                BY <3>1 DEF Collect, end
            <4>2. 1 \in 1..(end + 1)
                BY <2>13 DEF end
            <4>3. (end - 1) \in ((1 - 1)..end)
                BY <2>13 DEF end
            <4>4. (end - 1) = ((end - 1) - 1 + 1)
                BY <2>13 DEF end
            <4>5. Len(stack') = end - 1
                BY <4>1, <4>2, <4>3, <4>4, <2>13, SubSeqProperties DEF end
            <4> QED
                BY <2>14, <4>5
        <3>6. end \in Nat
            BY <2>13 DEF end
        <3> QED
            BY <3>4, <3>5, <3>6

    <2>10. SUFFICES
            ASSUME i < N
            PROVE /\ IsAMinCover(QNext, X, Y, Leq)
                  /\ PartialNext \cap Patch(kNext) = {}
        <3>1. (i = N) \/ (i < N)
            BY <2>19, <2>18 DEF Collect, Expand, i, Partial
        <3> QED  (* goal from <2>8 *)
            BY <2>9, <2>10, <3>1

    <2>2. SUFFICES /\ QNext \in SUBSET Y
                   /\ IsACover(QNext, X, Leq)
                   /\ Cardinality(QNext) = N
                   /\ PartialNext \cap Patch(kNext) = {}
        <3> HIDE DEF QNext
        <3>1. IsAMinCover(QNext, X, Y, Leq)
            BY <1>3, <1>4, <2>2,
                MinCoverEquivCoverCard, XYAreFiniteSets,
                ProblemInput, HaveCardAsCost DEF N
        <3> QED  (* goal from <2>10 *)
            BY <2>2, <3>1

    <2>11. Expand
        <3>1. ~ (i = N)
            BY <2>10, <2>17, <1>4
        <3> QED
            BY <2>19, <3>1 DEF Collect, i, end

    <2>23. /\ PartialE = Partial
           /\ kE = k
           /\ iE = i
           /\ QE = Q
           /\ ymax = Lm[k]
           /\ k \in 1..N

        <3>1. k \in 1..N
            <4>1. k = i + 1
                BY DEF k
            <4>2. i \in Nat
                BY <2>17
            <4>3. i < N
                BY <2>10
            <4>4. N \in Nat
                BY <1>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4
        <3> QED
            BY <3>1, <2>18 DEF PartialE, Partial, end,
                kE, k, iE, i, QE, Q, ymax

    <2>26. ASSUME
                NEW S \in SUBSET Q, NEW yk,
                /\ yk \in BelowAndSuff(ymax, Q, Y)
                /\ ymax \notin S
           PROVE
                yk \notin S
        <3>9. SUFFICES ASSUME yk \in S
                       PROVE FALSE
            BY <3>9
        <3>7. ymax \notin S
            BY <2>26
        <3>14. PICK x:  x \in Only(ymax, Q)
            <4>1. ymax \in Q
                <5>1. ymax \in Patch(k)
                    BY <2>23, <1>4, <1>3, PatchSplit DEF ymax
                <5> QED
                    BY <5>1 DEF Q
            <4> QED
                BY <2>12, <4>1, MinimalHasAllEssential
        <3>10. \A w \in Q \ {ymax}:  ~ Leq[x, w]
            BY <3>14 DEF Only
        <3>11. yk \in Q \ {ymax}
            <4>1. yk # ymax
                BY <3>9, <3>7
            <4>2. yk \in Q
                BY <3>9, S \subseteq Q
            <4> QED
                BY <4>1, <4>2
        <3>12. ~ Leq[x, yk]
            BY <3>10, <3>11
        <3>13. Leq[x, yk]
            <4>1. yk \in BelowAndSuff(ymax, Q, Y)
                BY <2>26
            <4> QED
                BY <4>1, <3>14 DEF BelowAndSuff, ymax
        <3> QED  (* goal from <3>9 *)
            BY <3>12, <3>13

    <2>22. PICK yk:
            /\ yk \in BelowAndSuff(Lm[k], Q, Y)
            /\ PartialNext = Partial \cup {yk}
            /\ yk \notin Partial

        <3>2. PICK r \in 1..Len(enum):
                PartialNext = PartialE \cup {enum[r]}
            <4>1. stack' = front \o more
                BY <2>11 DEF Expand, front, end,
                    more, enum, succ, ymax, QE, kE, iE, PartialE
            <4>2. /\ front \in Seq(SUBSET Y)
                  /\ more \in Seq(SUBSET Y)
                BY <2>20, <2>21
            <4>8. /\ Len(front) \in Nat
                  /\ Len(more) \in Nat
                  /\ end \in Nat \ {0}
                  /\ siNext \in Nat
                BY <2>20, <2>21, <2>13, <2>14 DEF end
            <4> USE <4>8
            <4>3. siNext \in 1..Len(stack')
                BY <2>14
            <4>4. siNext > Len(front)
                <5>1. Len(front) = end - 1
                    BY <2>20
                <5>2. siNext >= end
                    BY <2>8 DEF end
                <5> QED
                    BY <5>1, <5>2
            <4>5. /\ stack[siNext]' = more[siNext - Len(front)]
                  /\ siNext \in 1..(Len(front) + Len(more))
                <5>1. /\ Len(stack') = Len(front) + Len(more)
                      /\ \A j \in 1..(Len(front) + Len(more)):
                        stack[j]' = IF j <= Len(front)
                            THEN front[j]
                            ELSE more[j - Len(front)]
                    BY <4>1, <4>2, ConcatProperties
                <5>2. /\ siNext \in 1..(Len(front) + Len(more))
                      /\ ~ (siNext <= Len(front))
                    <6>1. ~ (siNext <= Len(front))
                        BY <4>8, <4>4
                    <6>2. siNext \in 1..(Len(front) + Len(more))
                        BY <4>3, <5>1, <4>4, <4>8
                    <6> QED
                        BY <6>1, <6>2
                <5> QED
                    BY <5>1, <5>2
            <4> DEFINE r == siNext - end + 1
            <4>6. r \in 1..Len(enum)
                <5>1. SUFFICES r \in DOMAIN more
                    BY <5>1 DEF more
                <5>2. siNext \in end..(end + Len(more) - 1)
                    <6>1. siNext >= end
                        BY <2>20, <2>8 DEF end
                    <6>2. siNext \in 1..(end - 1 + Len(more))
                        BY <4>5, <2>20
                    <6> QED
                        BY <6>1, <6>2
                <5>3. r \in 1..Len(more)
                    BY <5>2, <4>8 DEF r
                <5> QED
                    BY <5>3, <2>21
            <4>7. more[r] = PartialE \cup {enum[r]}
                BY <4>6 DEF more
            <4>10. stack[siNext]' = more[r]
                BY <4>5, <2>20 DEF r
            <4>9. PartialNext = PartialE \cup {enum[r]}
                BY <4>7, <4>10 DEF PartialNext
            <4> QED
                BY <4>6, <4>9
        <3> DEFINE yk == enum[r]
        <3>3. yk \in BelowAndSuff(Lm[k], Q, Y)
            <4>1. IsFiniteSet(succ)
                BY BelowAndSuffIsFinite, XYAreFiniteSets DEF succ
            <4>2. enum \in Bijection(1..Len(enum), succ)
                BY <4>1, EnumerateProperties DEF enum
            <4>3. r \in DOMAIN enum
                BY <3>2, <4>2 DEF Bijection, Injection
            <4>4. enum[r] \in succ
                BY <4>2, <4>3 DEF Bijection, Injection
            <4> QED
                BY <4>4, <2>23 DEF yk, succ
        <3>4. yk \notin Partial
            <4>2. Partial \cap Patch(k) = {}
                    BY <2>6, <2>16 DEF Partial, k, i
            <4> DEFINE S == Partial
            <4>4. ymax \notin S
                <5>1. ymax \in Patch(k)
                    BY <2>23, <1>4, <1>3, PatchSplit
                <5> QED
                    BY <4>2, <5>1
            <4>5. S \subseteq Q
                BY DEF S, Q
            <4> QED
                BY <4>4, <3>3, <4>5, <2>26, <2>23 DEF S
        <3> QED
            BY <3>2, <3>3, <3>4, <2>23

    <2>25. PartialNext \cap Patch(k + 1) = {}
        <3>1. Partial \cap Patch(k) = {}
            BY <2>6, <2>16 DEF Partial, k, i
        <3>2. PartialNext = Partial \cup {yk}
            BY <2>22
        <3>3. Patch(k) = {ymax} \cup Patch(k + 1)
            BY <2>23, <1>4, <1>3, PatchSplit
        <3>4. Patch(k + 1) \subseteq Patch(k)
            BY <3>3
        <3>5. Partial \cap Patch(k + 1) = {}
            BY <3>1, <3>4
        <3>6. SUFFICES yk \notin Patch(k + 1)
            BY <3>2, <3>5
        <3> QED
            <4> DEFINE S == Patch(k + 1)
            <4>1. ymax \notin S
                BY <1>3, <2>23, PatchSplit DEF S
            <4>2. S \in SUBSET Q
                BY <3>4 DEF S, Q
            <4>3. yk \in BelowAndSuff(ymax, Q, Y)
                BY <2>22, <2>23
            <4> QED  (* goal from <3>6 *)
                BY <4>1, <4>2, <4>3, <2>26

    <2>24. /\ iNext \in Nat
           /\ kNext \in Nat
           /\ k \in Nat
           /\ kNext = k + 1
           /\ IsFiniteSet(PartialNext)
           /\ Cardinality(PartialNext) = k
        <3>1. IsFiniteSet(Partial)
            <4> DEFINE S == DOMAIN stack
            <4>1. Partial = stack[si]
                BY DEF Partial
            <4>2. stack[si] \subseteq Y
                <5>1. si \in S
                    BY <2>16 DEF S
                <5>2. stack \in [S -> SUBSET Y]
                    BY <2>13 DEF S
                <5> QED
                    BY <5>1, <5>2
            <4>3. Partial \subseteq Y
                BY <4>1, <4>2
            <4>4. IsFiniteSet(Y)
                BY XYAreFiniteSets
            <4> QED
                BY <4>3, <4>4, FS_Subset
        <3>2. yk \notin Partial
            BY <2>22
        <3>3. /\ IsFiniteSet(Partial \cup {yk})
              /\ Cardinality(Partial \cup {yk}) = i + 1
            BY <3>1, <3>2, FS_AddElement DEF i
        <3>4. /\ IsFiniteSet(PartialNext)
              /\ Cardinality(PartialNext) = i + 1
            BY <3>3, <2>22
        <3>5. /\ iNext = i + 1
              /\ iNext \in Nat
            BY <3>4, <2>17 DEF iNext
        <3>6. /\ kNext = k + 1
              /\ kNext \in Nat
              /\ k \in Nat
            <4>1. /\ kNext = iNext + 1
                  /\ k = i + 1
                BY DEF kNext, k
            <4> QED
                BY <4>1, <3>5, <2>17
        <3> QED
            BY <3>4, <3>5, <3>6 DEF k

    <2>3. QNext \in SUBSET Y
        <3>1. QNext = PartialNext \cup Patch(kNext)
            BY DEF QNext
        <3>2. PartialNext \in SUBSET Y
            <4>1. PartialNext = Partial \cup {yk}
                BY <2>22
            <4>2. Partial \in SUBSET Y
                <5>1. Partial \subseteq Q
                    BY DEF Q
                <5>2. Q \subseteq Y
                    BY <2>12
                <5> QED
                    BY <5>1, <5>2
            <4>3. yk \in Y
                BY <2>22 DEF BelowAndSuff
            <4> QED
                BY <4>1, <4>2, <4>3
        <3>3. Patch(kNext) \in SUBSET Y
            BY <2>24, <1>3, <1>4, <2>23, PatchProperties
        <3> QED
            BY <3>1, <3>2, <3>3

    <2>4. IsACover(QNext, X, Leq)
        <3>1. SUFFICES
                ASSUME NEW x \in X
                PROVE \E y \in QNext:  Leq[x, y]
            BY <3>1 DEF IsACover
        <3>2. CASE \E y \in Q \ {ymax}:  Leq[x, y]
            <4>1. PICK y \in Q \ {ymax}:  Leq[x, y]
                BY <3>2
            (* If y is an element from Q other than yk,
            then it belongs to the intersection of Q and QNext.
            *)
            <4>2. SUFFICES y \in QNext
                BY <4>1, <4>2
            <4>3. /\ y \in Partial \cup Patch(k)
                  /\ y # ymax
                BY <4>1 DEF Q
            <4>4. Patch(k) = (Patch(kNext) \cup {ymax})
                <5>1. Patch(k) = (Patch(k + 1) \cup {ymax})
                    <6>1. N \in Nat
                        BY <1>4
                    <6>2. k \in 1..N
                        BY <2>23
                    <6>3. ymax = Lm[k]
                        BY <2>23 DEF ymax
                    <6> QED
                        BY <6>1, <6>2, <6>3, <2>23,
                            <1>3, <1>4, PatchSplit
                <5>2. kNext = k + 1
                    BY <2>24
                <5> QED
                    BY <5>1, <5>2
            <4>5. y \in Partial \cup Patch(kNext)
                BY <4>3, <4>4
            <4>6. (Partial \cup Patch(kNext)) \subseteq QNext
                <5>1. PartialNext = Partial \cup {yk}
                    BY <2>22
                <5>2. QNext = PartialNext \cup Patch(kNext)
                    BY DEF QNext
                <5> QED
                    BY <5>1, <5>2
            <4> QED
                BY <4>1, <4>5, <4>6

        <3>3. CASE \A y \in Q \ {ymax}:  ~ Leq[x, y]
            <4>1. SUFFICES Leq[x, yk]  (* goal from <3>1 *)
                <5>1. yk \in QNext
                    <6>1. yk \in PartialNext
                        BY <2>22
                    <6>2. PartialNext \subseteq QNext
                        BY DEF QNext
                    <6> QED
                        BY <6>1, <6>2
                <5> QED
                    BY <4>1, <2>22, <5>1
            (* If x is in the k-th gap, then yk covers it,
            because yk was selected to have this property,
            via BelowAndSuff.
            *)
            <4>2. x \in Only(ymax, Q)
                BY <3>1, <3>3 DEF Only
            <4>3. (* /\ yk \in Y *)
                  (* /\ yk \in Leq[y, ymax] *)
                  \A u \in Only(ymax, Q):  Leq[u, yk]
                <5>1. yk \in BelowAndSuff(ymax, Q, Y)
                    BY <2>22, <2>23 DEF ymax
                <5> QED
                    BY <5>1 DEF BelowAndSuff
            <4> QED  (* goal from <4>1 *)
                BY <4>2, <4>3
        <3> QED  (* goal from <3>1 *)
            BY <3>2, <3>3

    <2>5. Cardinality(QNext) = N
        <3> DEFINE Pc == Patch(kNext)
        <3>8. /\ N \in Nat
              /\ k \in Nat
            BY <1>4, <2>24
        <3>1. QNext = PartialNext \cup Pc
            BY DEF QNext, Pc
        <3>6. Cardinality(QNext) = Cardinality(PartialNext) +
                Cardinality(Pc) - Cardinality(PartialNext \cap Pc)
            <4>1. IsFiniteSet(PartialNext)
                BY <2>24
            <4>2. IsFiniteSet(Pc)
                <5>1. kNext \in 1..(N + 1)
                    BY <2>23, <2>24, <1>4
                <5>2. Cm \in SUBSET Y
                    BY <1>3
                <5> QED
                    BY <5>1, <5>2, PatchProperties DEF Pc
            <4> QED
                BY <3>1, <4>1, <4>2, FS_Union
        <3>2. Cardinality(PartialNext \cap Pc) = 0
            <4>1. PartialNext \cap Pc = {}
                BY <2>25, <2>24 DEF Pc
            <4> QED
                BY <4>1, FS_EmptySet
        <3>3. Cardinality(PartialNext) = k
            BY <2>24
        <3>4. Cardinality(Pc) = N - k
            <4>1. kNext = k + 1
                BY <2>24
            <4>2. Cardinality(Pc) = N - kNext + 1
                <5>1. kNext \in 1..(N + 1)
                    BY <2>23, <2>24, <1>4
                <5>2. Cm \in SUBSET Y
                    BY <1>3
                <5> QED
                    BY <5>1, <5>2, PatchProperties DEF Pc
            <4> QED
                BY <4>1, <4>2, <3>8
        <3> QED
            BY <3>6, <3>2, <3>3, <3>4, <3>8

    <2> QED  (* goal from <2>2 *)
        BY <2>3, <2>4, <2>5, <2>25, <2>24
<1>5. ASSUME PartialCoversInStack /\ UNCHANGED vars
      PROVE PartialCoversInStack'
    BY <1>5 DEF PartialCoversInStack, vars
<1>6. ASSUME [TypeInv /\ TypeInv' /\ Next]_vars /\ PartialCoversInStack
      PROVE PartialCoversInStack'
    BY <1>2, <1>5, <1>6
<1> DEFINE
    Inv == PartialCoversInStack
    Nx == TypeInv /\ TypeInv' /\ Next
<1>7. ASSUME Inv /\ [Nx]_vars
      PROVE Inv'
    BY <1>6, <1>7 DEF Inv, Nx
<1> QED
    <2>1. \/ ~ /\ PartialCoversInStack
               /\ [][TypeInv /\ TypeInv' /\ Next]_vars
          \/ [] PartialCoversInStack
        BY <1>7, PTL DEF Inv, Nx  (* RuleINV1 *)
    <2>2. \/ ~ /\ Init
               /\ [][TypeInv /\ TypeInv' /\ Next]_vars
          \/ [] PartialCoversInStack
        BY <1>1, <2>1
    <2>3. \/ ~ /\ Init
               /\ []TypeInv
               /\ [][Next]_vars
          \/ [] PartialCoversInStack
        BY <2>2, PTL  (* RuleINV2 *)
    <2> QED
        BY <2>3, TypeOK, PTL DEF Spec


(* We now show that:

    MinCoversBelow(Cm) \subseteq MinCoversOf(X, Y, Leq)
*)
THEOREM StrongReductionSoundness ==
    ASSUME
        NEW C,
        IsAMinCover(Cm, X, Max, Leq)
    PROVE
        Spec => [] InvSound(C)
PROOF
<1>1. ASSUME Init
      PROVE InvSound(C)
    <2>1. MinCoversBelow = {}
        BY <1>1 DEF Init
    <2> QED
        BY <2>1 DEF InvSound
<1>2. ASSUME TypeInv /\ PartialCoversInStack /\ Next /\ InvSound(C)
      PROVE InvSound(C)'
    <2>1. /\ stack # << >>
          /\ Collect \/ Expand
        BY <1>2 DEF Next
    <2>2. CASE Expand
        BY <1>2, <2>2 DEF Expand, InvSound
    <2>3. CASE Collect
        <3>5. SUFFICES ASSUME C \in MinCoversBelow'
                       PROVE IsAMinCover(C, X, Y, Leq)
            BY <3>5 DEF InvSound
        <3> DEFINE
            end == Len(stack)
            Partial == stack[end]
            i == Cardinality(Partial)
            k == i + 1
            Q == Partial \cup Patch(k)
        <3>8. end \in DOMAIN stack
            <4>4. stack \in Seq(SUBSET Y)
                BY <1>2 DEF TypeInv
            <4>1. /\ Len(stack) \in Nat
                  /\ DOMAIN stack = 1..Len(stack)
                BY <4>4, LenProperties
            <4>2. /\ end \in Nat
                  /\ end \in 1..end
                BY <4>1, <2>1, <4>4, EmptySeq DEF end
            <4>3. end \in 1..Len(stack)
                BY <4>2 DEF end
            <4> QED
                BY <4>1, <4>3
        <3>7. /\ i \in Nat
              /\ k \in Nat
              /\ N \in Nat
            <4>1. stack \in Seq(SUBSET Y)
                BY <1>2 DEF TypeInv
            <4>2. Partial \in SUBSET Y
                BY <4>1, <3>8, LenProperties DEF Partial
            <4>3. IsFiniteSet(Partial)
                BY <4>2, SubsetYFinite
            <4>4. i \in Nat
                BY <4>3, FS_CardinalityType DEF i
            <4>5. k \in Nat
                BY <4>4 DEF k
            <4>6. N \in Nat
                BY MinCoverFromMaxYIsMinCoverFromY,
                    MinCoverProperties, NType
            <4> QED
                BY <4>4, <4>5, <4>6
        <3>1. /\ i = N
              /\ MinCoversBelow' = MinCoversBelow \cup {Partial}
            BY <2>3 DEF Collect, i, Partial, end
        <3>2. IsAMinCover(Q, X, Y, Leq)
            BY <3>8, <1>2 DEF PartialCoversInStack,
                Q, Partial, end, k, i
        <3>3. Q = Partial
            <4>1. k = N + 1
                BY <3>7, <3>1 DEF k
            <4>2. Patch(k) = {}
                BY <4>1, <3>7 DEF Patch, Image
            <4> QED
                BY <4>2 DEF Q
        <3>4. CASE C \in MinCoversBelow
            BY <1>2, <3>4 DEF InvSound
        <3>6. CASE C \notin MinCoversBelow
            <4>1. C = Partial
                BY <3>6, <3>5, <3>1
            <4> QED
                BY <4>1, <3>3, <3>2
        <3> QED
            BY <3>4, <3>6
    <2> QED
        BY <2>1, <2>2, <2>3
<1>3. ASSUME [TypeInv /\ PartialCoversInStack /\ Next]_vars /\ InvSound(C)
      PROVE InvSound(C)'
    BY <1>2, <1>3 DEF InvSound, vars
<1> DEFINE
    Inv == InvSound(C)
    Nxt == TypeInv /\ PartialCoversInStack /\ Next
<1>4. ASSUME Inv /\ [Nxt]_vars
      PROVE Inv'
    BY <1>3, <1>4 DEF Inv, Nxt, InvSound, vars
<1> QED
    <2>4. (Inv /\ [][Nxt]_vars)  =>  []Inv
        BY <1>4, PTL  (* RuleINV1 *)
    <2>1. \/ ~ /\ InvSound(C)
               /\ [][TypeInv /\ PartialCoversInStack /\ Next]_vars
          \/ []InvSound(C)
        BY <2>4 DEF Inv, Nxt
    <2>2. \/ ~ /\ Init
               /\ [][TypeInv /\ PartialCoversInStack /\ Next]_vars
          \/ []InvSound(C)
        BY <1>1, <2>1
    <2>3. \/ ~ /\ Init
               /\ []TypeInv
               /\ []PartialCoversInStack
               /\ [][Next]_vars
          \/ []InvSound(C)
        BY <2>2, PTL  (* RuleINV2 *)
    <2> QED
        BY <2>3, StackContainsPartialCovers, TypeOK, PTL DEF Spec

--------------------------------------------------------------------------------

THEOREM StrongReductionSafety ==
    ASSUME
        NEW C,
        IsAMinCover(Cm, X, Max, Leq)
    PROVE
        /\ Spec => [] InvSound(C)
        /\ (C \in AllCandidatesBelow(Cm, Y))
            => (Spec => [] InvCompl(C))
PROOF
<1>1. ASSUME C \in AllCandidatesBelow(Cm, Y)
      PROVE C \in SUBSET Y
    BY <1>1 DEF AllCandidatesBelow
<1> QED
    BY <1>1, StrongReductionSoundness, StrongReductionCompleteness

================================================================================
(* Proofs checked with TLAPS version 1.4.3 *)
