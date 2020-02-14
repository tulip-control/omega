------------------------------- MODULE Lattices --------------------------------
(* Operations for minimal covering within a lattice, and theorems about them.

- bounds, Supremum, Infimum, sets of elements above and below
- Floor, Feil, Floors, Ceilings, MaxFloors, MaxCeilings
- quasiorder, partial order, lattice, complete lattice
- some reverse operations: Hat, MaxHat, unfloor
- properties of the above

The results from this module form the basis for proving correct the algorithm
in the module `CyclicCore.tla` .

Author:  Ioannis Filippidis


References
==========

[1] Olivier Coudert
    "Two-level logic minimization: An overview"
    Integration, the VLSI Journal
    Vol.17, No.2, Oct 1994, pp. 97--140
    10.1016/0167-9260(94)00007-7

--------------------------------------------------------------------------------
Copyright 2017 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
*)
EXTENDS
    FiniteSetFacts,
    MinCover,
    Optimization


ThoseUnder(X, y, Leq) == { x \in X:  Leq[x, y] }
ThoseOver(Y, x, Leq) == { y \in Y:  Leq[x, y] }
Umbrella(x, X, Y, Leq) == UNION {
    ThoseUnder(X, y, Leq):  y \in ThoseOver(Y, x, Leq) }

IsBelow(r, S, Leq) == \A u \in S:  Leq[r, u]
IsAbove(r, S, Leq) == \A u \in S:  Leq[u, r]
IsTightBound(r, S, Leq) ==
    LET
        Z == Support(Leq)
    IN
        /\ r \in Z
        /\ IsAbove(r, S, Leq)
        /\ \A q \in Z:  IsAbove(q, S, Leq) => Leq[r, q]

HasTightBound(S, Leq) ==
    LET Z == Support(Leq)
    IN \E r \in Z:  IsTightBound(r, S, Leq)

TightBound(S, Leq) ==
    LET Z == Support(Leq)
    IN CHOOSE r \in Z:  IsTightBound(r, S, Leq)

UpsideDown(Leq) ==
    LET Z == Support(Leq)
    IN [t \in Z \X Z |-> Leq[t[2], t[1]]]

HasSup(S, Leq) == HasTightBound(S, Leq)
HasInf(S, Leq) == LET Geq == UpsideDown(Leq)
                  IN HasTightBound(S, Geq)

Supremum(S, Leq) == TightBound(S, Leq)
Infimum(S, Leq) == LET Geq == UpsideDown(Leq)
                   IN TightBound(S, Geq)

Floor(y, X, Leq) == Supremum(ThoseUnder(X, y, Leq), Leq)
Ceil(x, Y, Leq) == Infimum(ThoseOver(Y, x, Leq), Leq)

Floors(S, X, Leq) == { Floor(y, X, Leq):  y \in S }
Ceilings(S, Y, Leq) == { Ceil(x, Y, Leq):  x \in S }

(* In Coudert's terminology:

1. \max\tau_X or "column reduction" the operator `MaxFloors`
2. \max\tau_Y or "row reduction" the operator `MaxCeilings`.
*)
MaxFloors(S, X, Leq) == Maxima(Floors(S, X, Leq), Leq)
MaxCeilings(S, Y, Leq) == Maxima(Ceilings(S, Y, Leq), Leq)

(* A quasiorder is also known as a preorder. *)
IsAQuasiOrder(R) == /\ IsReflexive(R) /\ IsTransitive(R)
                    /\ IsAFunction(R) /\ \E S:  S \X S = DOMAIN R

IsAPartialOrder(R) ==
    /\ IsReflexive(R) /\ IsTransitive(R) /\ IsAntiSymmetric(R)
    /\ IsAFunction(R) /\ \E S:  S \X S = DOMAIN R

IsAStrictPartialOrder(R) ==
    /\ IsIrreflexive(R) /\ IsTransitive(R) /\ IsAntiSymmetric(R)
    /\ IsAFunction(R) /\ \E S:  S \X S = DOMAIN R

IsAnEquivalenceRelation(R) ==
    /\ IsReflexive(R) /\ IsTransitive(R) /\ IsSymmetric(R)
    /\ IsAFunction(R) /\ \E S:  S \X S = DOMAIN R

IsALattice(R) ==
    /\ IsAPartialOrder(R)
    /\ LET Z == Support(R)
       IN \A S \in SUBSET Z:  \/ Cardinality(S) # 2
                              \/ HasInf(S, R) /\ HasSup(S, R)

IsACompleteLattice(R) ==
    /\ IsAPartialOrder(R)
    /\ LET Z == Support(R)
       IN \A S \in SUBSET Z:  HasInf(S, R) /\ HasSup(S, R)

SomeAbove(u, Y, Leq) == CHOOSE r \in Y:  Leq[u, r]
(* `SomeMaxAbove(u, Y, Leq) = SomeAbove(u, Maxima(Y, Leq), Leq)` *)
SomeMaxAbove(u, Y, Leq) == CHOOSE m \in Maxima(Y, Leq):  Leq[u, m]
Hat(S, Y, Leq) == { SomeAbove(y, Y, Leq):  y \in S }
IsAHat(H, C, Y, Leq) ==
    /\ H \in SUBSET Y
    /\ Refines(C, H, Leq)
    /\ Cardinality(H) <= Cardinality(C)
(* `MaxHat(S, Y, Leq) = Hat(S, Maxima(Y, Leq), Leq)` *)
MaxHat(S, Y, Leq) == { SomeMaxAbove(y, Y, Leq):  y \in S }

SomeUnfloor(u, X, Y, Leq) == CHOOSE y \in Y:  u = Floor(y, X, Leq)
Unfloors(S, X, Y, Leq) == { SomeUnfloor(y, X, Y, Leq):  y \in S }
(* `Unfloors` satisfies `IsUnfloor`, but we use `IsUnfloor` to prove
theorems in order to be able to replace `Unfloors` with the more
concrete and computationally simpler `Hat` when `F` is an antichain.
*)
IsUnfloor(C, F, X, Leq) == /\ F = Floors(C, X, Leq)
                           /\ Cardinality(C) <= Cardinality(F)

--------------------------------------------------------------------------------
(* Properties of lattices. *)


THEOREM LatticeProperties ==
    ASSUME
        NEW Leq, IsACompleteLattice(Leq)
    PROVE
        /\ IsReflexive(Leq)
        /\ IsTransitive(Leq)
        /\ IsAntiSymmetric(Leq)
        /\ IsAFunction(Leq)
        /\ \E S:  S \X S = DOMAIN Leq
        /\ LET Z == Support(Leq)
           IN \A S \in SUBSET Z:  HasInf(S, Leq) /\ HasSup(S, Leq)
    PROOF
    BY DEF IsACompleteLattice, IsAPartialOrder


THEOREM SupIsUnique ==
    ASSUME
        NEW Leq, NEW S,
        S \subseteq Support(Leq),
        IsACompleteLattice(Leq)
    PROVE
        LET Z == Support(Leq)
        IN \A u, v \in Z:
            (IsTightBound(u, S, Leq) /\ IsTightBound(v, S, Leq))
            => (u = v)
    PROOF
    BY DEF IsTightBound, IsACompleteLattice, IsAPartialOrder, IsAntiSymmetric


THEOREM SupExists ==
    ASSUME
        NEW Leq, NEW S,
        /\ IsACompleteLattice(Leq)
        /\ S \subseteq Support(Leq)
    PROVE
        LET
            Z == Support(Leq)
            r == Supremum(S, Leq)
        IN
            /\ r \in Z
            /\ IsAbove(r, S, Leq)
            /\ \A q \in Z:  IsAbove(q, S, Leq) => Leq[r, q]
    PROOF
    BY DEF IsACompleteLattice, Supremum, HasSup,
        HasTightBound, TightBound, IsTightBound


THEOREM InfExists ==
    ASSUME
        NEW Leq, NEW S,
        IsACompleteLattice(Leq),
        S \subseteq Support(Leq)
    PROVE
        LET
            Z == Support(Leq)
            r == Infimum(S, Leq)
        IN
            /\ r \in Z
            /\ IsBelow(r, S, Leq)
            /\ \A q \in Z:  IsBelow(q, S, Leq) => Leq[q, r]
    PROOF OMITTED


THEOREM SupIsMonotonic ==
    ASSUME
        NEW Leq, NEW A, NEW B,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN /\ A \subseteq B
           /\ B \subseteq Z
    PROVE
        LET
            a == Supremum(A, Leq)
            b == Supremum(B, Leq)
        IN
            Leq[a, b]
    PROOF OMITTED


THEOREM SupOfRefinement ==
    ASSUME
        NEW Leq, NEW A, NEW B,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN /\ A \subseteq Z
           /\ B \subseteq Z,
        \A u \in A:  \E v \in B:  Leq[u, v]
    PROVE
        LET
            a == Supremum(A, Leq)
            b == Supremum(B, Leq)
        IN
            Leq[a, b]
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        a == Supremum(A, Leq)
        b == Supremum(B, Leq)
    <1>2. /\ a \in Z
          /\ IsAbove(a, A, Leq)
          /\ \A q \in Z:  IsAbove(q, A, Leq) => Leq[a, q]
        BY SupExists
    <1>3. /\ b \in Z
          /\ IsAbove(b, B, Leq)
          /\ \A q \in Z:  IsAbove(q, B, Leq) => Leq[b, q]
        BY SupExists
    <1>4. IsAbove(b, A, Leq)
        <2>1. SUFFICES ASSUME NEW u \in A
                       PROVE Leq[u, b]
            BY DEF IsAbove
        <2> DEFINE v == CHOOSE r \in B:  Leq[u, r]
        <2>2. Leq[u, v]
            OBVIOUS
        <2>3. Leq[v, b]
            BY <1>3 DEF IsAbove
        <2> QED
            <3>1. IsTransitive(Leq)
                BY DEF IsACompleteLattice, IsAPartialOrder
            <3>2. (u \in Z) /\ (v \in Z) /\ (b \in Z)
                BY <1>3
            <3> QED
                BY <2>2, <2>3, <3>1, <3>2 DEF IsTransitive
    <1> QED
        BY <1>2, <1>3, <1>4


LEMMA PartialOrderHasSymmetricDomain ==
    ASSUME
        NEW Leq,
        IsAPartialOrder(Leq)
    PROVE
        LET Z == Support(Leq)
        IN (DOMAIN Leq) = (Z \X Z)
    PROOF
    <1> DEFINE Z == Support(Leq)
    <1>1. PICK S:  (DOMAIN Leq) = (S \X S)
        BY DEF IsAPartialOrder
    <1>2. SUFFICES Z = S
        BY <1>1
    <1>3. Z \subseteq S
        BY <1>1 DEF Support
    <1>4. S \subseteq Z
        <3> SUFFICES ASSUME NEW u \in S
                     PROVE u \in Z
            OBVIOUS
        <3> QED
            BY <1>1 DEF Support
    <1> QED
        BY <1>3, <1>4


COROLLARY LatticeHasSymmetricDomain ==
    ASSUME
        NEW Leq,
        IsACompleteLattice(Leq)
    PROVE
        LET Z == Support(Leq)
        IN (DOMAIN Leq) = (Z \X Z)
    PROOF
    BY PartialOrderHasSymmetricDomain DEF IsACompleteLattice

--------------------------------------------------------------------------------
(* Properties of `Floor`. *)


(* `SupExists` for `Floor`. *)
PROPOSITION FloorExists ==
    ASSUME
        NEW Leq, NEW X, NEW y,
        LET
            Z == Support(Leq)
        IN
            /\ IsACompleteLattice(Leq)
            /\ X \subseteq Z
    PROVE
        LET
            Z == Support(Leq)
            U == ThoseUnder(X, y, Leq)
            f == Floor(y, X, Leq)
        IN
            /\ f \in Z
            /\ IsAbove(f, U, Leq)
            /\ \A q \in Z:  IsAbove(q, U, Leq) => Leq[f, q]
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        U == ThoseUnder(X, y, Leq)
        f == Floor(y, X, Leq)
    <1>1. U \subseteq Z
        BY DEF ThoseUnder
    <1>2. f = Supremum(U, Leq)
        BY DEF Floor
    <1> QED
        BY <1>1, <1>2, SupExists


COROLLARY FloorsIsSubset ==
    ASSUME
        NEW Leq, NEW X, NEW S,
        LET
            Z == Support(Leq)
        IN
            /\ X \subseteq Z
            /\ S \subseteq Z
            /\ IsACompleteLattice(Leq)
    PROVE
        LET Z == Support(Leq)
        IN Floors(S, X, Leq) \subseteq Z
    PROOF
    BY FloorExists DEF Floors


(* If `u` is below `y`, then `u` is below `Floor(y, X, Leq)`. *)
PROPOSITION FloorIsAboveThoseUnder ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW y, NEW u \in X,
        LET
            Z == Support(Leq)
        IN
            /\ X \subseteq Z
            /\ IsACompleteLattice(Leq)
            /\ Leq[u, y]
    PROVE
        LET fy == Floor(y, X, Leq)
        IN Leq[u, fy]
    PROOF
    <1> DEFINE
        U == ThoseUnder(X, y, Leq)
        fy == Floor(y, X, Leq)
    <1>1. u \in U
        BY DEF ThoseUnder
    <1>2. U \subseteq X
        BY DEF ThoseUnder
    <1>3. fy = Supremum(U, Leq)
        BY DEF Floor
    <1> QED
        BY <1>1, <1>2, <1>3, SupExists DEF IsAbove


THEOREM FloorIsMonotonic ==
    ASSUME
        NEW Leq, NEW X, NEW u, NEW v,
        IsACompleteLattice(Leq),
        LET
            Z == Support(Leq)
        IN
            /\ u \in Z
            /\ v \in Z
            /\ Leq[u, v]
            /\ X \subseteq Z
    PROVE
        LET
            a == Floor(u, X, Leq)
            b == Floor(v, X, Leq)
        IN
            Leq[a, b]
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        A == ThoseUnder(X, u, Leq)
        B == ThoseUnder(X, v, Leq)
        a == Floor(u, X, Leq)
        b == Floor(v, X, Leq)
    <1>2. /\ a = Supremum(A, Leq)
          /\ b = Supremum(B, Leq)
        BY DEF Floor
    <1>3. A \subseteq B
        BY LatticeProperties DEF IsTransitive, ThoseUnder
    <1>4. B \subseteq Z
        <2>1. B \subseteq X
            BY DEF ThoseUnder
        <2> QED
            BY <2>1
    <1> QED
        BY <1>2, <1>3, <1>4, SupIsMonotonic


THEOREM FloorIsSmaller ==
    ASSUME
        NEW Leq, NEW X, NEW y,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN /\ y \in Z
           /\ X \subseteq Z
    PROVE
        LET r == Floor(y, X, Leq)
        IN Leq[r, y]
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        r == Floor(y, X, Leq)
        S == ThoseUnder(X, y, Leq)
    <1>2. r = Supremum(S, Leq)
        BY DEF Floor
    <1>3. \A q \in Z:  IsAbove(q, S, Leq) => Leq[r, q]
        <2>1. HasSup(S, Leq)
            BY DEF IsACompleteLattice, ThoseUnder
        <2>2. \E u \in Z:  IsTightBound(u, S, Leq)
            BY <2>1 DEF HasSup, HasTightBound
        <2> QED
            BY <1>2, <2>2 DEF Supremum, TightBound, IsTightBound
    <1>4. IsAbove(y, S, Leq)
        BY DEF ThoseUnder, IsAbove
    <1> QED
        BY <1>3, <1>4


PROPOSITION FloorIsIdempotent ==
    ASSUME
        NEW Leq, NEW X, NEW v,
        LET
            Z == Support(Leq)
        IN
            /\ IsACompleteLattice(Leq)
            /\ X \subseteq Z
            /\ v \in Z
            /\ \E y \in Z:  v = Floor(y, X, Leq)
    PROVE
        v = Floor(v, X, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
    <1>1. PICK y \in Z:  v = Floor(y, X, Leq)
        OBVIOUS
    <1> DEFINE
        Bv == ThoseUnder(X, v, Leq)
        By == ThoseUnder(X, y, Leq)
        fv == Floor(v, X, Leq)
        fy == Floor(y, X, Leq)
    <1>2. /\ fv = Supremum(Bv, Leq)
          /\ fy = Supremum(By, Leq)
        BY DEF Floor
    <1>3. v = fy
        BY <1>1
    <1>4. SUFFICES fv = fy
        BY <1>3
    <1>5. SUFFICES Bv = By
        BY <1>2
    <1>6. By \subseteq Bv
        BY <1>3, FloorIsAboveThoseUnder DEF ThoseUnder
    <1>7. Bv \subseteq By
        <2>1. SUFFICES ASSUME NEW u \in Bv
                       PROVE u \in By
            OBVIOUS
        <2>2. Leq[u, v]
            BY <2>1 DEF ThoseUnder
        <2>3. Leq[v, y]
            BY <1>3, FloorIsSmaller
        <2>4. Leq[u, y]
            <3>1. IsTransitive(Leq)
                BY LatticeProperties
            <3>2. u \in Z /\ v \in Z /\ y \in Z
                <4>1. Bv \subseteq Z
                    BY DEF ThoseUnder
                <4>2. u \in Z
                    BY <2>1, <4>1
                <4> QED
                    BY <4>2, <1>1
            <3>3. Leq[u, v] /\ Leq[v, y]
                BY <2>2, <2>3
            <3> QED
                BY <3>1, <3>2, <3>3 DEF IsTransitive
        <2> QED
            BY <2>4 DEF ThoseUnder
    <1> QED
        BY <1>6, <1>7


THEOREM FloorsSmaller ==
    ASSUME
        NEW X, NEW Y, NEW Leq,
        IsFiniteSet(Y)
    PROVE
        LET
            R == Floors(Y, X, Leq)
        IN
            /\ IsFiniteSet(R)
            /\ Cardinality(R) <= Cardinality(Y)
    PROOF
    BY ImageOfFinite DEF Floors


THEOREM MaxFloorSmaller ==
    ASSUME
        NEW X, NEW Y, NEW Leq,
        IsFiniteSet(Y)
    PROVE
        LET
            R == MaxFloors(Y, X, Leq)
            T == Floors(Y, X, Leq)
        IN
            /\ R \subseteq T
            /\ IsFiniteSet(R) /\ IsFiniteSet(T)
            /\ Cardinality(R) <= Cardinality(T)
            /\ Cardinality(T) <= Cardinality(Y)
    PROOF
    <1> DEFINE
        R == MaxFloors(Y, X, Leq)
        T == Floors(Y, X, Leq)
    <1>1. R = Maxima(T, Leq)
        BY DEF MaxFloors
    <1>2. R \subseteq T
        BY <1>1, MaxIsSubset
    <1>3. /\ IsFiniteSet(T)
          /\ Cardinality(T) <= Cardinality(Y)
        BY ImageOfFinite DEF Floors
    <1>4. /\ IsFiniteSet(R)
          /\ Cardinality(R) <= Cardinality(T)
        BY <1>2, <1>3, FS_Subset
    <1> QED
        BY <1>2, <1>3, <1>4, FS_CardinalityType

--------------------------------------------------------------------------------
(* `Geq` properties. *)


THEOREM UpsideDownHasSameSupport ==
    ASSUME
        NEW Leq
    PROVE
        LET
            Geq == UpsideDown(Leq)
        IN Support(Geq) = Support(Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Geq == UpsideDown(Leq)
    <1>1. Geq = [t \in Z \X Z |-> Leq[t[2], t[1]]]
        BY DEF UpsideDown
    <1>2. Support(Geq) \subseteq Z
        <2>1. DOMAIN Geq = Z \X Z
            BY <1>1
        <2> QED
            BY <2>1 DEF Support
    <1>3. Z \subseteq Support(Geq)
        <3>1. \A u \in Z:  \E p \in DOMAIN Geq:  p[1] = u
            BY <1>1
        <3>2. Z \subseteq { p[1]:  p \in DOMAIN Geq }
            BY <3>1
        <3> QED
            BY <3>2 DEF Support
    <1> QED
        BY <1>2, <1>3


LEMMA LeqSwapOfGeq ==
    ASSUME
        NEW Leq
    PROVE
        LET
            Geq == UpsideDown(Leq)
            Z == Support(Leq)
            W == Support(Geq)
        IN
            /\ W = Z
            /\ \A u, v \in W:  Geq[u, v] = Leq[v, u]
    PROOF
    <1> DEFINE
        Geq == UpsideDown(Leq)
        Z == Support(Leq)
        W == Support(Geq)
    <1> W = Z
        BY UpsideDownHasSameSupport
    <1> SUFFICES ASSUME NEW u \in W, NEW v \in W
                 PROVE Geq[u, v] = Leq[v, u]
        OBVIOUS
    <1>1. << u, v >> \in Z \X Z
        OBVIOUS
    <1> QED
        BY <1>1 DEF UpsideDown


THEOREM SwapPreservesOrderProperties ==
    ASSUME
        NEW Leq
    PROVE
        LET
            Z == Support(Leq)
            Geq == UpsideDown(Leq)
        IN
            /\ IsReflexive(Leq) => IsReflexive(Geq)
            /\ IsTransitive(Leq) => IsTransitive(Geq)
            /\ IsAntiSymmetric(Leq) => IsAntiSymmetric(Geq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Geq == UpsideDown(Leq)
        W == Support(Geq)
    <1>1. Geq = [t \in Z \X Z |-> Leq[t[2], t[1]]]
        BY DEF UpsideDown
    <1>2. W = Z
        BY UpsideDownHasSameSupport
    <1>3. ASSUME IsReflexive(Leq)
          PROVE IsReflexive(Geq)
        <2>1. SUFFICES ASSUME NEW x \in W
                       PROVE Geq[x, x]
            BY DEF IsReflexive
        <2>2. x \in Z
            BY <1>2
        <2>3. Leq[x, x]
            BY <1>3, <2>2 DEF IsReflexive
        <2>4. << x, x >> \in Z \X Z
            BY <2>2
        <2>5. Geq[ << x, x >> ] = Leq[ << x, x >> ]
            BY <1>1, <2>4
        <2> QED
            BY <2>3, <2>5
    <1>4. ASSUME IsTransitive(Leq)
          PROVE IsTransitive(Geq)
        <2>1. \A x, y, z \in Z:  (Leq[x, y] /\ Leq[y, z]) => Leq[x, z]
            BY <1>4 DEF IsTransitive
        <2>2. \A x, y, z \in Z:  (Geq[y, x] /\ Geq[z, y]) => Geq[z, x]
            BY <2>1, <1>1
        <2> QED
            BY <1>2, <2>2 DEF IsTransitive
    <1>5. ASSUME IsAntiSymmetric(Leq)
          PROVE IsAntiSymmetric(Geq)
        <2>1. SUFFICES ASSUME NEW x \in W, NEW y \in W,
                              Geq[x, y] /\ (x # y)
                       PROVE ~ Geq[y, x]
            BY DEF IsAntiSymmetric
        <2>2. x \in Z /\ y \in Z
            BY <2>1, <1>2
        <2>3. << x, y >> \in Z \X Z
            BY <2>2
        <2>4. Leq[y, x]
            BY <2>1, <1>1, <2>3
        <2>5. ~ Leq[x, y]
            BY <2>4, <1>5, <2>2, <2>1 DEF IsAntiSymmetric
        <2> QED
            <3>1. << y, x >> \in Z \X Z
                BY <2>2
            <3> QED
                BY <1>1, <3>1, <2>5
    <1> QED
        BY <1>3, <1>4, <1>5


THEOREM UpsideDownIsLattice ==
    ASSUME
        NEW Leq,
        IsACompleteLattice(Leq)
    PROVE
        LET Geq == UpsideDown(Leq)
        IN IsACompleteLattice(Geq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Geq == UpsideDown(Leq)
        W == Support(Geq)
    <1>1. Geq = [t \in Z \X Z |-> Leq[t[2], t[1]]]
        BY DEF UpsideDown
    <1>2. Support(Geq) = Z
        BY UpsideDownHasSameSupport
    <1>3. DOMAIN Leq = Z \X Z
        BY LatticeHasSymmetricDomain
    <1>4. IsReflexive(Geq) /\ IsTransitive(Geq) /\ IsAntiSymmetric(Geq)
        <2>1. IsReflexive(Leq) /\ IsTransitive(Leq) /\ IsAntiSymmetric(Leq)
            BY DEF IsACompleteLattice, IsAPartialOrder
        <2> QED
            BY <2>1, SwapPreservesOrderProperties
    <1>5. IsAPartialOrder(Geq)
        <2>1. IsAFunction(Geq)
            BY <1>1 DEF IsAFunction
        <2>2. DOMAIN Geq = Z \X Z
            BY <1>1
        <2> QED
            BY <2>1, <2>2, <1>4 DEF IsAPartialOrder
    <1>6. ASSUME NEW S \in SUBSET Z
          PROVE HasInf(S, Geq) /\ HasSup(S, Geq)
        <2>1. HasSup(S, Geq)
            <3>1. HasInf(S, Leq)
                BY DEF IsACompleteLattice
            <3> QED
                BY <3>1 DEF HasInf, HasSup
        <2>2. HasInf(S, Geq)
            <3>1. HasSup(S, Leq)
                BY DEF IsACompleteLattice
            <3>2. Leq = UpsideDown(Geq)
                <4>1. IsAFunction(Leq)
                    BY DEF IsACompleteLattice, IsAPartialOrder
                <4>2. UpsideDown(Geq) = [t \in Z \X Z |-> Geq[t[2], t[1]] ]
                    BY <1>2 DEF UpsideDown
                <4>3. \A t \in Z \X Z:  Geq[t[2], t[1]] = Leq[t[1], t[2] ]
                    <5> HIDE DEF Geq
                    <5> SUFFICES ASSUME NEW t \in Z \X Z
                                 PROVE Geq[t[2], t[1]] = Leq[t[1], t[2]]
                        OBVIOUS
                    <5>1. << t[2], t[1] >> \in Z \X Z
                        OBVIOUS
                    <5> QED
                        BY <5>1, <1>1
                <4>4. UpsideDown(Geq) = [t \in Z \X Z |-> Leq[t[1], t[2]] ]
                    BY <4>3, <4>2
                <4>5. UpsideDown(Geq) = [t \in Z \X Z |-> Leq[t] ]
                    BY <4>4
                <4>6. Leq = [t \in Z \X Z |-> Leq[t]]
                    BY <1>3, <4>1 DEF IsAFunction
                <4> QED
                    BY <4>5, <4>6
            <3> QED
                BY <3>1, <3>2 DEF HasSup, HasInf
        <2> QED
            BY <2>1, <2>2
    <1> QED
        BY <1>2, <1>5, <1>6 DEF IsACompleteLattice

--------------------------------------------------------------------------------
(* `Ceil` properties. *)


PROPOSITION CeilExists ==
    ASSUME
        NEW Leq, NEW Y, NEW x,
        LET
            Z == Support(Leq)
        IN
            /\ IsACompleteLattice(Leq)
            /\ Y \subseteq Z
    PROVE
        LET
            Z == Support(Leq)
            V == ThoseOver(Y, x, Leq)
            c == Ceil(x, Y, Leq)
        IN
            /\ c \in Z
            /\ IsBelow(c, V, Leq)
            /\ \A q \in Z:  IsBelow(q, V, Leq) => Leq[c, q]
    PROOF OMITTED  (* For symmetric reasons as FloorExists. *)


COROLLARY CeilingsIsSubset ==
    ASSUME
        NEW Leq, NEW Y, NEW S,
        LET
            Z == Support(Leq)
        IN
            /\ Y \subseteq Z
            /\ S \subseteq Z
            /\ IsACompleteLattice(Leq)
    PROVE
        LET Z == Support(Leq)
        IN Ceilings(S, Y, Leq) \subseteq Z
    PROOF
    BY CeilExists DEF Ceilings


PROPOSITION CeilIsBelowThoseOver ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW x, NEW v \in Y,
        LET
            Z == Support(Leq)
        IN
            /\ Y \subseteq Z
            /\ IsACompleteLattice(Leq)
            /\ Leq[x, v]
    PROVE
        LET C == Ceil(x, Y, Leq)
        IN Leq[C, v]
    PROOF
    <1> DEFINE
        T == ThoseOver(Y, x, Leq)
        C == Ceil(x, Y, Leq)
    <1>1. v \in T
        BY DEF ThoseOver
    <1>2. T \subseteq Y
        BY DEF ThoseOver
    <1>3. C = Infimum(T, Leq)
        BY DEF Ceil
    <1> QED
        BY <1>1, <1>2, <1>3, InfExists DEF IsBelow


THEOREM CeilIsLarger ==
    ASSUME
        NEW Leq, NEW Y, NEW x,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN /\ x \in Z
           /\ Y \subseteq Z
    PROVE
        LET r == Ceil(x, Y, Leq)
        IN Leq[x, r]
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        r == Ceil(x, Y, Leq)
        Geq == UpsideDown(Leq)
        S == ThoseUnder(Y, x, Geq)
        w == Floor(x, Y, Geq)
        P == Support(Geq)
    <1>1. IsACompleteLattice(Geq)
        BY UpsideDownIsLattice
    <1>2. Geq = [t \in Z \X Z |-> Leq[t[2], t[1]]]
        BY DEF UpsideDown
    <1>3. Leq[x, w] = Geq[w, x]
        <2>1. Z = P
            BY UpsideDownHasSameSupport
        <2>2. x \in Z
            OBVIOUS
        <2>3. w \in P
            <3>1. w = Supremum(S, Geq)
                BY DEF Floor, ThoseUnder
            <3>2. S \subseteq Z
                BY DEF ThoseUnder
            <3>3. S \subseteq P
                BY <2>1, <3>2
            <3> QED
                BY <3>1, <3>3, <1>1, SupExists
        <2>4. DOMAIN Leq = Z \X Z
            BY LatticeHasSymmetricDomain
        <2>5. DOMAIN Geq = Z \X Z
            BY <1>2
        <2>6. << x, w >> \in DOMAIN Leq
            <3> HIDE DEF Z, P
            <3> QED
                BY <2>1, <2>2, <2>3, <2>4
        <2>7. << w, x >> \in DOMAIN Geq
            BY <2>1, <2>2, <2>3, <2>5
        <2> QED
            BY <1>2, <2>6, <2>7
    <1>4. Leq[x, w]
        <2>1. Z = Support(Geq)
            BY UpsideDownHasSameSupport
        <2>2. Geq[w, x]
            BY <1>1, <2>1, FloorIsSmaller
        <2> QED
            BY <2>2, <1>3
    <1>5. r = w
        <2>1. ThoseOver(Y, x, Leq) = ThoseUnder(Y, x, Geq)
            BY <1>2 DEF ThoseOver, ThoseUnder
        <2>2. w = Supremum(S, Geq)
            BY DEF Floor, ThoseUnder
        <2>3. r = Infimum(S, Leq)
            BY <2>1 DEF Ceil, ThoseOver
        <2> QED
            BY <2>2, <2>3 DEF Supremum, Infimum
    <1> QED
        BY <1>4, <1>5


(* Similar to MaxFloorSmaller. *)
THEOREM MaxCeilSmaller ==
    ASSUME
        NEW X, NEW Y, NEW Leq,
        IsFiniteSet(X)
    PROVE
        LET
            R == MaxCeilings(X, Y, Leq)
            T == Ceilings(X, Y, Leq)
        IN
            /\ R \subseteq T
            /\ IsFiniteSet(R) /\ IsFiniteSet(T)
            /\ Cardinality(R) <= Cardinality(T)
            /\ Cardinality(T) <= Cardinality(X)
    PROOF
    <1> DEFINE
        R == MaxCeilings(X, Y, Leq)
        T == Ceilings(X, Y, Leq)
    <1>1. R = Maxima(T, Leq)
        BY DEF MaxCeilings
    <1>2. R \subseteq T
        BY <1>1, MaxIsSubset
    <1>3. /\ IsFiniteSet(T)
          /\ Cardinality(T) <= Cardinality(X)
        BY ImageOfFinite DEF Ceilings
    <1>4. /\ IsFiniteSet(R)
          /\ Cardinality(R) <= Cardinality(T)
        BY <1>2, <1>3, FS_Subset
    <1> QED
        BY <1>2, <1>3, <1>4, FS_CardinalityType

--------------------------------------------------------------------------------
(* Reasoning about the variant (termination). *)


THEOREM FloorEqual ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW X0, NEW Y0, NEW y \in Y,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN /\ X0 \subseteq Z
           /\ Y0 \subseteq Z
           /\ X \subseteq Z
           /\ Y \subseteq Z
           /\ IsFiniteSet(X0) /\ IsFiniteSet(Y0)
           (* the next line should be provable from the above line *)
           /\ IsFiniteSet(X) /\ IsFiniteSet(Y)
           /\ X = MaxCeilings(X0, Y, Leq)
           /\ Y = MaxFloors(Y0, X0, Leq)
           /\ Cardinality(X) = Cardinality(X0)
    PROVE
        y = Floor(y, X, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        RTX0 == Ceilings(X0, Y, Leq)
        y0 == CHOOSE r \in Y0:  y = Floor(r, X0, Leq)
        S0 == ThoseUnder(X0, y0, Leq)
        S1 == ThoseUnder(X0, y, Leq)
        S2 == ThoseUnder(RTX0, y, Leq)
        S == ThoseUnder(X, y, Leq)
        a == Floor(y0, X0, Leq)
        b == Floor(y, X, Leq)
        c == Floor(y, X0, Leq)
    <1>1. /\ Floor(y0, X0, Leq) = Supremum(S0, Leq)
          /\ Floor(y, X0, Leq) = Supremum(S1, Leq)
          /\ Floor(y, X, Leq) = Supremum(S, Leq)
        BY DEF Floor
    <1>2. /\ S0 \subseteq Z
          /\ S1 \subseteq Z
          /\ S \subseteq Z
        BY DEF ThoseUnder
    <1>3. /\ a \in Z
          /\ b \in Z
          /\ c \in Z
        BY <1>1, <1>2, SupExists
    <1>4. SUFFICES Leq[y, b]
        <2>1. Leq[b, y]
            BY FloorIsSmaller
        <2>2. IsAntiSymmetric(Leq)
            BY DEF IsACompleteLattice, IsAPartialOrder
        <2> QED
            BY <2>1, <2>2, <1>3 DEF IsAntiSymmetric
    <1>5. y = Floor(y0, X0, Leq)
        <2>1. SUFFICES \E r \in Y0:  y = Floor(r, X0, Leq)
            OBVIOUS
        <2>2. Y = Maxima(Floors(Y0, X0, Leq), Leq)
            BY DEF MaxFloors
        <2>3. Y \subseteq Floors(Y0, X0, Leq)
            BY <2>2, MaxIsSubset
        <2> QED
            BY <2>3 DEF Floors
    <1>6. SUFFICES Leq[a, b]
        BY <1>5
    <1>7. X = Ceilings(X0, Y, Leq)
        <2>1. X = Maxima(RTX0, Leq)
            BY DEF MaxCeilings
        <2>2. X \subseteq RTX0
            BY <2>1, MaxIsSubset
        <2>3. Cardinality(RTX0) <= Cardinality(X0)
            BY ImageOfFinite DEF Ceilings
        <2>4. Cardinality(X) <= Cardinality(RTX0)
            BY <2>2, FS_Subset, MaxCeilSmaller
        <2>5. Cardinality(X) = Cardinality(X0)
            OBVIOUS
        <2>6. Cardinality(X0) <= Cardinality(RTX0)
            BY <2>4, <2>5
        <2>7. /\ IsFiniteSet(RTX0)
              /\ Cardinality(X0) = Cardinality(RTX0)
            BY <2>2, <2>6, MaxCeilSmaller, FS_CardinalityType
        <2>8. Cardinality(X) = Cardinality(RTX0)
            BY <2>7
        <2> QED
            BY <2>1, <2>7, <2>8, MaxSame
    <1>8. S0 \subseteq S1
        <2>1. SUFFICES \A x \in S0:  Leq[x, y]
            BY DEF ThoseUnder
        <2>2. y = Supremum(S0, Leq)
            BY <1>1, <1>5
        <2>3. IsAbove(y, S0, Leq)
            BY <2>2, <1>2, SupExists
        <2> QED
            BY <2>3 DEF IsAbove
    <1>9. Leq[a, c]
        BY <1>8, <1>1, <1>2, SupIsMonotonic
    <1>10. SUFFICES Leq[c, b]
        <2>1. Leq[a, c]
            BY <1>9
        <2>2. Leq[c, b]
            BY <1>10
        <2>3. IsTransitive(Leq)
            BY DEF IsACompleteLattice, IsAPartialOrder
        <2> QED
            BY <2>1, <2>2, <2>3, <1>3 DEF IsTransitive
    <1>11. SUFFICES Refines(S1, S, Leq)
        BY <1>1, <1>2, SupOfRefinement DEF Refines
    <1>12. SUFFICES Refines(S1, S2, Leq)
        BY <1>7
    <1>13. SUFFICES \A u \in S1:  \E v \in S2:  Leq[u, v]
        BY DEF Refines
    <1>14. \A x \in S1:  Leq[x, y]
        BY DEF ThoseUnder
    <1>15. \A x \in S1:  Leq[x, Ceil(x, Y, Leq)]
        BY <1>2, CeilIsLarger
    <1>16. \A x \in X0:  Ceil(x, Y, Leq) \in RTX0
        BY DEF Ceilings
    <1>17. \A x \in X0:  LET C == Ceil(x, Y, Leq)
                         IN Leq[x, y] => Leq[C, y]
        BY CeilIsBelowThoseOver
    <1>18. S1 \subseteq X0
        BY DEF ThoseUnder
    <1>19. \A x \in S1:  LET C == Ceil(x, Y, Leq)
                         IN Leq[C, y]
        BY <1>18, <1>14, <1>17
    <1>20. \A x \in S1:  Ceil(x, Y, Leq) \in RTX0
        BY <1>18, <1>19 DEF Ceilings
    <1>21. \A x \in S1:  Ceil(x, Y, Leq) \in S2
        BY <1>19, <1>20 DEF ThoseUnder
    <1> QED
        BY <1>15, <1>21


THEOREM CeilEqual ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW X0, NEW Y0, NEW x \in X,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN /\ X0 \subseteq Z
           /\ Y0 \subseteq Z
           /\ X \subseteq Z
           /\ Y \subseteq Z
           /\ IsFiniteSet(X0) /\ IsFiniteSet(Y0)
           /\ IsFiniteSet(X) /\ IsFiniteSet(Y)
           /\ X = MaxCeilings(X0, Y, Leq)
           /\ Y = MaxFloors(Y0, X0, Leq)
           /\ Cardinality(Y) = Cardinality(Y0)
    PROVE
        x = Ceil(x, Y, Leq)
    PROOF OMITTED  (* similar to proof of `FloorEqual`. *)


THEOREM Fixpoint ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW X0, NEW Y0,
        IsACompleteLattice(Leq),
        LET Z == Support(Leq)
        IN
            /\ X0 \subseteq Z
            /\ Y0 \subseteq Z
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ IsFiniteSet(X0) /\ IsFiniteSet(Y0)
            (* The next line should be provable from the previous line. *)
            /\ IsFiniteSet(X) /\ IsFiniteSet(Y)
            /\ X = MaxCeilings(X0, Y, Leq)
            /\ Y = MaxFloors(Y0, X0, Leq)
                (* variant unchanged *)
            /\ Cardinality(X) = Cardinality(X0)
            /\ Cardinality(Y) = Cardinality(Y0)
    PROVE
        /\ X = MaxCeilings(X, Y, Leq)
        /\ Y = MaxFloors(Y, X, Leq)
    PROOF
    <1>1. Y = MaxFloors(Y, X, Leq)
        <2>1. Y = Maxima(Y, Leq)
            BY MaxIsIdempotent DEF MaxFloors
        <2>2. SUFFICES Y = Floors(Y, X, Leq)
            BY <2>1 DEF MaxFloors
        <2>3. SUFFICES ASSUME NEW y \in Y
                       PROVE y = Floor(y, X, Leq)
            BY <2>2 DEF Floors
        <2> QED
            BY FloorEqual
    <1>2. X = MaxCeilings(X, Y, Leq)
        (* Proof similar to that of step <1>1. *)
        <2>1. X = Maxima(X, Leq)
            BY MaxIsIdempotent DEF MaxCeilings
        <2>2. SUFFICES X = Ceilings(X, Y, Leq)
            BY <2>1 DEF MaxCeilings
        <2>3. SUFFICES ASSUME NEW x \in X
                       PROVE x = Ceil(x, Y, Leq)
            BY <2>2 DEF Ceilings
        <2> QED
            BY CeilEqual
    <1> QED
        BY <1>1, <1>2

--------------------------------------------------------------------------------
(* Removing essential elements is an isomorphism for the minimal covers. *)

(* X \cap Y contains only essential elements. *)
PROPOSITION CommonAreEssential ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C,
        IsACompleteLattice(Leq),
        LET
            Z == Support(Leq)
        IN
            /\ C \subseteq Y
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ Y = Maxima(Y, Leq)  (* antichain *)
            /\ IsACover(C, X, Leq)
    PROVE
        (X \cap Y) \subseteq C
    PROOF
    <1>1. SUFFICES \A u \in X \cap Y:  \A y \in Y:
                       Leq[u, y] => (u = y)
        BY DEF IsACover
    <1>2. IsAntiChain(Y, Leq)
        BY LatticeProperties, MaximaIsAntiChain
    <1> QED
        BY <1>2 DEF IsAntiChain


LEMMA RemainsMinCoverAfterAddingEssential ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW Ce,
        IsACompleteLattice(Leq),
        LET
            Z == Support(Leq)
            E == X \cap Y
        IN
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ X = Maxima(X, Leq)
            /\ Y = Maxima(Y, Leq)
            /\ IsAMinCover(Ce, X \ E, Y \ E, Leq)
            /\ IsFiniteSet(Z)
            /\ CardinalityAsCost(Z)
    PROVE
        LET
            E == X \cap Y
            C == Ce \cup E
        IN IsAMinCover(C, X, Y, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        E == X \cap Y
        Card(u) == Cardinality(u)
        C == Ce \cup E
        Xe == X \ E
        Ye == Y \ E
    <1>1. SUFFICES ASSUME ~ IsAMinCover(C, X, Y, Leq)
                   PROVE FALSE
        OBVIOUS
    <1>2. /\ IsACover(Ce, Xe, Leq)
          /\ Ce \in SUBSET Ye
        BY MinCoverProperties
    <1>3. PICK W \in SUBSET Y:
            /\ IsACover(W, X, Leq)
            /\ CostLeq[ << W, C >> ]
            /\ ~ CostLeq[ << C, W >> ]
        <2>1. IsACoverFrom(C, X, Y, Leq)
            <3>1. IsACoverFrom(Ce, Xe, Ye, Leq)
                BY <1>2 DEF IsACoverFrom, IsACover
            <3>2. IsACoverFrom(C, Xe \cup E, Ye \cup E, Leq)
                BY <1>2, <3>1, LatticeProperties, AddToBoth
            <3> QED
                BY <3>2
        <2>2. C \in CoversOf(X, Y, Leq)
            BY <2>1 DEF IsACoverFrom, CoversOf
        <2> HIDE DEF C
        <2> QED
            BY <1>1, <2>2, CheaperCoverExists
    <1> DEFINE We == W \ E
    <1>4. We \in SUBSET Ye
        BY <1>3
    <1>5. /\ IsFiniteSet(W) /\ IsFiniteSet(We)
          /\ IsFiniteSet(C) /\ IsFiniteSet(Ce)
          /\ IsFiniteSet(E)
       <2>1. USE FS_Subset
       <2>2. IsFiniteSet(Ce)
           BY <1>2
       <2>3. IsFiniteSet(E)
           OBVIOUS
       <2>4. IsFiniteSet(C)
           BY <2>2, <2>3, FS_Union
       <2>5. IsFiniteSet(W)
           BY <1>3
       <2>6. IsFiniteSet(We)
           BY <2>3, <2>5
       <2> QED
           BY <2>2, <2>3, <2>4, <2>5, <2>6
    <1>6. /\ Card(W) = Card(We) + Card(E)
          /\ Card(C) = Card(Ce) + Card(E)
       <2>1. Card(W) = Card(We) + Card(E)
           <3>1. W = We \cup E
               <4>1. E \subseteq W
                   BY <1>3, CommonAreEssential
               <4> QED
                   BY <4>1
           <3>2. We \cap E = {}
               BY <1>4
           <3> QED
               BY <1>5, <3>1, <3>2, FS_UnionDisjoint
       <2>2. Card(C) = Card(Ce) + Card(E)
           <3>1. C = Ce \cup E
               OBVIOUS
           <3>2. Ce \cap E = {}
               BY <1>2
           <3> QED
               BY <1>5, <3>1, <3>2, FS_UnionDisjoint
        <2> QED
            BY <2>1, <2>2
    <1>7. /\ C \in DOMAIN Cost /\ Ce \in DOMAIN Cost
          /\ W \in DOMAIN Cost /\ We \in DOMAIN Cost
        BY <1>2, <1>3 DEF CardinalityAsCost
    <1>8. CostLeq[ << We, Ce >> ]
        <2>1. USE DEF CardinalityAsCost, CostLeq
        <2>2. CostLeq[ << W, C >> ]
            BY <1>3
        <2>3. Card(W) <= Card(C)
            <3>1. << W, C >> \in DOMAIN CostLeq
                BY <1>7
            <3>2. Cost[W] <= Cost[C]
                BY <2>2, <3>1
            <3> QED
                BY <1>7, <3>2
        <2>4. Card(We) <= Card(Ce)
            BY <1>5, <1>6, <2>3, FS_CardinalityType
        <2> QED
            <3>1. Cost[We] <= Cost[Ce]
                BY <1>7, <2>4
            <3>2. << We, Ce >> \in DOMAIN CostLeq
                BY <1>7
            <3> QED
                BY <3>1, <3>2
    <1>9. ~ CostLeq[ << Ce, We >> ]
        <2>1. USE DEF CardinalityAsCost, CostLeq
        <2>2. SUFFICES ASSUME CostLeq[ << Ce, We >> ]
                       PROVE FALSE
            OBVIOUS
        <2>3. Card(Ce) <= Card(We)
            <3>1. << Ce, We >> \in DOMAIN CostLeq
                BY <1>7, CostLeqHelper
            <3>2. Cost[Ce] <= Cost[We]
                BY <2>2, <3>1
            <3> QED
                BY <1>7, <3>2
        <2>4. CostLeq[ << C, W >> ]
            <3>1. << C, W >> \in DOMAIN CostLeq
                BY <1>7, CostLeqHelper
            <3>2. Card(C) <= Card(W)
                BY <2>3, <1>6, <1>5, FS_CardinalityType
            <3>3. Cost[C] <= Cost[W]
                BY <1>7, <3>2
            <3> QED
                BY <3>1, <3>3
        <2>5. ~ CostLeq[ << C, W >> ]
            BY <1>3
        <2> QED
            BY <2>4, <2>5
    <1>10. CostLeq[ << Ce, We >> ]  (* because `C` is a minimal cover and *)
                            (* `W` is a cover that costs no more *)
                            (* than `C`, so they must cost the same. *)
        <2>1. \A r \in SUBSET Ye:
                \/ ~ /\ IsACover(r, Xe, Leq)
                     /\ CostLeq[ << r, Ce >> ]
                \/ CostLeq[ << Ce, r >> ]
            BY MinCoverProperties
        <2>2. We \in SUBSET Ye
            BY <1>4
        <2>3. IsACover(We, Xe, Leq)
            BY <1>3, SubtractFromBoth, LatticeProperties
        <2> QED
            BY <2>1, <2>2, <2>3, <1>8
    <1> QED
        BY <1>9, <1>10


LOCAL PhantomProp(OtherCover, C, X, Leq) ==
    /\ OtherCover # C
    /\ IsACover(OtherCover, X, Leq)
    /\ CostLeq[ << OtherCover, C >> ]
    /\ ~ CostLeq[ << C, OtherCover >> ]


(* The following helps Isabelle check proof correctness. *)
THEOREM CheaperCoverExistsHelper ==
    ASSUME
        NEW Leq, NEW X, NEW Y,
        NEW C \in CoversOf(X, Y, Leq),  (* so some cover exists *)
        ~ IsAMinCover(C, X, Y, Leq)
    PROVE
        \E OtherCover \in SUBSET Y:  PhantomProp(OtherCover, C, X, Leq)
    PROOF
    BY CheaperCoverExists DEF PhantomProp


(* If `C` is a minimal cover of `X`, *)
(* then `C \ E` is a minimal cover of `X \ E`. *)
LEMMA RemainsMinCoverAfterRemovingEssential ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C,
        IsACompleteLattice(Leq),
        LET
            Z == Support(Leq)
            E == X \cap Y
        IN
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ X = Maxima(X, Leq)
            /\ Y = Maxima(Y, Leq)
            /\ IsAMinCover(C, X, Y, Leq)
            /\ IsFiniteSet(Z)
            /\ CardinalityAsCost(Z)
    PROVE
        LET
            E == X \cap Y
            Xe == X \ E
            Ye == Y \ E
            Ce == C \ E
        IN
            IsAMinCover(Ce, Xe, Ye, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        E == X \cap Y
        Card(u) == Cardinality(u)
        Ce == C \ E
        Xe == X \ E
        Ye == Y \ E
    <1>1. SUFFICES ASSUME ~ IsAMinCover(Ce, Xe, Ye, Leq)
                   PROVE FALSE
        OBVIOUS
    <1>2. /\ IsACover(C, X, Leq)
          /\ C \in SUBSET Y
        BY MinCoverProperties
    <1>3. PICK We \in SUBSET Ye:
            /\ IsACover(We, Xe, Leq)
            /\ CostLeq[ << We, Ce >> ]
            /\ ~ CostLeq[ << Ce, We >> ]
        <2>1. IsACover(Ce, Xe, Leq)
            BY <1>2, SubtractFromBoth, LatticeProperties
        <2>2. Ce \in SUBSET Ye
            BY MinCoverProperties
        <2>3. Ce \in CoversOf(Xe, Ye, Leq)
            BY <2>1, <2>2 DEF CoversOf
        <2> QED
            (* Extra step to help Isabelle check the generated proofs. *)
            <3>1. \E We \in SUBSET Ye:  PhantomProp(We, Ce, Xe, Leq)
                BY <1>1, <2>3, CheaperCoverExistsHelper
            <3> QED
                BY <3>1 DEF PhantomProp
    <1> DEFINE W == We \cup E
    <1>4. IsACoverFrom(W, X, Y, Leq)
        <2>1. IsACoverFrom(We, Xe, Ye, Leq)
            BY <1>3 DEF IsACoverFrom
        <2>2. IsACoverFrom(We \cup E, Xe \cup E, Ye \cup E, Leq)
            BY <2>1, AddToBoth, LatticeProperties
        <2>3. /\ X = Xe \cup E
              /\ Y = Ye \cup E
            OBVIOUS
        <2> QED
            BY <2>2, <2>3
    <1>5. /\ IsFiniteSet(W) /\ IsFiniteSet(We)
          /\ IsFiniteSet(C) /\ IsFiniteSet(Ce)
          /\ IsFiniteSet(E)
        BY <1>2, <1>3, FS_Subset, FS_Union
    <1>6. /\ Card(W) = Card(We) + Card(E)
          /\ Card(C) = Card(Ce) + Card(E)
        <2>1. USE FS_UnionDisjoint
        <2>2. Card(W) = Card(We) + Card(E)
            BY <1>5
        <2>3. Card(C) = Card(Ce) + Card(E)
            <3>1. E \subseteq C
                BY <1>2, CommonAreEssential
            <3> QED
                BY <3>1, <1>5
        <2> QED
            BY <2>2, <2>3
    <1>7. /\ C \in DOMAIN Cost /\ Ce \in DOMAIN Cost
          /\ W \in DOMAIN Cost /\ We \in DOMAIN Cost
        BY <1>2, <1>3 DEF CardinalityAsCost
    <1>8. CostLeq[ << W, C >> ]
        <2> USE DEF CardinalityAsCost, CostLeq
        <2>1. CostLeq[ << We, Ce >> ]
            BY <1>3
        <2>2. Card(We) <= Card(Ce)
            BY <1>7, <2>1
        <2>3. Card(W) <= Card(C)
            BY <2>2, <1>6, <1>5, FS_CardinalityType
        <2> QED
            <3>1. Cost[W] <= Cost[C]
                BY <2>3, <1>7
            <3>2. << W, C >> \in DOMAIN CostLeq
                BY <1>7
            <3> QED
                BY <3>1, <3>2
    <1>9. ~ CostLeq[ << C, W >> ]
        <2> USE DEF CardinalityAsCost, CostLeq
        <2>1. SUFFICES ASSUME CostLeq[ << C, W >> ]
                       PROVE FALSE
            OBVIOUS
        <2>2. Card(C) <= Card(W)
            BY <2>1, <1>7
        <2>3. CostLeq[ << Ce, We >> ]
            <3>1. Card(Ce) <= Card(We)
                BY <2>2, <1>6, <1>5, FS_CardinalityType
            <3> QED
                BY <3>1, <1>7
        <2>4. ~ CostLeq[ << Ce, We >> ]
            BY <1>3
        <2> QED
            BY <2>3, <2>4
    <1>10. CostLeq[ << C, W >> ]
        <2>1. \A r \in SUBSET Y:
                \/ ~ /\ IsACover(r, X, Leq)
                     /\ CostLeq[ << r, C >> ]
                \/ CostLeq[ << C, r >> ]
            BY MinCoverProperties
        <2>2. /\ W \in SUBSET Y
              /\ IsACover(W, X, Leq)
            BY <1>4 DEF IsACoverFrom
        <2> QED
            BY <2>1, <2>2, <1>8
    <1> QED
        BY <1>9, <1>10


THEOREM MinCoverUnchangedByEssential ==
    ASSUME
        NEW Leq, NEW X, NEW Y,
        NEW C, NEW Ce,
        IsACompleteLattice(Leq),
        LET
            Z == Support(Leq)
            E == X \cap Y
        IN
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ X = Maxima(X, Leq)
            /\ Y = Maxima(Y, Leq)
            /\ IsFiniteSet(Z)
            /\ CardinalityAsCost(Z)
            /\ C = (Ce \cup E)
            /\ Ce = C \ E
    PROVE
        LET
            E == X \cap Y
            Xe == X \ E
            Ye == Y \ E
        IN
            IsAMinCover(C, X, Y, Leq) <=> IsAMinCover(Ce, Xe, Ye, Leq)
    PROOF
    <1> DEFINE
        E == X \cap Y
        Xe == X \ E
        Ye == Y \ E
    <1>1. ASSUME IsAMinCover(C, X, Y, Leq)
          PROVE IsAMinCover(Ce, Xe, Ye, Leq)
        <2>1. Ce = C \ E
            OBVIOUS
        <2> QED
            BY <1>1, <2>1, RemainsMinCoverAfterRemovingEssential
    <1>2. ASSUME IsAMinCover(Ce, Xe, Ye, Leq)
          PROVE IsAMinCover(C, X, Y, Leq)
        <2>1. C = Ce \cup E
            OBVIOUS
        <2> QED
            BY <1>2, RemainsMinCoverAfterAddingEssential
    <1> QED
        BY <1>1, <1>2

--------------------------------------------------------------------------------
(* `Hat` properties. *)

(* Above each element in a partially ordered finite set
there exists some maximal element.
*)
THEOREM HasSomeMaximalAbove ==
    ASSUME
        NEW Leq, NEW S, NEW u \in S,
        LET
            Z == Support(Leq)
        IN
            /\ IsFiniteSet(Z)
            /\ S \subseteq Z
            /\ IsReflexive(Leq)
            /\ IsTransitive(Leq)
            /\ IsAntiSymmetric(Leq)
    PROVE
        \E v \in S:  /\ Leq[u, v]
                     /\ IsMaximal(v, S, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Geq == UpsideDown(Leq)
        W == Support(Geq)
    <1>1. /\ IsReflexive(Geq)
          /\ IsTransitive(Geq)
          /\ IsAntiSymmetric(Geq)
          /\ W = Z
        BY SwapPreservesOrderProperties, UpsideDownHasSameSupport
    <1>2. PICK v \in S:  /\ Geq[v, u]
                         /\ IsMinimal(v, S, Geq)
        BY <1>1, HasSomeMinimalBelow
    <1>3. Leq[u, v]
        BY <1>2, LeqSwapOfGeq
    <1>4. IsMaximal(v, S, Leq)
        <2>1. /\ v \in S
              /\ \A q \in S:  Geq[q, v] => Geq[v, q]
            BY <1>2 DEF IsMinimal
        <2>2. \A q \in S:  Leq[v, q] => Leq[q, v]
            BY <2>1, LeqSwapOfGeq
        <2> QED
            BY <2>1, <2>2 DEF IsMaximal
    <1> QED
        BY <1>3, <1>4


(* Any subset `Y` of a partially ordered finite set `Z` can be mapped to
its "MaxHat", made of maximal elements above each `y \in Y`.
*)
LEMMA HasMaxHat ==
    ASSUME
        NEW Leq, NEW S, NEW Y,
        LET
            Z == Support(Leq)
        IN
            /\ IsAPartialOrder(Leq)
            /\ IsFiniteSet(Z)
            /\ S \subseteq Y
            /\ Y \subseteq Z
    PROVE
        LET
            Max == Maxima(Y, Leq)
        IN
            \A y \in S:  \E ym \in Max:  Leq[y, ym]
    PROOF
    <1>1. ASSUME NEW y \in S
          PROVE \E ym \in Y:  /\ Leq[y, ym]
                              /\ IsMaximal(ym, Y, Leq)
        <2>1. y \in Y
            OBVIOUS
        <2> QED
            BY <2>1, HasSomeMaximalAbove DEF IsAPartialOrder
    <1> QED
        BY <1>1 DEF Maxima


(* `H` is smaller than `S` if any two of the selected maximal
elements above different elements of `P` coincide.
*)
PROPOSITION MaxHatProperties ==
    ASSUME
        NEW Leq, NEW S, NEW Y,
        LET
            Z == Support(Leq)
        IN
            /\ IsAPartialOrder(Leq)
            /\ IsFiniteSet(Z)
            /\ S \subseteq Y
            /\ Y \subseteq Z
    PROVE
        LET
            Max == Maxima(Y, Leq)
            H == MaxHat(S, Y, Leq)
        IN
            /\ IsFiniteSet(H)
            /\ H \in SUBSET Max
            /\ Refines(S, H, Leq)
            /\ Cardinality(H) <= Cardinality(S)
    PROOF
    <1> DEFINE
        Max == Maxima(Y, Leq)
        H == MaxHat(S, Y, Leq)
    <1>1. IsFiniteSet(S)
        BY FS_Subset
    <1>2. /\ IsFiniteSet(H)
          /\ Cardinality(H) <= Cardinality(S)
        <2> DEFINE
            f == [u \in S |-> SomeMaxAbove(u, Y, Leq)]
        <2>1. f \in Surjection(S, H)
            BY DEF Surjection, MaxHat
        <2> QED
            BY <2>1, <1>1, FS_Surjection
    <1>3. /\ H \in SUBSET Max
          /\ Refines(S, H, Leq)
        BY HasMaxHat DEF MaxHat, SomeMaxAbove, Refines
    <1> QED
        BY <1>2, <1>3


THEOREM MaxHatIsCoverToo ==
    ASSUME
        NEW Leq, NEW X, NEW S, NEW H,
        LET
            Z == Support(Leq)
        IN
            /\ IsTransitive(Leq)
            /\ IsFiniteSet(Z)
            /\ X \subseteq Z
            /\ S \subseteq Z
            /\ H \subseteq Z
            /\ Refines(S, H, Leq)
            /\ IsACover(S, X, Leq)
    PROVE
        IsACover(H, X, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
    <1> USE DEF IsACover
    <1>1. SUFFICES ASSUME NEW u \in X
                   PROVE \E ym \in H:  Leq[u, ym]
        OBVIOUS
    <1>2. PICK y \in S:  Leq[u, y]
        BY <1>1
    <1>3. PICK ym \in H:  Leq[y, ym]
        BY DEF Refines
    <1>4. /\ u \in Z
          /\ y \in Z
          /\ ym \in Z
        BY <1>1, <1>2, <1>3
    <1> QED
        BY <1>2, <1>3, <1>4 DEF IsTransitive

--------------------------------------------------------------------------------
(* Effect of `MaxCeilings(X)` on minimal covers. *)


(* `Max(X)` preserves covers. *)
LEMMA MaxPreservesCovers ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C \in SUBSET Y,
        LET
            Z == Support(Leq)
        IN
            /\ IsFiniteSet(Z)
            /\ IsAPartialOrder(Leq)
            /\ X \subseteq Z
            /\ Y \subseteq Z
    PROVE
        LET Max == Maxima(X, Leq)
        IN IsACover(C, X, Leq) <=> IsACover(C, Max, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Max == Maxima(X, Leq)
    <1>1. ASSUME IsACover(C, X, Leq)
          PROVE IsACover(C, Max, Leq)
        BY <1>1, MaxIsSubset DEF IsACover
    <1>2. ASSUME IsACover(C, Max, Leq)
          PROVE IsACover(C, X, Leq)
        <2>1. SUFFICES ASSUME NEW u \in X
                       PROVE \E y \in C:  Leq[u, y]
            BY DEF IsACover
        <2>2. PICK v \in X:  Leq[u, v] /\ IsMaximal(v, X, Leq)
            BY <2>1, HasSomeMaximalAbove DEF IsAPartialOrder
        <2>3. v \in Max
            BY <2>2 DEF Maxima
        <2>4. PICK y \in C:  Leq[v, y]
            BY <1>2, <2>3 DEF IsACover
        <2>5. Leq[u, y]
            <3>1. (Z \X Z) = DOMAIN Leq
                BY PartialOrderHasSymmetricDomain
            <3>2. /\ u \in Z
                  /\ v \in Z
                  /\ y \in Z
                BY <2>1, <2>2, <2>4
            <3>3. Leq[u, v] /\ Leq[v, y]
                BY <2>2, <2>4
            <3> QED
                BY <3>2, <3>3 DEF IsAPartialOrder, IsTransitive
        <2> QED
            BY <2>5
    <1> QED
        BY <1>1, <1>2


(* Ceilings(X) preserves covers. *)
LEMMA CeilPreservesCovers ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C \in SUBSET Y,
        LET
            Z == Support(Leq)
        IN
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ IsACompleteLattice(Leq)
    PROVE
        LET Top == Ceilings(X, Y, Leq)
        IN IsACover(C, X, Leq) <=> IsACover(C, Top, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Top == Ceilings(X, Y, Leq)
    <1>1. ASSUME IsACover(C, X, Leq)
          PROVE IsACover(C, Top, Leq)
        <2>1. SUFFICES ASSUME NEW u \in Top
                       PROVE \E y \in C:  Leq[u, y]
            BY DEF IsACover
        <2>2. PICK r \in X:  u = Ceil(r, Y, Leq)
            BY <2>1 DEF Ceilings
        <2>3. PICK y \in C:  Leq[r, y]
            BY <1>1 DEF IsACover
        <2> QED
            BY <2>2, <2>3, CeilIsBelowThoseOver
    <1>2. ASSUME IsACover(C, Top, Leq)
          PROVE IsACover(C, X, Leq)
        <2>1. SUFFICES ASSUME NEW r \in X
                       PROVE \E y \in C:  Leq[r, y]
            BY DEF IsACover
        <2> DEFINE u == Ceil(r, Y, Leq)
        <2>2. Leq[r, u]
            BY <2>1, CeilIsLarger
        <2>3. PICK y \in C:  Leq[u, y]
            <3>1. u \in Top
                BY DEF Ceilings
            <3> QED
                BY <3>1, <1>2 DEF IsACover
        <2>4. IsTransitive(Leq)
            BY LatticeProperties
        <2> QED
            <3>1. /\ r \in Z
                  /\ u \in Z
                  /\ y \in Z
                <4>1. u \in Z
                    BY <2>1, InfExists DEF Ceil, ThoseOver
                <4> QED
                    BY <2>1, <2>3, <4>1
            <3>2. Leq[r, u] /\ Leq[u, y]
                BY <2>2, <2>3
            <3> QED
                BY <3>1, <3>2, <2>4 DEF IsTransitive
    <1> QED
        BY <1>1, <1>2


(* MaxCeilings(X) preserves covers. *)
THEOREM MaxCeilPreservesCovers ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C \in SUBSET Y,
        LET
            Z == Support(Leq)
        IN
            /\ IsFiniteSet(Z)
            /\ IsACompleteLattice(Leq)
            /\ X \subseteq Z
            /\ Y \subseteq Z
    PROVE
        LET R == MaxCeilings(X, Y, Leq)
        IN IsACover(C, X, Leq) <=> IsACover(C, R, Leq)
    PROOF
    <1> DEFINE
        Top == Ceilings(X, Y, Leq)
        Max == Maxima(Top, Leq)
        R == MaxCeilings(X, Y, Leq)
    <1>1. R = Max
        BY DEF MaxCeilings
    <1>2. IsACover(C, X, Leq) <=> IsACover(C, Top, Leq)
        BY CeilPreservesCovers
    <1>3. IsACover(C, Top, Leq) <=> IsACover(C, Max, Leq)
        <2>1. Top \subseteq Support(Leq)
            BY InfExists DEF Ceilings, Ceil, ThoseOver
        <2>2. IsAPartialOrder(Leq)
            BY DEF IsACompleteLattice
        <2> QED
            BY <2>1, <2>2, MaxPreservesCovers
    <1> QED
        BY <1>1, <1>2, <1>3


THEOREM MinCoverUnchangedByMaxCeil ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C \in SUBSET Y,
        LET
            Z == Support(Leq)
        IN
            /\ IsFiniteSet(Z)
            /\ IsACompleteLattice(Leq)
            /\ X \subseteq Z
            /\ Y \subseteq Z
    PROVE
        LET R == MaxCeilings(X, Y, Leq)
        IN IsAMinCover(C, X, Y, Leq) <=> IsAMinCover(C, R, Y, Leq)
    PROOF
    BY MaxCeilPreservesCovers DEF IsAMinCover, CoversOf

--------------------------------------------------------------------------------
(* Effect of `Maxima(Y)` on minimal covers. *)


(* Soundness of Max(Y):
Every cover using elements from Max(Y) that is minimal within Max(Y) is
a cover from Y minimal within Y.
*)
LEMMA MinCoversFromMaxSuffice ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C,
        LET
            Z == Support(Leq)
            Max == Maxima(Y, Leq)
        IN
            /\ IsAPartialOrder(Leq)
            /\ IsFiniteSet(Z)
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ IsAMinCover(C, X, Max, Leq)
            /\ CardinalityAsCost(Z)
    PROVE
        IsAMinCover(C, X, Y, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Max == Maxima(Y, Leq)
    <1>1. /\ C \in SUBSET Max
          /\ IsACover(C, X, Leq)
          /\ \A r \in SUBSET Max:
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ CostLeq[ << r, C >> ]
            \/ CostLeq[ << C, r >> ]
        BY MinCoverProperties
    <1>2. /\ C \in SUBSET Max
          /\ Max \in SUBSET Y
        BY <1>1, MaxIsSubset
    <1>3. SUFFICES ASSUME ~ IsAMinCover(C, X, Y, Leq)
                   PROVE FALSE
        OBVIOUS
    <1>4. PICK P \in SUBSET Y:
            /\ IsACover(P, X, Leq)
            /\ CostLeq[ << P, C >> ]
            /\ ~ CostLeq[ << C, P >> ]
        <2>1. C \in CoversOf(X, Y, Leq)
            <3>1. C \in SUBSET Y
                BY <1>2
            <3>2. IsACover(C, X, Leq)
                BY <1>1
            <3> QED
                BY <3>1, <3>2 DEF CoversOf
        <2> QED
            BY <2>1, <1>3, CheaperCoverExists
    <1> DEFINE Pm == MaxHat(P, Y, Leq)
    <1>5. /\ Pm \in SUBSET Max
          /\ \A y \in P:  \E ym \in Pm:  Leq[y, ym]
          /\ Cardinality(Pm) <= Cardinality(P)
        BY MaxHatProperties DEF Refines
    <1>6. /\ IsFiniteSet(C) /\ (Cardinality(C) \in Nat)
          /\ IsFiniteSet(P) /\ (Cardinality(P) \in Nat)
          /\ IsFiniteSet(Pm) /\ (Cardinality(Pm) \in Nat)
        <2>1. C \in SUBSET Z
            BY <1>2
        <2>2. P \in SUBSET Z
            BY <1>4
        <2>3. Pm \in SUBSET Z
            BY <1>5, <1>2
        <2> QED
            BY <2>1, <2>2, <2>3, FS_Subset, FS_CardinalityType
    <1>7. /\ C \in DOMAIN Cost
          /\ P \in DOMAIN Cost
          /\ Pm \in DOMAIN Cost
        BY <1>2, <1>4, <1>5 DEF CardinalityAsCost
    <1>8. IsACover(Pm, X, Leq)
        <2>1. IsTransitive(Leq)
            BY DEF IsAPartialOrder
        <2>2. IsACover(P, X, Leq)
            BY <1>4
        <2>3. P \subseteq Z /\ Pm \subseteq Z
            <3>1. SUBSET Z = DOMAIN Cost
                BY DEF CardinalityAsCost
            <3> QED
                BY <1>7, <3>1
        <2>4. Refines(P, Pm, Leq)
            BY <1>5 DEF Refines
        <2> QED
            BY <2>1, <2>2, <2>3, <2>4, MaxHatIsCoverToo
    <1>9. CostLeq[ << Pm, C >> ]
        <2>1. CostLeq[ << P, C >> ]
            BY <1>4
        <2> USE DEF CardinalityAsCost, CostLeq
        <2>2. Cardinality(P) <= Cardinality(C)
            BY <2>1, <1>7
        <2>3. Cardinality(Pm) <= Cardinality(C)
            BY <2>2, <1>5, <1>6
        <2> QED
            BY <2>3, <1>7
    <1>10. ~ CostLeq[ << C, Pm >> ]
        <2>1. ~ CostLeq[ << C, P >> ]
            BY <1>4
        <2> USE DEF CardinalityAsCost, CostLeq
        <2>2. ~ (Cardinality(C) <= Cardinality(P))
            BY <2>1, <1>7
        <2>3. Cardinality(C) > Cardinality(P)
            BY <2>2, <1>6
        <2>4. Cardinality(C) > Cardinality(Pm)
            BY <2>3, <1>5, <1>6
        <2>5. ~ (Cardinality(C) <= Cardinality(Pm))
            BY <2>4, <1>6
        <2> QED
            BY <2>5, <1>7
    <1> QED
        <2>1. CostLeq[ << C, Pm >> ]
            <3>1. Pm \in SUBSET Max
                BY <1>5
            <3>2. IsACover(Pm, X, Leq)
                BY <1>8
            <3>3. CostLeq[ << Pm, C >> ]
                BY <1>9
            <3> QED
                BY <3>1, <3>2, <3>3, <1>1
        <2> QED
            BY <2>1, <1>10


(* Completeness of Max(Y):
For each cover from Y minimal within Y, there exists a cover from Max(Y)
minimal in Max(Y). So, if a minimal cover from Y exists, then a minimal cover
from Max(Y) also exists.
*)
LEMMA MaxHatOfMinCoverIsAMinCover ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C,
        LET
            Z == Support(Leq)
        IN
            /\ IsAPartialOrder(Leq)
            /\ IsFiniteSet(Z)
            /\ X \subseteq Z
            /\ Y \subseteq Z
            /\ IsAMinCover(C, X, Y, Leq)
            /\ CardinalityAsCost(Z)
    PROVE
        LET
            Max == Maxima(Y, Leq)
            Cm == MaxHat(C, Y, Leq)
        IN
            IsAMinCover(Cm, X, Max, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Max == Maxima(Y, Leq)
    <1>1. /\ C \in SUBSET Y
          /\ IsACover(C, X, Leq)
          /\ \A r \in SUBSET Y:
            \/ ~ /\ IsACover(r, X, Leq)
                 /\ CostLeq[ << r, C >> ]
            \/ CostLeq[ << C, r >> ]
        BY MinCoverProperties
    <1>2. IsFiniteSet(C)
        BY <1>1, FS_Subset
    <1>3. DEFINE Cm == MaxHat(C, Y, Leq)
    <1>4. /\ IsFiniteSet(Cm)
          /\ Cm \in SUBSET Max
          /\ Refines(C, Cm, Leq)
          /\ Cardinality(Cm) <= Cardinality(C)
        BY <1>1, MaxHatProperties
    <1>5. /\ C \in SUBSET Z
          /\ Cm \in SUBSET Z
        BY <1>1, <1>4, MaxIsSubset
    <1>6. IsACover(Cm, X, Leq)
        BY <1>4, <1>1, <1>5, MaxHatIsCoverToo DEF IsAPartialOrder
    <1>7. Cardinality(Cm) = Cardinality(C)
        <2> USE DEF CardinalityAsCost, CostLeq
        <2>1. CostLeq[ << Cm, C >> ]
            <3>1. Max \in SUBSET Y
                BY MaxIsSubset
            <3>2. /\ Cm \in DOMAIN Cost
                  /\ C \in DOMAIN Cost
                BY <1>1, <1>4, <3>1
            <3> QED
                BY <1>4, <3>2 DEF CostLeq
        <2>2. CostLeq[ << C, Cm >> ]
            <3>1. Cm \in SUBSET Y
                BY <1>4, MaxIsSubset
            <3>2. /\ IsACover(Cm, X, Leq)
                  /\ CostLeq[ << Cm, C >> ]
                BY <1>6, <2>1
            <3> QED
                BY <1>1, <3>1, <3>2
        <2>3. /\ Cardinality(Cm) <= Cardinality(C)
              /\ Cardinality(Cm) >= Cardinality(C)
            BY <2>1, <2>2, <1>5
        <2>4. /\ Cardinality(Cm) \in Nat
              /\ Cardinality(C) \in Nat
            BY <1>2, <1>4, FS_CardinalityType
        <2> QED
            BY <2>3, <2>4
    <1>8. ASSUME NEW r \in SUBSET Max,
                 /\ IsACover(r, X, Leq)
                 /\ CostLeq[ << r, Cm >> ]
          PROVE CostLeq[ << Cm, r >> ]
        <2> USE DEF CardinalityAsCost, CostLeq
        <2>1. r \in SUBSET Y
            BY <1>8, MaxIsSubset
        <2>2. CostLeq[ << r, C >> ]
            <3>1. Cardinality(r) <= Cardinality(Cm)
                BY <1>8, <1>5, <2>1
            <3>2. Cardinality(r) <= Cardinality(C)
                BY <3>1, <1>7
            <3> QED
                BY <3>2, <1>5, <2>1
        <2>3. CostLeq[ << C, r >> ]
            BY <1>1, <1>8, <2>1, <2>2
        <2> QED
            <3>1. Cardinality(C) <= Cardinality(r)
                BY <2>3, <1>5, <2>1
            <3>2. Cardinality(Cm) <= Cardinality(r)
                BY <3>1, <1>7
            <3> QED
                BY <3>2, <1>5, <2>1
    <1> QED
        BY <1>4, <1>6, <1>8 DEF IsAMinCover, IsMinimal, CoversOf

--------------------------------------------------------------------------------
(* Floor effects on minimal covers. *)


PROPOSITION UnfloorProperties ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW u,
        /\ IsACompleteLattice(Leq)
        /\ u \in Floors(Y, X, Leq)
    PROVE
        LET y == SomeUnfloor(u, X, Y, Leq)
        IN
            /\ y \in Y
            /\ u = Floor(y, X, Leq)
    PROOF
    <1>1. \E y \in Y:  u = Floor(y, X, Leq)
        BY DEF Floors
    <1> QED
        BY <1>1 DEF SomeUnfloor


(* `Cf = Floors(Unfloors(Cf))` .
But it is possible that `C # Unfloors(Floors(C))` .

The cause is that different elements in `C` can have the same `Floor` .
So for two elements `y1, y2 \in C` it can be `r == Floor(y1) = Floor(y2)`,
but `Unfloor(r)` will be a choice of one of `y1` or `y2` .
The choice is arbitrary, because `Unfloor` is defined using `CHOOSE` .
*)
PROPOSITION UnfloorSetProperties ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW Cf,
        /\ IsACompleteLattice(Leq)
        /\ Cf \subseteq Floors(Y, X, Leq)
    PROVE
        LET C == Unfloors(Cf, X, Y, Leq)
        IN
            /\ Cf = Floors(C, X, Leq)
            /\ C \subseteq Y
    PROOF
    <1> DEFINE
        C == Unfloors(Cf, X, Y, Leq)
    <1>1. SUFFICES ASSUME NEW u \in Cf
                   PROVE \E y \in Y:  u = Floor(y, X, Leq)
        BY <1>1 DEF Floors, Unfloors, SomeUnfloor
    <1> QED
        BY UnfloorProperties


(* The assumption `IsAntiChain(Cf, Leq) /\ Cf \subseteq Floors(Y, X, Leq)`
does not suffice in the following proposition, because `Cf` can be an
antichain of elements that are not maximal within `Floors(Y, X, Leq)` .
In that case, `Leq[z, fy]` does not contradict the antichain property,
because `fy` is outside the set of comparison (in that case the antichain).
*)
PROPOSITION MaxFloorsHatIsUnfloor ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW Cf,
        LET
            Z == Support(Leq)
        IN
            /\ X \subseteq Z /\ Y \subseteq Z
                (* so that `Floor` exist *)
            /\ IsACompleteLattice(Leq)
            /\ IsFiniteSet(Cf)
                (* ensures that each `z \in Cf` is below some `y \in Y` *)
                (* and that elements in `Cf` are maximal within `Floors`. *)
            /\ Cf \subseteq MaxFloors(Y, X, Leq)
    PROVE
        LET
            C == Hat(Cf, Y, Leq)
        IN
            /\ Cf = Floors(C, X, Leq)
            /\ Cardinality(Cf) = Cardinality(C)
                (* `IsUnfloors` is slightly weaker. *)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        C == Hat(Cf, Y, Leq)
        Yf == Floors(Y, X, Leq)
        F == Floors(C, X, Leq)
        Card(S) == Cardinality(S)
    <1>1. IsFiniteSet(C)
        BY ImageOfFinite DEF Hat
    <1>2. /\ Cf \subseteq Maxima(Yf, Leq)
          /\ Cf \subseteq Yf
          /\ Yf \subseteq Z
        <2>1. Cf \subseteq Maxima(Yf, Leq)
            BY DEF MaxFloors
        <2>2. Cf \subseteq Yf
            BY <2>1, MaxIsSubset
        <2>3. Yf \subseteq Z
            BY FloorExists DEF Floors
        <2> QED
            BY <2>1, <2>2, <2>3
    <1>3. \A z \in Cf:  \E y \in Y:  z = Floor(y, X, Leq)
        BY <1>2 DEF Floors
    <1>4. \A z \in Cf:  \E y \in Y:  Leq[z, y]
        BY <1>3, FloorIsSmaller
    <1>5. \A z \in Cf:  \E y \in C:  Leq[z, y]
        BY <1>4 DEF Hat, SomeAbove
    <1>6. \A y \in C:  \E z \in Cf:  Leq[z, y]
        BY <1>4 DEF Hat, SomeAbove
    <1>7. C \subseteq Y
        BY <1>4 DEF Hat, SomeAbove
    <1>8. F \subseteq Yf
        BY <1>7 DEF MaxFloors, Floors
    <1>9. Cf = F
        <2>1. ASSUME NEW z \in Cf, NEW y \in C, NEW fy \in F,
                     /\ Leq[z, y]
                     /\ fy = Floor(y, X, Leq)
              PROVE z = fy
                (* Essentially the "conversely" in Coudert's Lemma 3. *)
            <3> DEFINE fz == Floor(z, X, Leq)
            <3>1. Leq[z, fy]
                <4>1. (z \in Z) /\ (y \in Z)
                    BY <2>1, <1>2, <2>1, <1>7
                <4>2. Leq[fz, fy]
                    BY <2>1, <4>1, FloorIsMonotonic
                <4>3. z = fz
                    BY <1>3, <4>1, FloorIsIdempotent
                <4> QED
                    BY <4>2, <4>3
            <3>2. z \in Maxima(Yf, Leq)
                BY <2>1, <1>2
            <3>3. fy \in Yf
                BY <2>1, <1>8
            <3>4. Leq[fy, z]
                BY <3>2, <3>3, <3>1, MaximaProperties
            <3>5. Leq[fy, z] /\ Leq[z, fy]
                BY <3>4, <3>1
            <3>6. fy \in Z
                BY <3>3, <1>2
            <3>7. (fy \in Z) /\ (z \in Z)
                BY <3>6, <2>1, <1>2
            <3>8. IsAntiSymmetric(Leq)
                BY LatticeProperties
            <3> QED
                BY <3>5, <3>8, <3>7 DEF IsAntiSymmetric
        <2>2. Cf \subseteq F
            <3>1. SUFFICES ASSUME NEW z \in Cf
                           PROVE z \in F
                OBVIOUS
            <3>2. PICK y \in C:  Leq[z, y]
                BY <3>1, <1>5
            <3> DEFINE fy == Floor(y, X, Leq)
            <3>3. fy \in F
                BY DEF Floors
            <3>4. SUFFICES z = fy
                BY <3>3
            <3> QED
                BY <3>1, <3>2, <3>3, <2>1
        <2>3. F \subseteq Cf
            <3>1. SUFFICES ASSUME NEW fy \in F
                           PROVE fy \in Cf
                OBVIOUS
            <3>2. PICK y \in C:  fy = Floor(y, X, Leq)
                BY <3>1 DEF Floors
            <3>3. PICK z \in Cf:  Leq[z, y]
                BY <3>2, <1>6
            <3>4. SUFFICES z = fy
                BY <3>3
            <3> QED
                BY <3>1, <3>3, <3>2, <2>1
        <2> QED
            BY <2>2, <2>3
    <1>10. Card(Cf) = Card(C)
        <2>1. Card(Cf) <= Card(C)
            <3> HIDE DEF C
            <3> QED
                BY <1>9, <1>1, ImageOfFinite DEF Floors
        <2>2. Card(C) <= Card(Cf)
            BY ImageOfFinite DEF Hat
        <2> QED
            BY <2>1, <2>2, <1>1, FS_CardinalityType
    <1> QED
        BY <1>9, <1>10
--------------------------------------------------------------------------------
(* Effect of `Floor` on covers. *)


THEOREM FloorPreservesCover ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C, NEW Cf,
        LET
            Z == Support(Leq)
        IN
            /\ X \subseteq Z /\ Y \subseteq Z
            /\ C \subseteq Z
            /\ IsACompleteLattice(Leq)
            /\ Cf = Floors(C, X, Leq)
    PROVE
        IsACover(C, X, Leq) <=> IsACover(Cf, X, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
    <1> Cf \subseteq Z
        BY FloorsIsSubset
    <1>1. ASSUME IsACover(C, X, Leq)
          PROVE IsACover(Cf, X, Leq)
        <2>1. SUFFICES ASSUME NEW u \in X
                       PROVE \E y \in Cf:  Leq[u, y]
            BY DEF IsACover
        <2>2. PICK v \in C:  Leq[u, v]
            BY <1>1 DEF IsACover
        <2> DEFINE y == Floor(v, X, Leq)
        <2>3. Leq[u, y]
            BY <2>1, <2>2, FloorIsAboveThoseUnder
        <2>4. y \in Cf
            BY DEF Floors
        <2> QED
            BY <2>3, <2>4
    <1>2. ASSUME IsACover(Cf, X, Leq)
          PROVE IsACover(C, X, Leq)
        <2>1. SUFFICES ASSUME NEW u \in X
                       PROVE \E y \in C:  Leq[u, y]
            BY DEF IsACover
        <2>2. PICK v \in Cf:  Leq[u, v]
            BY <1>2 DEF IsACover
        <2>3. PICK y \in C:  v = Floor(y, X, Leq)
            BY DEF Floors
        <2>4. Leq[v, y]
            <3>1. v \in Z /\ y \in Z
                BY <2>2, <2>3
            <3>2. v = Floor(y, X, Leq)
                BY <2>3
            <3> QED
                BY <3>1, <3>2, FloorIsSmaller
        <2> QED
            <3>1. Leq[u, v]
                BY <2>2
            <3>2. Leq[v, y]
                BY <2>4
            <3>3. IsTransitive(Leq)
                BY LatticeProperties
            <3>4. u \in Z /\ v \in Z /\ y \in Z
                BY <2>1, <2>2, <2>3
            <3> QED
                BY <3>1, <3>2, <3>3, <3>4 DEF IsTransitive
    <1> QED
        BY <1>1, <1>2


(* A more general version of the next corollary can be proved about `Hat`,
by a proof similar to `MaxHatIsCoverToo`.
*)
COROLLARY UnfloorPreservesCover ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW Cf, NEW C,
        LET
            Z == Support(Leq)
        IN
            /\ X \subseteq Z /\ Y \subseteq Z
            /\ C \subseteq Z /\ Cf \subseteq Z
            /\ IsACompleteLattice(Leq)
            /\ IsACover(Cf, X, Leq)
            /\ Cf = Floors(C, X, Leq)
    PROVE
        IsACover(C, X, Leq)
    PROOF
    BY FloorPreservesCover

--------------------------------------------------------------------------------
(* Effect of `Floor` on minimal covers. *)


LEMMA FloorPreservesMinCover ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C,
        LET
            Z == Support(Leq)
        IN
            /\ IsACompleteLattice(Leq)
            /\ CardinalityAsCost(Z)
            /\ X \subseteq Z
            /\ Y \subseteq Z /\ IsFiniteSet(Y)  (* Finiteness of `Y`
                may be avoidable, but of `Yf` appears to be necessary. *)
            /\ C \subseteq Y
            /\ IsAMinCover(C, X, Y, Leq)
    PROVE
        LET
            Cf == Floors(C, X, Leq)
            Yf == Floors(Y, X, Leq)
        IN
            IsAMinCover(Cf, X, Yf, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Cf == Floors(C, X, Leq)
        Yf == Floors(Y, X, Leq)
        Card(S) == Cardinality(S)
    <1> IsFiniteSet(C)
        BY FS_Subset
    <1>1. /\ Cf \subseteq Z
          /\ Yf \subseteq Z
        BY FloorsIsSubset
    <1>2. /\ IsFiniteSet(Cf) /\ IsFiniteSet(Yf)
          /\ Card(Cf) <= Card(C)
        BY FloorsSmaller
    <1>3. /\ IsACover(C, X, Leq)
          /\ C \in SUBSET Y
          /\ \A r \in SUBSET Y:
                    /\ IsACover(r, X, Leq)
                    /\ CostLeq[ << r, C >> ]
                => CostLeq[ << C, r >> ]
        BY MinCoverProperties
    <1>4. SUFFICES ASSUME ~ IsAMinCover(Cf, X, Yf, Leq)
                   PROVE FALSE
        OBVIOUS
    <1>5. PICK Wf \in SUBSET Yf:
            /\ IsACover(Wf, X, Leq)
            /\ CostLeq[ << Wf, Cf >> ]
            /\ ~ CostLeq[ << Cf, Wf >> ]
        <2>1. Cf \in CoversOf(X, Yf, Leq)
            <3> IsACover(Cf, X, Leq)
                BY <1>3, FloorPreservesCover
            <3> Cf \in SUBSET Yf
                BY <1>3, FloorsIsSubset DEF Floors
            <3> QED
                BY DEF CoversOf
        <2> QED
            BY <1>4, <2>1, CheaperCoverExists
    <1>6. /\ IsFiniteSet(Wf)
          /\ Card(Wf) <= Card(Cf)
        <2> Card(Wf) <= Card(Cf)
            BY <1>5, <1>1 DEF CardinalityAsCost, CostLeq
        <2> IsFiniteSet(Wf)
            BY <1>5, <1>2, FS_Subset
        <2> QED
            OBVIOUS
    <1> DEFINE W == Unfloors(Wf, X, Y, Leq)
    <1>7. /\ W \subseteq Y
          /\ Wf = Floors(W, X, Leq)
        BY UnfloorSetProperties
    <1>8. W \subseteq Z /\ Wf \subseteq Z
        BY <1>1, <1>7
    <1>9. /\ IsFiniteSet(W)
          /\ Card(W) <= Card(Wf)
        BY <1>6, ImageOfFinite DEF Unfloors
    <1>10. CostLeq[ << C, W >> ]
        <2> /\ W \in SUBSET Y
            /\ IsACover(W, X, Leq)
            /\ CostLeq[ << W, C >> ]
            <3> IsACover(W, X, Leq)
                <4> IsUnfloor(W, Wf, X, Leq)
                    BY <1>7, <1>9 DEF IsUnfloor
                <4> QED
                    BY <1>7, <1>5, FloorPreservesCover
            <3> CostLeq[ << W, C >> ]
                <4> Card(W) <= Card(C)
                    BY <1>9, <1>6, <1>2, FS_CardinalityType
                <4> QED
                    BY <1>7 DEF CardinalityAsCost, CostLeq
            <3> QED
                BY <1>7
        <2> QED
            BY <1>3
    <1> IsFiniteSet(W) /\ IsFiniteSet(Wf) /\ IsFiniteSet(Cf)
        BY <1>9, <1>2, <1>6
    <1> USE FS_CardinalityType DEF CardinalityAsCost, CostLeq
    <1>11. Card(C) <= Card(W)
        <2> C \subseteq Z /\ W \subseteq Z
            BY <1>8
        <2> QED
            BY <1>10
    <1>12. Card(Wf) < Card(Cf)
        <2> Cf \subseteq Z /\ Wf \subseteq Z
            BY <1>8, <1>1
        <2> QED
            BY <1>5
    <1>13. Card(W) < Card(C)
        BY <1>2, <1>12, <1>9
    <1> QED
        BY <1>11, <1>13


LEMMA UnfloorPreservesMinCover ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW Cf, NEW C,
        LET
            Z == Support(Leq)
            Yf == Floors(Y, X, Leq)
        IN
            /\ IsACompleteLattice(Leq)
            /\ CardinalityAsCost(Z)
            /\ X \subseteq Z
            /\ Y \subseteq Z /\ IsFiniteSet(Y)
            /\ C \subseteq Y
            /\ IsAMinCover(Cf, X, Yf, Leq)
                (* Relation of unfloor `C` to `Cf`. *)
            /\ Cf = Floors(C, X, Leq)
            /\ Cardinality(C) <= Cardinality(Cf)
    PROVE
        IsAMinCover(C, X, Y, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Yf == Floors(Y, X, Leq)
        Card(S) == Cardinality(S)
    <1>1. /\ Yf \subseteq Z
          /\ IsFiniteSet(Yf)
        BY FloorsIsSubset, FloorsSmaller
    <1>2. /\ IsACover(Cf, X, Leq)
          /\ Cf \in SUBSET Yf
          /\ \A r \in SUBSET Yf:
                    /\ IsACover(r, X, Leq)
                    /\ CostLeq[ << r, Cf >> ]
                => CostLeq[ << Cf, r >> ]
        BY MinCoverProperties
    <1>3. SUFFICES ASSUME ~ IsAMinCover(C, X, Y, Leq)
                   PROVE FALSE
        OBVIOUS
    <1>4. PICK W \in SUBSET Y:
            /\ IsACover(W, X, Leq)
            /\ CostLeq[ << W, C >> ]
            /\ ~ CostLeq[ << C, W >> ]
        <2> C \in CoversOf(X, Y, Leq)
            <3> IsACover(C, X, Leq)
                BY <1>2, FloorPreservesCover
            <3> C \in SUBSET Y
                OBVIOUS
            <3> QED
                BY DEF CoversOf
        <2> QED
            BY <1>3, CheaperCoverExists
    <1> DEFINE Wf == Floors(W, X, Leq)
    <1>5. Wf \subseteq Yf
        BY <1>4 DEF Floors
    <1>6. IsACover(Wf, X, Leq)
        BY <1>4, FloorPreservesCover
    <1>7. W \subseteq Z /\ Wf \subseteq Z /\ Cf \subseteq Z
        BY <1>5, <1>4, <1>2, <1>1
    <1> /\ IsFiniteSet(W) /\ IsFiniteSet(Wf)
        /\ IsFiniteSet(C) /\ IsFiniteSet(Cf)
        BY <1>4, <1>2, <1>1, FS_Subset, FloorsSmaller
    <1> W \subseteq Z /\ Wf \subseteq Z /\ Cf \subseteq Z
        BY <1>4, <1>5, <1>1, <1>2
    <1> USE FS_CardinalityType DEF CardinalityAsCost, CostLeq
    <1>8. Card(C) <= Card(W)
        <2>1. Card(Wf) <= Card(W)
            BY FloorsSmaller
        <2>2. CostLeq[ << Wf, Cf >> ]
            BY <1>4, <2>1
        <2>3. CostLeq[ << Cf, Wf >> ]
            BY <1>2, <1>5, <1>6, <2>2
        <2>4. Card(Cf) <= Card(Wf)
            BY <2>3
        <2> QED
            BY <2>4, <2>1
    <1>9. Card(W) < Card(C)
        BY <1>4
    <1> QED
        BY <1>8, <1>9


(* FloorPreservesMinCover and UnfloorPreservesMinCover combined.  *)
THEOREM MinCoverPreservedIfFloors ==
    ASSUME
        NEW Leq, NEW X, NEW Y, NEW C, NEW Cf,
        LET
            Z == Support(Leq)
        IN
            /\ IsACompleteLattice(Leq)
            /\ CardinalityAsCost(Z)
            /\ X \subseteq Z
            /\ Y \subseteq Z /\ IsFiniteSet(Y)
            /\ C \subseteq Y
            /\ Cf = Floors(C, X, Leq)
            /\ Cardinality(C) <= Cardinality(Cf)
    PROVE
        LET
            Yf == Floors(Y, X, Leq)
        IN
            /\ IsAMinCover(C, X, Y, Leq) <=> IsAMinCover(Cf, X, Yf, Leq)
            /\ Cardinality(C) = Cardinality(Cf)
    PROOF
    <1> DEFINE
        Yf == Floors(Y, X, Leq)
    <1>1. IsFiniteSet(C) /\ IsFiniteSet(Cf)
        <2>1. (C \subseteq Y) /\ IsFiniteSet(Y)
            OBVIOUS
        <2>2. IsFiniteSet(C)
            BY <2>1, FS_Subset
        <2>3. Cf = Floors(C, X, Leq)
            OBVIOUS
        <2>4. IsFiniteSet(Cf)
            BY <2>2, <2>3, ImageOfFinite DEF Floors
        <2> QED
            BY <2>2, <2>4
    <1>2. /\ Cardinality(C) \in Nat
          /\ Cardinality(Cf) \in Nat
        BY <1>1, FS_CardinalityType
    <1>3. ASSUME IsAMinCover(C, X, Y, Leq)
          PROVE IsAMinCover(Cf, X, Yf, Leq)
        BY <1>3, FloorPreservesMinCover DEF Yf
    <1>4. ASSUME IsAMinCover(Cf, X, Yf, Leq)
          PROVE IsAMinCover(C, X, Y, Leq)
        BY <1>4, UnfloorPreservesMinCover DEF Yf
    <1>5. Cardinality(C) = Cardinality(Cf)
        <2> DEFINE
            k == Cardinality(C)
            m == Cardinality(Cf)
        <2>1. k <= m
            BY DEF k, m
        <2>2. m <= k
            BY <1>1, ImageOfFinite DEF k, m, Floors
        <2>3. (k \in Nat) /\ (m \in Nat)
            BY <1>2
        <2> HIDE DEF k, m
        <2>4. ASSUME
                (k <= m) /\ (m <= k)
              PROVE k = m
            BY <2>3, <2>4
        <2> QED
            BY <2>1, <2>2, <2>4 DEF k, m
    <1> QED
        BY <1>3, <1>4, <1>5

================================================================================
(* Proofs checked with TLAPS version 1.4.3 *)
