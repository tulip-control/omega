----------------------------- MODULE Optimization ------------------------------
(* Generic notions of optimization and binary relations as functions.

- minimal, maximal, minimum, maximum elements
- reflexive, irreflexive, transitive, symmetric, antisymmetric relations
- antichains, chains
- properties of the above

Author:  Ioannis Filippidis

--------------------------------------------------------------------------------
Copyright 2017 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
*)
EXTENDS
    FiniteSetFacts,
    Integers,
    WellFoundedInduction


IsAFunction(f) == f = [x \in DOMAIN f |-> f[x]]

Support(R) == { p[1]:  p \in DOMAIN R } \cup { p[2]:  p \in DOMAIN R }

IsReflexive(R) == LET S == Support(R)
                  IN \A x \in S:  R[x, x]

IsIrreflexive(R) == LET S == Support(R)
                    IN \A x \in S:  ~ R[x, x]

IsTransitive(R) == LET S == Support(R)
                   IN \A x, y, z \in S:  (R[x, y] /\ R[y, z]) => R[x, z]

IsSymmetric(R) == LET S == Support(R)
                  IN \A x, y \in S:  R[x, y] => R[y, x]

IsAntiSymmetric(R) == LET S == Support(R)
                      IN \A x, y \in S:  (R[x, y] /\ (x # y)) => ~ R[y, x]

(* `S` is a set of pairwise comparable elements (totality). *)
IsChain(S, Leq) == \A x, y \in S:  Leq[x, y] \/ Leq[y, x]

(* `S` is a set of pairwise incomparable elements. *)
IsAntiChain(S, Leq) == \A x, y \in S:
    (x # y) => ( ~ Leq[x, y]  /\  ~ Leq[y, x] )
--------------------------------------------------------------------------------
(* Optimization *)

(* When the minimum exists, it is unique, similarly for the maximum. *)
IsMinimum(r, S, Leq) == /\ r \in S
                        /\ \A u \in S \ {r}:  Leq[r, u]

IsMaximum(r, S, Leq) == /\ r \in S
                        /\ \A u \in S \ {r}:  Leq[u, r]

(* This definition requires that `Leq` be reflexive,
so it applies to partial orders.
*)
IsMinimalRefl(r, S, Leq) == /\ r \in S
                            /\ \A u \in S \ {r}:  ~ Leq[u, r]

IsMaximalRefl(r, S, Leq) == /\ r \in S
                            /\ \A u \in S \ {r}:  ~ Leq[r, u]

(* Most general definition, applies even if `Leq` is not anti-symmetric,
so also to preorders.
*)
IsMinimal(r, S, Leq) == /\ r \in S
                        /\ \A u \in S:  Leq[u, r] => Leq[r, u]

IsMaximal(r, S, Leq) == /\ r \in S
                        /\ \A u \in S:  Leq[r, u] => Leq[u, r]

(* This definition is used in the implementation, because the BDD of
   Eq[u, r] turns out to be (much) smaller than the BDD of Leq[r, u]. *)
IsAMinimumAlt(r, S, Leq, Eq) == /\ r \in S
                                /\ \A u \in S:  Leq[u, r] => Eq[u, r]

(* If a minimum does exist, then it is unique, so clearly "minima"
refers to minimal elements. In presence of the minimum, `Minima` is
a singleton.
*)
Minima(S, Leq) == { x \in S:  IsMinimal(x, S, Leq) }
Maxima(S, Leq) == { x \in S:  IsMaximal(x, S, Leq) }

IndicatorFuncToRel(f) == { x \in DOMAIN f:  f[x] = TRUE }
IrreflexiveFrom(Leq) ==
    LET
        S == Support(Leq)
    IN
        [t \in S \X S |-> IF t[1] = t[2] THEN FALSE ELSE Leq[t]]

--------------------------------------------------------------------------------

(* Definition of `IsMaximal` restated as a theorem. *)
LEMMA MaxProperties ==
    ASSUME
        NEW Leq, NEW S, NEW x, NEW other,
        IsMaximal(x, S, Leq)
    PROVE
        /\ x \in S
        /\ (other \in S  /\  Leq[x, other]) => Leq[other, x]
    PROOF
    BY DEF IsMaximal


COROLLARY MaximaProperties ==
    ASSUME
        NEW Leq, NEW S, NEW x, NEW other,
        x \in Maxima(S, Leq)
    PROVE
        /\ x \in S
        /\ (other \in S  /\  Leq[x, other]) => Leq[other, x]
    PROOF
    BY MaxProperties DEF Maxima


THEOREM MaxIsIdempotent ==
    ASSUME NEW S, NEW Leq
    PROVE LET Max(Q) == Maxima(Q, Leq)
          IN Max(Max(S)) = Max(S)
    PROOF
    BY DEF Maxima, IsMaximal


THEOREM MaxIsSubset ==
    ASSUME NEW S, NEW Leq
    PROVE Maxima(S, Leq) \subseteq S
    PROOF
    BY DEF Maxima


THEOREM MaxSmaller ==
    ASSUME
        NEW S, NEW Leq,
        IsFiniteSet(S)
    PROVE
        LET
            Max == Maxima(S, Leq)
        IN
            /\ IsFiniteSet(Max)
            /\ Cardinality(Max) <= Cardinality(S)
    PROOF
    BY MaxIsSubset, FS_Subset


(* S = Max(S) when S is an antichain. *)
THEOREM MaxSame ==
    ASSUME
        NEW S, NEW Leq,
        IsFiniteSet(S),
        Cardinality(S) = Cardinality(Maxima(S, Leq))
    PROVE
        S = Maxima(S, Leq)
    PROOF
    <1> DEFINE
        Max == Maxima(S, Leq)
        Card(R) == Cardinality(R)
    <1>1. SUFFICES ASSUME S # Max
                   PROVE FALSE
        OBVIOUS
    <1>2. /\ Max \subseteq S
          /\ Max # S
        BY MaxIsSubset, <1>1
    <1>3. Card(Max) < Card(S)
        BY <1>2, FS_Subset
    <1> QED
        BY <1>3


THEOREM MaximaIsAntiChain ==
    ASSUME
        NEW S, NEW Leq,
        IsAntiSymmetric(Leq),
        S \subseteq Support(Leq),
        S = Maxima(S, Leq)
    PROVE
        IsAntiChain(S, Leq)
    PROOF
    <1>1. SUFFICES ASSUME NEW x \in S, NEW y \in S,
                          /\ x # y
                          /\ Leq[x, y]
                   PROVE FALSE
        BY DEF IsAntiChain
    <1>2. ~ Leq[y, x]
        BY <1>1 DEF IsAntiSymmetric
    <1>3. Leq[y, x]
        <2>1. IsMaximal(x, S, Leq)
            BY <1>1 DEF Maxima
        <2> QED
            BY <1>1, <2>1 DEF IsMaximal
    <1> QED
        BY <1>2, <1>3


THEOREM AntiChainIsMaxima ==
    ASSUME
        NEW S, NEW Leq,
        /\ IsReflexive(Leq)
        /\ IsAntiChain(S, Leq)
    PROVE
        S = Maxima(S, Leq)
    PROOF
    <1>1. SUFFICES ASSUME NEW x \in S, NEW y \in S,
                          Leq[y, x]
                   PROVE Leq[x, y]
        BY DEF Maxima, IsMaximal
    <1>2. CASE x = y
        BY <1>1, <1>2 DEF IsReflexive
    <1>3. CASE x # y
        BY <1>1, <1>3 DEF IsAntiChain
    <1> QED
        BY <1>2, <1>3


THEOREM EquivDefsOfMin ==
    ASSUME NEW S, NEW Leq, NEW Eq,
           \A u, r \in S:  Eq[u, r] \equiv (Leq[u, r] /\ Leq[r, u])
    PROVE \A r \in S:
            IsMinimal(r, S, Leq) \equiv IsAMinimumAlt(r, S, Leq, Eq)
    PROOF
    BY DEF IsMinimal, IsAMinimumAlt


(* If x \in S (so S is nonempty), and x is not a minimum,
then some y \in S \ {x} is smaller than x.
*)
THEOREM SmallerExists ==
    ASSUME
        NEW Leq, NEW S, NEW x \in S,
        ~ IsMinimal(x, S, Leq)
    PROVE
        \E y \in S:  /\ y # x
                     /\ Leq[y, x]
                     /\ ~ Leq[x, y]
    PROOF
    BY DEF IsMinimal


THEOREM LargerExists ==
    ASSUME
        NEW Leq, NEW S, NEW x \in S,
        ~ IsMaximal(x, S, Leq)
    PROVE
        \E y \in S:  /\ y # x
                     /\ Leq[x, y]
                     /\ ~ Leq[y, x]
    PROOF
    BY DEF IsMaximal


THEOREM StrictSubsetOfFiniteWellFoundedOnSubsets ==
    ASSUME
        NEW S,
        IsFiniteSet(S)
    PROVE
        LET
            LeqRel == StrictSubsetOrdering(S)
        IN
            IsWellFoundedOn(LeqRel, SUBSET S)
    PROOF
    BY FS_StrictSubsetOrderingWellFounded, FS_FiniteSubsetsOfFinite

--------------------------------------------------------------------------------

PROPOSITION IndicatorTrueOnRel ==
    ASSUME
        NEW f
    PROVE
        \A x \in IndicatorFuncToRel(f):  f[x]
    PROOF
    BY DEF IndicatorFuncToRel


PROPOSITION IndicatorEquivRel ==
    ASSUME
        NEW f, NEW x
    PROVE
        LET R == IndicatorFuncToRel(f)
        IN (x \in R) <=> /\ x \in DOMAIN f
                         /\ f[x]
    PROOF
    BY DEF IndicatorFuncToRel


PROPOSITION SupportOfSymmetricDomain ==
    ASSUME
        NEW Leq, NEW S,
        (DOMAIN Leq) = (S \X S)
    PROVE
        S = Support(Leq)
    PROOF
    <1> DEFINE Z == Support(Leq)
    <1>1. Z \subseteq S
        BY DEF Support
    <1>2. S \subseteq Z
        <3> SUFFICES ASSUME NEW u \in S
                     PROVE u \in Z
            OBVIOUS
        <3> QED
            BY DEF Support
    <1> QED
        BY <1>1, <1>2


PROPOSITION LtDomainIsSupportSquared ==
    ASSUME
        NEW Leq
    PROVE
        LET
            Lt == IrreflexiveFrom(Leq)
            S == Support(Lt)
        IN (S \X S) = DOMAIN Lt
    PROOF
    <1> DEFINE Lt == IrreflexiveFrom(Leq)
    <1>1. PICK S:  (S \X S) = DOMAIN Lt
        BY DEF IrreflexiveFrom
    <1>2. S = Support(Lt)
        BY <1>1, SupportOfSymmetricDomain
    <1> QED
        BY <1>1, <1>2


PROPOSITION LtHasSameSupport ==
    ASSUME
        NEW Leq
    PROVE
        LET Lt == IrreflexiveFrom(Leq)
        IN Support(Lt) = Support(Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Lt == IrreflexiveFrom(Leq)
    <1>1. Support(Lt) \subseteq Z
        BY DEF IrreflexiveFrom, Support
    <1>2. Z \subseteq Support(Lt)
        <2>1. \A u \in Z:  \E p \in DOMAIN Lt:  p[1] = u
            BY DEF IrreflexiveFrom
        <2>2. Z \subseteq { p[1]:  p \in DOMAIN Lt}
            BY <2>1
        <2> QED
            BY <2>2 DEF Support
    <1> QED
        BY <1>1, <1>2


PROPOSITION LtHasSameDomain ==
    ASSUME
        NEW Leq,
        \E S:  DOMAIN Leq = (S \X S)
    PROVE
        LET Lt == IrreflexiveFrom(Leq)
        IN DOMAIN Leq = DOMAIN Lt
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Lt == IrreflexiveFrom(Leq)
    <1>1. PICK S:  DOMAIN Leq = (S \X S)
        OBVIOUS
    <1>2. S = Z
        <2>1. ASSUME NEW u \in S
                     PROVE u \in Z
            BY <1>1 DEF Support
        <2>2. ASSUME NEW u \in Z
                     PROVE u \in S
            <3>1. PICK p \in DOMAIN Leq:  \/ p[1] = u
                                          \/ p[2] = u
                BY DEF Support
            <3>2. /\ p[1] \in S
                  /\ p[2] \in S
                BY <1>1
            <3> QED
                BY <3>1, <3>2
        <2> QED
            BY <2>1, <2>2
    <1>3. DOMAIN Lt = (Z \X Z)
        BY LtHasSameSupport DEF IrreflexiveFrom
    <1> QED
        BY <1>1, <1>2, <1>3


PROPOSITION LtIsIrreflexive ==
    ASSUME
        NEW Leq
    PROVE
        LET Lt == IrreflexiveFrom(Leq)
        IN IsIrreflexive(Lt)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Lt == IrreflexiveFrom(Leq)
    <1>1. SUFFICES ASSUME NEW x \in Z
                   PROVE ~ Lt[x, x]
        <2> Support(Lt) = Support(Leq)
           BY LtHasSameSupport
        <2> QED
            BY <1>1 DEF IsIrreflexive
    <1>2. << x, x >> \in Z \X Z
        BY <1>1
    <1> QED
        BY <1>2 DEF IrreflexiveFrom


PROPOSITION LtIsTransitive ==
    ASSUME
        NEW Leq,
        /\ IsAntiSymmetric(Leq)
        /\ IsTransitive(Leq)
    PROVE
        LET Lt == IrreflexiveFrom(Leq)
        IN IsTransitive(Lt)
    PROOF
    <1> DEFINE
        Lt == IrreflexiveFrom(Leq)
        Z == Support(Leq)
        W == Support(Lt)
    <1>1. Z = W
        BY LtHasSameSupport
    <1>2. ASSUME NEW x \in W, NEW y \in W
          PROVE << x, y >> \in DOMAIN Lt
        <2> (W \X W) = DOMAIN Lt
            BY LtDomainIsSupportSquared
        <2> << x, y >> \in (W \X W)
            OBVIOUS
        <2> QED
            OBVIOUS
    <1>3. SUFFICES ASSUME NEW x \in W, NEW y \in W, NEW z \in W,
                          Lt[x, y] /\ Lt[y, z]
                   PROVE Lt[x, z]
        BY <1>3 DEF IsTransitive
    <1>4. x # y
        <2>1. SUFFICES ASSUME x = y
                       PROVE FALSE
            OBVIOUS
        <2>2. << x, x >> \in DOMAIN Lt
            BY <1>2
        <2>3. Lt[x, x]
            BY <1>3, <2>1
        <2> QED
            BY <2>2, <2>3 DEF IrreflexiveFrom
    <1>5. Leq[x, y]
        <2>1. << x, y >> \in DOMAIN Lt
            BY <1>2
        <2>2. Lt[x, y]
            BY <1>3
        <2> QED
            BY <2>1, <2>2 DEF IrreflexiveFrom
    <1>6. Leq[y, z]
        <2>1. << y, z >> \in DOMAIN Lt
            BY <1>2
        <2>2. Lt[y, z]
            BY <1>3
        <2> QED
            BY <2>1, <2>2 DEF IrreflexiveFrom
    <1>7. Leq[x, z]
        <2>1. /\ x \in Z
              /\ y \in Z
              /\ z \in Z
            BY <1>1, <1>3
        <2> QED
            BY <2>1, <1>5, <1>6 DEF IsTransitive
    <1> QED
        <2>1. << x, z >> \in DOMAIN Lt
            BY <1>2
        <2>2. x # z
            <3>1. SUFFICES ASSUME x = z
                           PROVE FALSE
                OBVIOUS
            <3>2. Leq[x, y] /\ Leq[y, x]
                BY <1>5, <1>6, <3>1
            <3>3. ~ Leq[y, x]
                <4>1. (x \in Z) /\ (y \in Z)
                    BY <1>3, <1>1
                <4>2. x # y
                    BY <1>4
                <4>3. Leq[x, y]
                    BY <3>2
                <4> QED
                    BY <4>1, <4>2, <4>3 DEF IsAntiSymmetric
            <3> QED
                BY <3>2, <3>3
        <2> QED
            BY <2>1, <2>2, <1>7 DEF IrreflexiveFrom


PROPOSITION FiniteLatticeInducesWellFounded ==
    ASSUME
        NEW Leq, NEW S,
        LET
            Z == Support(Leq)
        IN
            /\ IsFiniteSet(S)
            /\ IsTransitive(Leq)
            /\ IsAntiSymmetric(Leq)
            /\ S \subseteq Z
    PROVE
        LET
            Z == Support(Leq)
            Lt == IrreflexiveFrom(Leq)
            R == IndicatorFuncToRel(Lt)
        IN
            IsWellFoundedOn(R, S)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Lt == IrreflexiveFrom(Leq)
        W == Support(Lt)
        R == IndicatorFuncToRel(Lt)
    <1>1. IsIrreflexive(Lt)
        BY LtIsIrreflexive
    <1>2. IsTransitive(Lt)
        BY LtIsTransitive
    <1>3. \A x \in Z:  << x, x >> \notin R
        <2>1. SUFFICES ASSUME NEW x \in Z
                       PROVE << x, x >> \notin R
            OBVIOUS
        <2>2. ~ Lt[x, x]
            <3> << x, x >> \in (Z \X Z)
                OBVIOUS
            <3> QED
                BY DEF IrreflexiveFrom
        <2> QED
            BY <2>2 DEF IndicatorFuncToRel
    <1>4. SUFFICES ASSUME ~ IsWellFoundedOn(R, S)
                   PROVE FALSE
        OBVIOUS
    <1>5. PICK f \in [Nat -> S]:
            \A n \in Nat:  << f[n + 1], f[n] >> \in R
        BY <1>4 DEF IsWellFoundedOn
    <1>6. \A n \in Nat:  f[n] \in W
        BY <1>5, LtHasSameSupport
    <1>7. ASSUME NEW i \in Nat, NEW j \in Nat,
                 i < j
          PROVE << f[j], f[i] >> \in R
        <2>1. \A n \in Nat:  Lt[f[n + 1], f[n]]
            BY <1>5, IndicatorEquivRel
        <2>2. \A n \in Nat:  Lt[f[i + n + 1], f[i]]
            <3>1. Lt[f[i + 1], f[i]]
                BY <2>1, <1>7
            <3>2. ASSUME NEW n \in Nat,
                         Lt[f[i + n + 1], f[i]]
                  PROVE Lt[f[i + n + 2], f[i]]
                <4>1. k == i + n + 1
                <4>2. Lt[f[k + 1], f[k]]
                    BY <2>1, <3>2
                <4>3. Lt[f[k], f[i]]
                    BY <3>2
                <4>4. SUFFICES Lt[f[k + 1], f[i]]
                    OBVIOUS
                <4>5. /\ f[k] \in W
                      /\ f[k + 1] \in W
                      /\ f[i] \in W
                    BY <1>6
                <4> QED
                    BY <4>2, <4>3, <4>5, <1>2 DEF IsTransitive
            <3> QED
                BY <3>1, <3>2, NatInduction
        <2>3. Lt[f[i + (j - i - 1) + 1], f[i]]
            <3>1. n == j - i - 1
            <3>2. n \in Nat
                BY <1>7
            <3>3. Lt[f[i + n + 1], f[i]]
                BY <3>2, <2>2
            <3> QED
                BY <3>3
        <2>4. Lt[f[j], f[i]]
            BY <1>7, <2>3
        <2>5. << f[j], f[i] >> \in DOMAIN Lt
            <3> << f[j], f[i] >> \in (W \X W)
                BY <1>6
            <3> W = Z
                BY LtHasSameSupport
            <3> QED
                BY LtDomainIsSupportSquared
        <2> QED
            BY <2>4, <2>5, IndicatorEquivRel
    <1>8. \A i, j \in Nat:  (i # j) => (f[i] # f[j])
        <2>1. SUFFICES ASSUME NEW i \in Nat, NEW j \in Nat,
                              i < j
                       PROVE f[i] # f[j]
            OBVIOUS
        <2>2. << f[j], f[i] >> \in R
            BY <2>1, <1>7
        <2> QED
            BY <2>2, <1>6, <1>3, LtHasSameSupport
    <1>9. PICK k \in Nat:  k = Cardinality(S)
        BY FS_CardinalityType
    <1> DEFINE
        m == k + 1
        D == 1..m
        T == {f[n]:  n \in D}
    <1>10. \A i, j \in D:  (i # j) => f[i] # f[j]
        BY <1>9, <1>8
    <1>11. ExistsBijection(D, T)
        <2>1. g == [n \in D |-> f[n]]
        <2>2. g \in [D -> T]
            OBVIOUS
        <2>3. g \in Injection(D, T)
            BY <1>10 DEF Injection
        <2>4. g \in Surjection(D, T)
            BY DEF Surjection
        <2>5. g \in Bijection(D, T)
            BY <2>3, <2>4 DEF Bijection
        <2> QED
            BY <2>5 DEF ExistsBijection
    <1>12. /\ IsFiniteSet(T)
           /\ m = Cardinality(T)
        BY <1>11, FS_NatBijection, FS_CountingElements
    <1>13. /\ T \subseteq S
           /\ T # S
        BY <1>8
    <1>14. Cardinality(T) < Cardinality(S)
        <2>1. /\ Cardinality(T) <= Cardinality(S)
              /\ (Cardinality(T) = Cardinality(S)) => (S = T)
            BY <1>13, FS_Subset
        <2> QED
            BY <2>1, <1>13
    <1> QED
        <2>1. m < k
            BY <1>9, <1>12, <1>14
        <2> QED
            BY <2>1


THEOREM FiniteSetHasMinimal ==
    ASSUME
        NEW Leq, NEW S,
        LET
            Z == Support(Leq)
        IN
            /\ IsTransitive(Leq)
            /\ IsAntiSymmetric(Leq)
            /\ IsFiniteSet(S)
            /\ S \subseteq Z
            /\ S # {}
    PROVE
        \E v \in S:  IsMinimal(v, S, Leq)
    PROOF
    <1> DEFINE
        Z == Support(Leq)
        Lt == IrreflexiveFrom(Leq)
        W == Support(Lt)
        R == IndicatorFuncToRel(Lt)
    <1>1. S \subseteq W
        BY LtHasSameSupport
    <1>2. IsWellFoundedOn(R, S)
        BY FiniteLatticeInducesWellFounded
    <1>3. PICK v \in S:  \A u \in S:  << u, v >> \notin R
        BY <1>2, WFMin
    <1>4. \A u \in S:  ~ Lt[u, v]
        <2>1. SUFFICES ASSUME NEW u \in S
                       PROVE ~ Lt[u, v]
            OBVIOUS
        <2>2. /\ u \in W
              /\ v \in W
            BY <1>3, <2>1, <1>1
        <2>3. << u, v >> \notin R
            BY <1>3
        <2>4. << u, v >> \in DOMAIN Lt
            <3> << u, v >> \in (W \X W)
                BY <2>2
            <3> QED
                BY LtDomainIsSupportSquared
        <2> QED
            BY <2>3, <2>4, IndicatorEquivRel
    <1>5. \A u \in S \ {v}:  ~ Leq[u, v]
        <2> SUFFICES ASSUME NEW u \in S \ {v}
                     PROVE ~ Leq[u, v]
            OBVIOUS
        <2>1. << u, v >> \in Z \X Z
            BY <1>1, LtHasSameSupport
        <2>2. Lt[u, v] = Leq[u, v]
            BY <2>1 DEF IrreflexiveFrom
        <2> QED
            BY <1>4, <2>2
    <1> QED
        BY <1>5 DEF IsMinimal


THEOREM HasSomeMinimalBelow ==
    ASSUME
        NEW Leq, NEW S, NEW u \in S,
        LET
            Z == Support(Leq)
        IN
            /\ IsFiniteSet(Z)
            /\ IsReflexive(Leq)
            /\ IsTransitive(Leq)
            /\ IsAntiSymmetric(Leq)
            /\ S \subseteq Z
    PROVE
        \E v \in S:  /\ Leq[v, u]
                     /\ IsMinimal(v, S, Leq)
    PROOF
    <1> DEFINE
        R == { r \in S:  Leq[r, u] }
        Z == Support(Leq)
    <1>1. u \in R
        BY DEF IsReflexive
    <1>2. IsFiniteSet(R)
        BY FS_Subset DEF R
    <1>3. PICK v \in R:  IsMinimal(v, R, Leq)
        BY <1>1, <1>2, FiniteSetHasMinimal
    <1>4. SUFFICES IsMinimal(v, S, Leq)
        <2>1. Leq[v, u]
            BY <1>3 DEF R
        <2> QED
            BY <2>1
    <1>5. SUFFICES ASSUME ~ IsMinimal(v, S, Leq)
                   PROVE FALSE
        OBVIOUS
    <1>6. PICK w \in S \ {v}:  /\ Leq[w, v]
                               /\ ~ Leq[v, w]
        BY <1>5, SmallerExists
    <1>7. w \in R
        BY <1>6, <1>3 DEF IsTransitive
    <1> QED
        BY <1>3, <1>7, <1>6 DEF IsMinimal
================================================================================
(* Proofs checked with TLAPS version 1.4.3 *)


--------------------------------------------------------------------------------
(*
The definitions above use bounded quantifiers to enable using TLC.
Also, sets instead of predicates reduce the amount of nesting in the
definitions (flat is better than nested). The same definitions are
possible using higher-order operators and unbounded quantifiers.
These are given below.
*)
--------------------------------------------------------------------------------
(* Defining IsMinimal and IsMaximal using Leq *)
IsMinimal(r, IsAMember(_), Leq) ==
    /\ IsAMember(r)
    /\ \A u:  \/ ~ IsAMember(u)  (* outside the collection, or *)
              \/ ~ Leq[u, r]  (* r no smaller than u, or *)
              \/ Leq[r, u]  (* r smaller than or equal to u *)

IsAMinimumAlt(r, IsAMember(_), Leq, Eq) ==
    /\ IsAMember(r)
    /\ \A u:  \/ ~ IsAMember(u)
              \/ ~ Leq[u, r]
              \/ Eq[u, r]

IsMaximal(r, IsAMember(_), Leq) ==
    /\ IsAMember(r)
    /\ \A u:  \/ ~ IsAMember(u)
              \/ ~ Leq[r, u]
              \/ Leq[u, r]

IsAMaximumAlt(r, IsAMember(_), Leq, Eq) ==
    /\ IsAMember(r)
    /\ \A u:  \/ ~ IsAMember(u)
              \/ ~ Leq[r, u]
              \/ Eq[r, u]

(*
Design choices:

1. operator vs function for Leq
2. Leq as argument vs as CONSTANT
3. Leq vs Geq
4. expressing Min using Max
5. IsAMember as operator vs set containment
*)
--------------------------------------------------------------------------------
(* Expressing IsMinimal using IsMaximal *)

IsMinimal(r, IsAMember, Leq) \equiv
    /\ IsAMember(r)
    /\ \A u:  \/ ~ IsAMember(u)
              \/ ~ Leq[u, r]
              \/ Leq[r, u]
\equiv
    LET Geq[<< a, b >> \in DOMAIN Leq] == Leq[b, a]
    IN /\ IsAMember(r)
       /\ \A u:  \/ ~ IsAMember(u)
                 \/ ~ Geq[r, u]
                 \/ Geq[u, r]
\equiv
    LET Geq[<< a, b >> \in DOMAIN Leq] == Leq[b, a]
    IN IsMaximal(r, IsAMember, Geq)

(* The above indicates a possible alternative definition for IsMinimal. *)
--------------------------------------------------------------------------------
(* Defining IsMinimal and IsMaximal using Geq *)

IsMinimal(r, IsAMember(_), Geq) ==
    /\ IsAMember(r)
    /\ A u:  \/ ~ IsAMember(u)
             \/ ~ Geq[r, u]
             \/ Geq[u, r]

IsMaximal(r, IsAMember(_), Geq) ==
    /\ IsAMember(r)
    /\ \A u:  \/ ~ IsAMember(u)
              \/ ~ Geq[u, r]
              \/ Geq[r, u]
--------------------------------------------------------------------------------
(* Design note on defining maxima *)

THEOREM
    TRUE \equiv \/ c >= u
                \/ ~ (c >= u)

         \equiv \/ c >= u
                \/ ~ (c >= u) /\ TRUE

         \equiv \/ c >= u
                \/ ~ (c >= u) /\ \/ u >= c
                                 \/ ~ (u >= c)

         \equiv \/ c >= u  (* c at least as large as u *)
                \/ ~ (c >= u) /\ (u >= c)  (* u strictly larger than c *)
                \/ ~ (c >= u) /\ ~ (u >= c)  (* c and u incomparable *)

(* We want cases 1 and 3 only, so *)

\/ c >= u
\/ ~ (c >= u) /\ ~ (u >= c)
\equiv
\/ c >= u
\/ ~ (u >= c)


(* It can also be shown that:

((p <= q) => (p = q))  \equiv  ~ (p <= q  /\  p # q)
*)
