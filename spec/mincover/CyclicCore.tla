------------------------------- MODULE CyclicCore ------------------------------
(* Correctness of the cyclic core computation.

This algorithm was originally proposed in [1].

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
    Integers,
    Lattices,
    MinCover,
    Optimization,
    TLAPS


CONSTANTS
    Leq,
    Xinit, Yinit

VARIABLES
    X,  (* Current set to be covered. *)
    Y,  (* Set of elements available for covering X. *)
    E,  (* Accumulates essential elements. *)
    Xold, Yold,  (* History variables used to detect fixpoint. *)
    i  (* Program counter. *)


Z == Support(Leq)
ASSUMPTION CostIsCard ==
    Cost = [cover \in SUBSET Z |-> Cardinality(cover)]

--------------------------------------------------------------------------------
(* Definitions for convenience. *)
RowRed(u, v) == MaxCeilings(u, v, Leq)
ColRed(u, v) == MaxFloors(v, u, Leq)


Card(S) == Cardinality(S)  (* shorthand *)
--------------------------------------------------------------------------------

InitIsFeasible == \E C:  IsACoverFrom(C, Xinit, Yinit, Leq)

ASSUMPTION ProblemInput ==
    /\ IsACompleteLattice(Leq)
    /\ IsFiniteSet(Z)
    /\ Xinit \subseteq Z
    /\ Yinit \subseteq Z
    /\ InitIsFeasible


THEOREM HaveCardAsCost == CardinalityAsCost(Z)
PROOF
BY CostIsCard DEF CardinalityAsCost


THEOREM LeqTransitive == IsTransitive(Leq)
PROOF
BY ProblemInput DEF IsACompleteLattice,
    IsACompleteLattice, IsAPartialOrder


THEOREM LeqIsPor == IsAPartialOrder(Leq)
PROOF
BY ProblemInput DEF IsACompleteLattice

--------------------------------------------------------------------------------
(* Specification of cyclic core computation. *)

TypeInv ==
    /\ X \in SUBSET Z
    /\ Y \in SUBSET Z
    /\ E \in SUBSET Z
    /\ Xold \in SUBSET Z
    /\ Yold \in SUBSET Z
    /\ i \in 1..3

Init ==
    /\ X = Xinit
    /\ Y = Yinit
    /\ E = {}
    /\ Xold = {}
    /\ Yold = {}
    /\ i = 1

ReduceColumns ==
    /\ (i = 1) /\ (i' = 2)
    /\ Y' = ColRed(X, Y)
    /\ Xold' = X
    /\ Yold' = Y
    /\ UNCHANGED << X, E >>

ReduceRows ==
    /\ (i = 2) /\ (i' = 3)
    /\ X' = RowRed(X, Y)
    /\ UNCHANGED << Y, E, Xold, Yold >>

RemoveEssential ==
    /\ (i = 3) /\ (i' = 1)
    /\ LET
          Ess == X \cap Y  (* Essential elements. *)
       IN
          /\ X' = X \ Ess
          /\ Y' = Y \ Ess
          /\ E' = E \cup Ess
    /\ UNCHANGED << Xold, Yold >>

Next ==
    \/ ReduceColumns
    \/ ReduceRows
    \/ RemoveEssential

vars == << X, Y, E, Xold, Yold, i >>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------------------------------------------------------------

IsFeasible == \E C:  IsAMinCover(C, X, Y, Leq)
HatIsMinCover ==
    \A C, H:
        \/ ~ /\ IsAMinCover(C, X, Y, Leq)
             /\ IsAHat(H, C \cup E, Yinit, Leq)
        \/ /\ IsAMinCover(H, Xinit, Yinit, Leq)
           /\ Cardinality(H) = Cardinality(C) + Cardinality(E)

Useful == [](IsFeasible /\ HatIsMinCover)
ReachesFixpoint == <>[][FALSE]_<< X, Y >>

--------------------------------------------------------------------------------
(* Invariants. *)


THEOREM TypeOK == Spec => []TypeInv
PROOF
<1>1. ASSUME Init
      PROVE TypeInv
    <2>1. {} \in SUBSET Z
        OBVIOUS
    <2>2. /\ X = Xinit /\ Y = Yinit /\ i = 1
          /\ E = {} /\ Xold = {} /\ Yold = {}
        BY <1>1 DEF Init
    <2>3. Xinit \in SUBSET Z /\ Yinit \in SUBSET Z
        BY ProblemInput
    <2>4. X \in SUBSET Z /\ Y \in SUBSET Z
        BY <2>2, <2>3
    <2>5. /\ E \in SUBSET Z
          /\ Xold \in SUBSET Z /\ Yold \in SUBSET Z
        BY <2>1, <2>2
    <2>6. i \in 1..3
        BY <2>2
    <2> QED
        BY <2>4, <2>5, <2>6 DEF TypeInv
<1>2. ASSUME TypeInv /\ Next
      PROVE TypeInv'
    <2>4. /\ X \in SUBSET Z /\ Y \in SUBSET Z
          /\ E \in SUBSET Z
          /\ Xold \in SUBSET Z /\ Yold \in SUBSET Z
          /\ i \in 1..3
        BY <1>2 DEF TypeInv
    <2>1. ASSUME ReduceColumns
          PROVE TypeInv'
        <3>2. /\ (i = 1) /\ (i' = 2)
              /\ Y' = ColRed(X, Y)
              /\ Xold' = X
              /\ Yold' = Y
              /\ UNCHANGED << X, E >>
            BY <2>1 DEF ReduceColumns
        <3>3. i' \in 1..3
            BY <3>2
        <3>4. Xold' \in SUBSET Z /\ Yold' \in SUBSET Z
            BY <3>2, <2>4
        <3>5. X' \in SUBSET Z /\ E' \in SUBSET Z
            BY <3>2, <2>4
        <3>6. Y' = MaxFloors(Y, X, Leq)
            BY <3>2 DEF ColRed
        <3>7. Y' \in SUBSET Z
            BY <3>6, <2>4, FloorsIsSubset, MaxIsSubset, ProblemInput
                DEF MaxFloors, Z
        <3> QED
            BY <3>3, <3>4, <3>5, <3>7 DEF TypeInv
    <2>2. ASSUME TypeInv /\ ReduceRows
          PROVE TypeInv'
        <3>1. /\ (i = 2) /\ (i' = 3)
              /\ X' = RowRed(X, Y)
              /\ UNCHANGED << Y, E, Xold, Yold >>
            BY <2>2 DEF ReduceRows
        <3>2. i' \in 1..3
            BY <3>1
        <3>3. /\ Y' \in SUBSET Z /\ E' \in SUBSET Z
              /\ Xold' \in SUBSET Z /\ Yold' \in SUBSET Z
            BY <3>1, <2>4
        <3>4. X' = MaxCeilings(X, Y, Leq)
            BY <3>1 DEF RowRed
        <3>5. X' \in SUBSET Z
            BY <3>4, <2>4,CeilingsIsSubset,  MaxIsSubset, ProblemInput
                DEF MaxCeilings, Z
        <3> QED
            BY <3>2, <3>3, <3>5 DEF TypeInv
    <2>3. ASSUME TypeInv /\ RemoveEssential
          PROVE TypeInv'
        <3> DEFINE
            Ess == X \cap Y
        <3>1. /\ (i = 3) /\ (i' = 1)
              /\ X' = X \ Ess
              /\ Y' = Y \ Ess
              /\ E' = E \cup Ess
              /\ UNCHANGED << Xold, Yold >>
            BY <2>3 DEF RemoveEssential
        <3>2. i' \in 1..3
            BY <3>1
        <3>3. Xold' \in SUBSET Z /\ Yold' \in SUBSET Z
            BY <3>1, <2>4
        <3>4. X' \in SUBSET Z /\ Y' \in SUBSET Z
            <4>1. X' \subseteq X /\ Y' \subseteq Y
                BY <3>1
            <4> QED
                BY <4>1, <2>4
        <3>5. E' \in SUBSET Z
            <4>1. Ess \in SUBSET Z
                <5>1. Ess \subseteq X
                    BY <3>1
                <5>2. X \in SUBSET Z
                    BY <2>4
                <5> QED
                    BY <5>1, <5>2
            <4>2. E' = E \cup Ess
                BY <3>1
            <4>3. E \in SUBSET Z
                BY <2>4
            <4> QED
                BY <4>2, <4>3, <4>1
        <3> QED
            BY <3>2, <3>3, <3>4, <3>5 DEF TypeInv
    <2> QED
        BY <1>2, <2>1, <2>2, <2>3 DEF Next
<1>3. ASSUME TypeInv /\ [Next]_vars
      PROVE TypeInv'
    BY <1>2, <1>3 DEF Next, vars, TypeInv
<1> QED
    <2> DEFINE
        Inv == TypeInv
        Nx == Next
    <2>1. ASSUME Inv /\ [Nx]_vars
          PROVE Inv'
        BY <2>1, <1>3 DEF Inv, Nx
    <2>2. (TypeInv /\ [][Next]_vars) => []TypeInv
        BY <2>1, PTL DEF Inv, Nx
    <2>3. (Init /\ [][Next]_vars) => []TypeInv
        BY <1>1, <2>2
    <2> QED
        BY <2>3 DEF Spec


THEOREM MaximalAtEssAux ==
    Spec => [] /\ (i = 2) => /\ X = Xold
                             /\ Y = ColRed(Xold, Yold)

               /\ (i = 3) => /\ X = RowRed(Xold, Y)
                             /\ Y = ColRed(Xold, Yold)
PROOF
<1> DEFINE Inv == /\ (i = 2) => /\ X = Xold
                                /\ Y = ColRed(Xold, Yold)

                  /\ (i = 3) => /\ X = RowRed(Xold, Y)
                                /\ Y = ColRed(Xold, Yold)
<1>1. ASSUME Init
      PROVE Inv
    BY <1>1 DEF Init, Inv
<1>2. ASSUME Inv /\ [Next]_vars
      PROVE Inv'
    <2>1. SUFFICES ASSUME Next
                   PROVE Inv'
        BY <1>2, <2>1 DEF vars
    <2>2. ASSUME ReduceColumns
          PROVE Inv'
        BY <2>2 DEF ReduceColumns, Inv
    <2>3. ASSUME ReduceRows
          PROVE Inv'
        BY <1>2, <2>3 DEF ReduceRows, Inv
    <2>4. ASSUME RemoveEssential
          PROVE Inv'
        BY <1>2, <2>4 DEF RemoveEssential, Inv
    <2> QED  (* goal from <2>1 *)
        BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1> QED
    <2>1. (Inv /\ [][Next]_vars)  =>  []Inv
        BY <1>2, PTL
    <2>2. (Init /\ [][Next]_vars)  =>  []Inv
        BY <2>1, <1>1
    <2> QED
        BY <2>2, PTL DEF Spec


THEOREM MaximalAtEss ==
    Spec => [] \/ i # 3
               \/ /\ X = RowRed(Xold, Y)
                  /\ Y = ColRed(Xold, Yold)
PROOF
<1> DEFINE
    InvMaxAtEss ==
        /\ (i = 2) => /\ X = Xold
                      /\ Y = ColRed(Xold, Yold)
        /\ \/ i # 3
           \/ /\ X = RowRed(Xold, Y)
              /\ Y = ColRed(Xold, Yold)
<1>2. (/\ (i = 2) => /\ X = Xold
                     /\ Y = ColRed(Xold, Yold)

       /\ (i = 3) => /\ X = RowRed(Xold, Y)
                     /\ Y = ColRed(Xold, Yold))  => InvMaxAtEss
    OBVIOUS
<1> QED
    BY <1>2, MaximalAtEssAux, PTL

--------------------------------------------------------------------------------
(* More invariants. *)


THEOREM Spec => [](X \subseteq Z /\ Y \subseteq Z)
PROOF
<1> DEFINE Inv == /\ X \subseteq Z
                  /\ Y \subseteq Z
<1>1. ASSUME TypeInv
      PROVE Inv
    BY <1>1 DEF TypeInv, Inv
<1>2. ([]TypeInv)  =>  []Inv
    BY <1>1, PTL
<1> QED
    BY TypeOK, <1>2, PTL


THEOREM YERefinesYinit ==
    Spec => [] Refines(Y \cup E, Yinit, Leq)
PROOF
<1> DEFINE
    Inv == Refines(Y \cup E, Yinit, Leq)
<1>1. Spec => [](IsFiniteSet(X) /\ IsFiniteSet(Y))
    <2>1. Spec => []TypeInv
        BY TypeOK
    <2>2. ([]TypeInv)  =>  [](IsFiniteSet(X) /\ IsFiniteSet(Y))
        <3>1. TypeInv => /\ X \in SUBSET Z
                         /\ Y \in SUBSET Z
            BY DEF TypeInv
        <3>2. IsFiniteSet(Z)
            BY ProblemInput
        <3>3. TypeInv => (IsFiniteSet(X) /\ IsFiniteSet(Y))
            BY <3>1, <3>2, FS_Subset
        <3> QED
            BY <3>3, PTL
    <2> QED
        BY <2>1, <2>2
<1>2. Inv' = Refines(Y' \cup E', Yinit, Leq)
    BY DEF Inv, Refines
<1>3. ASSUME TypeInv /\ Inv /\ ReduceColumns
      PROVE Inv'
    <2>1. SUFFICES Refines(Y' \cup E', Yinit, Leq)
        BY <1>2
    <2>2. SUFFICES
            ASSUME NEW u \in (Y' \cup E')
            PROVE \E v \in Yinit:  Leq[u, v]
        BY <2>1 DEF Refines, Refines  (* goal from <2>1 *)
    <2>3. ASSUME NEW w \in (Y \cup E)
          PROVE \E v \in Yinit:  Leq[w, v]
        <3>1. Refines(Y \cup E, Yinit, Leq)
            BY <1>3 DEF Inv
        <3> QED
            BY <3>1 DEF Refines, Refines
    <2>4. CASE u \in E'
        <3>1. E' = E
            BY <1>3 DEF ReduceColumns
        <3>2. u \in E
            BY <2>2, <2>4, <2>3, <3>1
        <3> QED  (* goal from <2>2 *)
            BY <3>2, <2>3
    <2>5. CASE u \in Y'
        <3>1. Y' = MaxFloors(Y, X, Leq)
            BY <1>3 DEF ReduceColumns, ColRed
        <3>2. Y' \subseteq Floors(Y, X, Leq)
            BY <3>1, MaxIsSubset DEF MaxFloors
        <3>3. u \in Floors(Y, X, Leq)
            BY <2>5, <3>2
        <3>4. PICK y \in Y:  u = Floor(y, X, Leq)
            BY <3>3 DEF Floors
        <3>8. y \in Z
            BY <3>4, <1>3 DEF TypeInv
        <3>5. Leq[u, y]
            <4>2. X \subseteq Z
                BY <1>3 DEF TypeInv
            <4>3. Z = Support(Leq)
                BY DEF Z
            <4>4. IsACompleteLattice(Leq)
                BY ProblemInput
            <4> QED
                BY <3>8, <4>2, <4>3, <4>4, FloorIsSmaller, <3>4
        <3>6. PICK v \in Yinit:  Leq[y, v]
            BY <2>3, <3>4
        <3>7. u \in Z
            BY <3>3, FloorsIsSubset, ProblemInput, <1>3 DEF TypeInv, Z
        <3>11. v \in Z
            BY <3>6, ProblemInput
        <3>9. Leq[u, y] /\ Leq[y, v]
            BY <3>5, <3>6
        <3>10. Leq[u, v]
            BY <3>8, <3>7, <3>11, <3>9, ProblemInput, LeqTransitive
                DEF IsTransitive, Z
        <3> QED
            <4>1. v \in Yinit
                BY <3>6
            <4> QED  (* goal from <2>2 *)
                BY <3>10, <4>1
    <2> QED
        BY <2>4, <2>5, <2>2  (* exhaustive by <2>2 *)
<1>4. ASSUME Inv /\ RemoveEssential
      PROVE Inv'
    <2> DEFINE Ess == X \cap Y
    <2>1. /\ Y' = Y \ Ess
          /\ E' = E \cup Ess
        BY <1>4 DEF RemoveEssential
    <2>2. (Y' \cup E')  =  (Y \cup E)
        <3>1. (Y' \cup E')  =  ((Y \ Ess)  \cup  (E \cup Ess))
            BY <2>1
        <3>2. (Y' \cup E')  =  ((Ess \cup (Y \ Ess)) \cup E)
            BY <3>1
        <3>3. (Ess \cup (Y \ Ess))  =  Y
            <4>1. Y \subseteq (Ess \cup (Y \ Ess))
                OBVIOUS
            <4>2. Ess \subseteq Y
                BY DEF Ess
            <4>3. (Ess \cup (Y \ Ess)) \subseteq Y
                BY <4>2
            <4> QED
                BY <4>1, <4>3
        <3> QED
            BY <3>2, <3>3
    <2>3. Refines(Y \cup E, Yinit, Leq)
        BY <1>4 DEF Inv
    <2>4. Refines(Y' \cup E', Yinit, Leq)
        BY <2>3, <2>2
    <2> QED
        BY <2>4, <1>2
<1>5. ASSUME Inv /\ ReduceRows
      PROVE Inv'
    <2>1. (Y' \cup E')  =  (Y \cup E)
        <3>1. Y' = Y /\ E' = E
            BY <1>5 DEF ReduceRows
        <3> QED
            BY <3>1
    <2>2. Refines(Y \cup E, Yinit, Leq)
        BY <1>5 DEF Inv
    <2>3. Refines(Y' \cup E', Yinit, Leq)
        BY <2>1, <2>2
    <2> QED
        BY <2>3, <1>2
<1>6. ASSUME TypeInv /\ Inv /\ Next
      PROVE Inv'
    BY <1>6, <1>3, <1>4, <1>5 DEF Next
<1>7. ASSUME Init
      PROVE Inv
    <2>1. SUFFICES Refines(Y \cup E, Yinit, Leq)
        BY DEF Inv
    <2>2. Y = Yinit /\ E = {}
        BY <1>7 DEF Init
    <2>3. (Y \cup E)  =  Yinit
        BY <2>2
    <2>4. Refines(Yinit, Yinit, Leq)
        <3>1. \A u \in Yinit:  Leq[u, u]
            <4>1. Yinit \subseteq Z
                BY ProblemInput
            <4>2. IsACompleteLattice(Leq) /\ Z = Support(Leq)
                BY ProblemInput DEF Z
            <4>3. \A u \in Z:  Leq[u, u]
                BY <4>2 DEF IsACompleteLattice, IsACompleteLattice,
                    IsAPartialOrder, IsAPartialOrder,
                    IsReflexive
            <4> QED
                BY <4>3, <4>1
        <3>2. \A u \in Yinit:  \E v \in Yinit:  Leq[u, u]
            BY <3>1
        <3> QED
            BY <3>2 DEF Refines
    <2> QED  (* goal from <2>1 *)
        BY <2>3, <2>4
<1> HIDE DEF Inv
<1>8. ASSUME Inv /\ [TypeInv /\ Next]_vars
      PROVE Inv'
    BY <1>8, <1>6 DEF Inv, vars
<1> QED
    <2>1. (Inv /\ [][TypeInv /\ Next]_vars) => []Inv
        BY <1>8, PTL
    <2>2. (Init /\ [][TypeInv /\ Next]_vars) => []Inv
        BY <2>1, <1>7
    <2>3. (Init /\ []TypeInv /\ [][Next]_vars) => []Inv
        BY <2>2, PTL
    <2> QED
        BY <2>3, TypeOK DEF Spec, Inv


THEOREM XinitRefinesXE ==
    Spec => [] Refines(Xinit, X \cup E, Leq)
PROOF
<1> DEFINE Inv == Refines(Xinit, X \cup E, Leq)
<1>1. ASSUME Init
      PROVE Inv
    <2>1. /\ X = Xinit
          /\ E = {}
        BY <1>1 DEF Init
    <2>2. Refines(Xinit, Xinit, Leq)
        <3>1. SUFFICES ASSUME NEW u \in Xinit
                       PROVE Leq[u, u]
            BY <3>1 DEF Refines
        <3>2. SUFFICES u \in Support(Leq)
            BY <3>2, LeqIsPor DEF IsAPartialOrder, IsReflexive
        <3> QED  (* goal from <3>2 *)
            BY ProblemInput, <3>1 DEF Z
    <2> QED
        BY <2>1, <2>2
<1>2. ASSUME Inv /\ [TypeInv /\ TypeInv' /\ Next]_vars
      PROVE Inv'
    <2>1. SUFFICES ASSUME TypeInv /\ TypeInv' /\ Next
                   PROVE Inv'
        BY <1>2, <2>1 DEF vars
    <2>2. ASSUME ReduceColumns
          PROVE Inv'
        BY <1>2, <2>2 DEF ReduceColumns
    <2>3. ASSUME ReduceRows
          PROVE Inv'
        <3>1. SUFFICES
                ASSUME NEW u \in Xinit
                PROVE \E v \in (X' \cup E'):  Leq[u, v]
            BY <3>1 DEF Refines
        <3>2. PICK r \in (X \cup E):  Leq[u, r]
            BY <1>2, <3>1 DEF Refines
        <3>3. CASE r \in E
            BY <3>2, <3>3, <2>3 DEF ReduceRows
        <3>4. CASE r \in X
            <4>2. /\ u \in Z
                  /\ r \in Z
                BY <2>1, <3>1, <3>4, ProblemInput DEF TypeInv
            <4>1. PICK v \in X':  Leq[r, v]
                <5> DEFINE
                    t == Ceil(r, Y, Leq)
                    S == Ceilings(X, Y, Leq)
                <5>1. /\ t \in S
                      /\ Leq[r, t]
                    <6>1. t \in S
                        BY <3>4 DEF t, Ceilings
                    <6>2. Leq[r, t]
                        BY <2>1, <3>4, ProblemInput,
                            CeilIsLarger DEF TypeInv, Z
                    <6> QED
                        BY <6>1, <6>2
                <5>2. X' = Maxima(S, Leq)
                    BY <2>3 DEF ReduceRows, RowRed, MaxCeilings
                <5>6. S \subseteq Z
                    BY <2>1, CeilingsIsSubset, ProblemInput
                        DEF TypeInv, Z
                <5>3. PICK v \in X':  Leq[t, v]
                    <6>1. PICK v \in S:  /\ Leq[t, v]
                                         /\ IsMaximal(v, S, Leq)
                        BY <5>1, <5>6, HasSomeMaximalAbove, ProblemInput
                            DEF IsACompleteLattice, IsAPartialOrder, Z
                    <6>2. v \in X'
                        BY <5>2, <6>1 DEF Maxima
                    <6> QED
                        BY <6>1, <6>2
                <5>5. /\ r \in Z
                      /\ t \in Z
                      /\ v \in Z
                    BY <4>2, <5>1, <5>6, <5>3, <2>1,
                        ProblemInput DEF TypeInv
                <5> QED
                    BY <5>3, <5>1, <5>5, LeqTransitive
                        DEF IsTransitive, Z
            <4>3. v \in Z
                BY <2>1, <4>1, ProblemInput DEF TypeInv
            <4> QED
                BY <3>2, <4>1, <4>2, <4>3, LeqTransitive
                    DEF IsTransitive, Z
        <3> QED
            BY <3>3, <3>4, <2>3 DEF ReduceRows
    <2>4. ASSUME RemoveEssential
          PROVE Inv'
        <3> DEFINE Ess == X \cap Y
        <3>1. /\ X' = X \ Ess
              /\ E' = E \cup Ess
            BY <2>4 DEF RemoveEssential
        <3>2. (X' \cup E')  =  (X \cup E)
            BY <3>1
        <3> QED
            BY <1>2, <3>2
    <2> QED  (* goal from <2>1 *)
        BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1> QED
    <2>1. (Inv /\ [][TypeInv /\ TypeInv' /\ Next]_vars)  =>  []Inv
        BY <1>2, PTL
    <2>2. (Init /\ [][TypeInv /\ TypeInv' /\ Next]_vars)  =>  []Inv
        BY <2>1, <1>1
    <2>3. (Init /\ []TypeInv /\ [][Next]_vars)  =>  []Inv
        BY <2>2, PTL
    <2> QED
        BY <2>3, TypeOK, PTL DEF Spec


THEOREM YincompE ==
    Spec => [](\A y \in Y:  \A e \in E:  ~ Leq[e, y])
PROOF
<1> DEFINE
    Inv == \A y \in Y:  \A e \in E:  ~ Leq[e, y]
    Aux == \/ i # 3
           \/ /\ X = RowRed(Xold, Y)
              /\ Y = ColRed(Xold, Yold)
<1> HIDE DEF Inv, Aux
<1>1. ASSUME Init
      PROVE Inv
    <2>1. E = {}
        BY <1>1 DEF Init
    <2> QED
        BY <2>1 DEF Inv
<1>2. ASSUME /\ TypeInv /\ Inv /\ Next
             /\ \/ i # 3
                \/ /\ X = RowRed(Xold, Y)
                   /\ Y = ColRed(Xold, Yold)
      PROVE Inv'
    <2>1. ASSUME Inv /\ ReduceColumns
          PROVE Inv'
        <3>1. /\ Y' = MaxFloors(Y, X, Leq)
              /\ E' = E
            BY <2>1 DEF ReduceColumns, ColRed
        <3>2. SUFFICES
                ASSUME NEW y \in Y', NEW e \in E'
                PROVE ~ Leq[e, y]
            BY DEF Inv
        <3>3. SUFFICES
                ASSUME Leq[e, y]
                PROVE FALSE
            OBVIOUS  (* goal from <3>2 *)
        <3>4. e \in E
            BY <3>2, <3>1
        <3>5. Y' = Maxima(Floors(Y, X, Leq), Leq)
            BY <3>1 DEF Maxima, Maxima, MaxFloors
        <3>6. Y' \subseteq Floors(Y, X, Leq)
            BY <3>5, MaxIsSubset
        <3>7. PICK p \in Y:  y = Floor(p, X, Leq)
            BY <3>2, <3>6 DEF Floors
        <3>14. p \in Z
            <4>1. Y \in SUBSET Z
                BY <1>2 DEF TypeInv
            <4> QED
                BY <3>7, <4>1
        <3>8. Leq[y, p]
            <4>1. X \subseteq Z
                BY <1>2 DEF TypeInv
            <4>2. Z = Support(Leq)
                BY DEF Z
            <4>3. IsACompleteLattice(Leq)
                BY ProblemInput
            <4> QED
                BY <3>7, <3>14, <4>1, <4>2, <4>3, FloorIsSmaller
        <3>12. Leq[e, p]
            <4>1. Leq[e, y] /\ Leq[y, p]
                BY <3>3, <3>8
            <4>2. (e \in Z) /\ (y \in Z) /\ (p \in Z)
                <5>1. e \in Z
                    <6>1. E \in SUBSET Z
                        BY <1>2 DEF TypeInv
                    <6> QED
                        BY <3>4, <6>1
                <5>2. y \in Z
                    <6>1. y = Floor(p, X, Leq)
                        BY <3>7
                    <6>2. IsACompleteLattice(Leq)
                        BY ProblemInput
                    <6>3. X \subseteq Z
                        BY <1>2 DEF TypeInv
                    <6>4. Z = Support(Leq)
                        BY DEF Z
                    <6> QED
                        BY <6>1, <6>2, <6>3, <6>4, FloorExists
                <5> QED
                    BY <5>1, <5>2, <3>14
            <4>3. IsTransitive(Leq)
                BY ProblemInput DEF IsACompleteLattice,
                    IsACompleteLattice, IsAPartialOrder
            <4> QED
                BY <4>1, <4>2, <4>3 DEF IsTransitive, Z
        <3>13. ~ Leq[e, p]
            <4>1. (p \in Y) /\ (e \in E)
                BY <3>4, <3>7
            <4> QED
                BY <4>1, <1>2 DEF Inv
        <3> QED
            BY <3>12, <3>13
    <2>2. ASSUME Inv /\ ReduceRows
          PROVE Inv'
        <3>1. (Y' = Y) /\ (E' = E)
            BY <2>2 DEF ReduceRows
        <3>2. \A y \in Y:  \A e \in E:  ~ Leq[e, y]
            BY <2>2 DEF Inv
        <3>3. \A y \in Y':  \A e \in E':  ~ Leq[e, y]
            BY <3>1, <3>2
        <3> QED
            BY <3>3 DEF Inv
    <2>3. ASSUME Inv /\ RemoveEssential
          PROVE Inv'
        <3> DEFINE Ess == X \cap Y
        <3>1. (Y' = (Y \ Ess)) /\ (E' = (E \cup Ess))
            BY <2>3 DEF RemoveEssential
        <3>2. \A y \in Y:  \A e \in E:  ~ Leq[e, y]
            BY <2>3 DEF Inv
        <3>3. SUFFICES
                ASSUME NEW y \in Y', NEW e \in E'
                PROVE ~ Leq[e, y]
            BY DEF Inv
        <3>4. Y' \subseteq Y
            BY <3>1
        <3>5. y \in Y
            BY <3>3, <3>4
        <3>6. (e \in E) \/ (e \in Ess)
            BY <3>1, <3>3
        <3>7. CASE e \in E
            BY <3>5, <3>7, <3>2
        <3>8. CASE e \in Ess
            <4>1. \A p, q \in Y:  (p # q) => ~ Leq[p, q]
                <5>1. \E S:  Y = Maxima(S, Leq)
                    BY <1>2, <2>3 DEF ColRed, MaxFloors, RemoveEssential
                <5>2. Y = Maxima(Y, Leq)
                    BY <5>1, MaxIsIdempotent
                <5>3. Y \subseteq Support(Leq)
                    <6>1. Y \in SUBSET Z
                        BY <1>2 DEF TypeInv
                    <6>2. Z = Support(Leq)
                        BY DEF Z
                    <6> QED
                        BY <6>1, <6>2
                <5>4. IsAntiSymmetric(Leq)
                    BY ProblemInput DEF IsACompleteLattice,
                        IsACompleteLattice, IsAPartialOrder
                <5>5. IsAntiChain(Y, Leq)
                    BY <5>2, <5>3, <5>4, MaximaIsAntiChain
                <5> QED
                    BY <5>5 DEF IsAntiChain
            <4>2. e # y
                <5>1. y \in (Y \ Ess)
                    BY <3>3, <3>1
                <5>2. y \notin Ess
                    BY <5>1
                <5>3. e \in Ess
                    BY <3>8
                <5> QED
                    BY <5>2, <5>3
            <4>3. (e \in Y) /\ (y \in Y)
                BY <3>8, <3>5 DEF Ess
            <4> QED  (* goal from <3>3 *)
                BY <4>1, <4>2, <4>3
        <3> QED
            BY <3>7, <3>8, <3>6
    <2> QED
        BY <1>2, <2>1, <2>2, <2>3 DEF Next
<1>3. ASSUME Inv /\ [TypeInv /\ Aux /\ Next]_vars
      PROVE Inv'
    BY <1>3, <1>2 DEF Inv, Aux, vars
<1> QED
    <2>1. (Inv /\ [][TypeInv /\ Aux /\ Next]_vars)  =>  []Inv
        BY <1>3, PTL
    <2>2. (Init /\ [][TypeInv /\ Aux /\ Next]_vars)  =>  []Inv
        BY <2>1, <1>1
    <2>3. (Init /\ []TypeInv /\ []Aux /\ [][Next]_vars)  =>  []Inv
        BY <2>2, PTL
    <2> QED
        BY <2>3, PTL, MaximalAtEss, TypeOK DEF Spec, Aux, Inv


THEOREM noYcapE ==
    Spec => []((Y \cap E) = {})
PROOF
<1>1. Spec => [](TypeInv /\ (\A y \in Y:  \A e \in E:  ~ Leq[e, y]))
    BY TypeOK, YincompE
<1>7. SUFFICES
        ASSUME TypeInv /\ (\A y \in Y:  \A e \in E:  ~ Leq[e, y])
        PROVE (Y \cap E) = {}
    BY <1>1, <1>7, PTL
<1>2. SUFFICES
        ASSUME NEW y \in (Y \cap E),
            /\ TypeInv
            /\ \A q \in Y:  \A e \in E:  ~ Leq[e, q]
        PROVE FALSE
    BY <1>7, <1>2
<1>3. ~ Leq[y, y]
    BY <1>2
<1>4. IsReflexive(Leq)
    BY ProblemInput DEF IsACompleteLattice, IsACompleteLattice,
        IsAPartialOrder
<1>5. y \in Support(Leq)
    <2>1. y \in Y
        BY <1>2
    <2>2. Y \subseteq Z
        BY <1>2 DEF TypeInv
    <2>3. Z = Support(Leq)
        BY DEF Z
    <2> QED
        BY <2>1, <2>2, <2>3
<1>6. Leq[y, y]
    BY <1>5, <1>4 DEF IsReflexive
<1> QED  (* goal from <1>2 *)
    BY <1>3, <1>6

--------------------------------------------------------------------------------
(* A minimal cover of Xinit, Yinit can be constructed from a minimal cover
of X, Y.
*)


THEOREM HatIsMinCoverInit ==
    ASSUME Init
    PROVE HatIsMinCover
PROOF
<1>1. SUFFICES
        ASSUME
            NEW C, NEW H,
            /\ IsAMinCover(C, X, Y, Leq)
            /\ IsAHat(H, C \cup E, Yinit, Leq)
        PROVE
            /\ IsAMinCover(H, Xinit, Yinit, Leq)
            /\ Card(H) = Card(C) + Card(E)
    BY <1>1 DEF HatIsMinCover, Card
<1>2. /\ E = {}
      /\ X = Xinit
      /\ Y = Yinit
    BY DEF Init
<1>3. /\ (C \cup E) = C
      /\ Card(C) + Card(E) = Card(C)
    <2>1. (C \cup E) = C
        BY <1>2
    <2>2. Card(C) + Card(E) = Card(C)
        <3>1. Card(C) \in Nat
            BY <1>1, <1>2, MinCoverProperties, ProblemInput, FS_Subset,
                FS_CardinalityType DEF Card
        <3>2. Card(E) = 0
            BY <1>2, FS_EmptySet DEF Card
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, <2>2
<1>4. IsAHat(H, C, Yinit, Leq)
    BY <1>1, <1>3
<1>5. IsAMinCover(H, X, Y, Leq)
    <2>1. /\ H \in SUBSET Y
          /\ Cardinality(H) <= Cardinality(C)
        BY <1>4, <1>2 DEF IsAHat
    <2>2. IsACover(H, X, Leq)
        <3>1. Refines(X, C, Leq)
            BY <1>1, MinCoverProperties, RefinesMeansCover
        <3>2. Refines(C, H, Leq)
            BY <1>4, <1>2 DEF IsAHat
        <3>3. /\ X \subseteq Z
              /\ C \subseteq Z
              /\ H \subseteq Z
            BY <2>1, <1>2, ProblemInput, <1>1, MinCoverProperties
        <3> QED
            BY <3>1, <3>2, <3>3, RefinesIsTransitive,
                LeqTransitive,RefinesMeansCover DEF Z
    <2> QED
        BY <1>1, <2>1, <2>2, HaveCardAsCost,
            MinCoverEquivCoverCard, <1>2, ProblemInput, FS_Subset
<1>6. Card(H) = Card(C) + Card(E)
    <2>1. Card(H) = Card(C)
        <3>1. IsAMinCover(C, X, Y, Leq)
            BY <1>1
        <3>2. /\ Y \in SUBSET Z
              /\ IsFiniteSet(Y)
            BY <1>2, ProblemInput, FS_Subset
        <3>3. CardinalityAsCost(Z)
            BY ProblemInput, HaveCardAsCost
        <3> QED
            BY <1>5, <3>1, <3>2, <3>3,
                AllMinCoversSameCard DEF Card
    <2> QED
        BY <2>1, <1>3
<1> QED
    BY <1>5, <1>6 DEF Init


THEOREM HatIsMinCoverUnchangedByReduceColumns ==
    ASSUME
        /\ TypeInv /\ TypeInv'
        /\ ((Y \cap E) = {})'
        /\ Refines(Xinit, X \cup E, Leq)
        /\ Refines(Y \cup E, Yinit, Leq)
        /\ HatIsMinCover
        /\ ReduceColumns
    PROVE
        HatIsMinCover'
PROOF
<1>1. IsFiniteSet(Xinit) /\ IsFiniteSet(Yinit)
    <2>1. Xinit \subseteq Z /\ Yinit \subseteq Z
        BY ProblemInput
    <2>2. IsFiniteSet(Z)
        BY ProblemInput
    <2> QED
        BY <2>1, <2>2, FS_Subset
<1>2. IsFiniteSet(X) /\ IsFiniteSet(Y)
    <2>1. X \in SUBSET Z /\ Y \in SUBSET Z
        BY DEF TypeInv
    <2>2. IsFiniteSet(Z)
        BY ProblemInput
    <2> QED
        BY <2>1, <2>2, FS_Subset
<1>3. SUFFICES
        ASSUME NEW C, NEW H,
            /\ IsAMinCover(C, X', Y', Leq)
            /\ IsAHat(H, C \cup E', Yinit, Leq)
        PROVE
            /\ IsAMinCover(H, Xinit, Yinit, Leq)
            /\ Card(H) = Card(C) + Card(E')
    BY DEF HatIsMinCover, Card
<1>4. E' = E /\ X' = X
    BY DEF ReduceColumns
<1>5. H \subseteq Z
    <2>1. H \subseteq Yinit
        BY <1>3 DEF IsAHat
    <2>2. Yinit \subseteq Z
        BY ProblemInput
    <2> QED
        BY <2>1, <2>2
<1>6. X \in SUBSET Z /\ E \in SUBSET Z
    BY DEF TypeInv
<1>7. /\ IsAMinCover(C, X, Y', Leq)
      /\ IsAHat(H, C \cup E, Yinit, Leq)
    BY <1>3, <1>4
<1>8. IsACoverFrom(H, Xinit, Yinit, Leq)
    <2>2. IsACover(C, X, Leq)
        BY <1>7, MinCoverProperties
    <2>3. IsACover(C \cup E, X \cup E, Leq)
        <3>1. \A x \in X:  \E y \in C:  Leq[x, y]
            BY <2>2 DEF IsACover
        <3>2. SUFFICES
                ASSUME NEW x \in (X \cup E)
                PROVE \E y \in (C \cup E):  Leq[x, y]
            BY DEF IsACover
        <3>3. CASE x \in X
            <4>1. PICK y \in C:  Leq[x, y]
                BY <3>1, <3>3
            <4>2. y \in (C \cup E)
                BY <4>1
            <4> QED  (* goal from <3>2 *)
                BY <4>1, <4>2
        <3>4. CASE x \in E
            <4>1. x \in Z
                <5>1. E \in SUBSET Z
                    BY DEF TypeInv
                <5> QED
                    BY <3>4, <5>1
            <4>2. IsReflexive(Leq)
                BY ProblemInput DEF IsACompleteLattice,
                    IsAPartialOrder
            <4>3. Leq[x, x]
                BY <4>1, <4>2 DEF IsReflexive, Z
            <4>4. x \in (C \cup E)
                BY <3>4
            <4> QED
                BY <4>3, <4>4
        <3> QED
            BY <3>3, <3>4, <3>2
    <2>4. IsACover(H, X \cup E, Leq)
        <3>1. \A u \in (X \cup E):  \E v \in (C \cup E):  Leq[u, v]
            BY <2>3 DEF IsACover
        <3>2. Refines(C \cup E, H, Leq)
            BY <1>7 DEF IsAHat
        <3>3. \A p \in (C \cup E):  \E q \in H:  Leq[p, q]
            BY <3>2 DEF Refines
        <3>4. SUFFICES
                ASSUME NEW u \in (X \cup E)
                PROVE \E y \in H:  Leq[u, y]
            BY DEF IsACover
        <3>5. PICK v \in (C \cup E):  Leq[u, v]
            BY <3>4, <3>1
        <3>6. PICK q \in H:  Leq[v, q]
            BY <3>5, <3>3
        <3>7. Leq[u, v] /\ Leq[v, q]
            BY <3>5, <3>6
        <3>8. (u \in Z) /\ (v \in Z) /\ (q \in Z)
            <4>1. u \in Z
                <5>2. u \in (X \cup E)
                    BY <3>4
                <5> QED
                    BY <1>6, <5>2
            <4>2. v \in Z
                <5>1. v \in (C \cup E)
                    BY <3>5
                <5>2. E \in SUBSET Z
                    BY DEF TypeInv
                <5>3. Y' \in SUBSET Z
                    BY DEF TypeInv
                <5>4. C \in SUBSET Y'
                    BY <1>3, MinCoverProperties
                <5>5. C \in SUBSET Z
                    BY <5>3, <5>4
                <5>6. (C \cup E) \in SUBSET Z
                    BY <5>2, <5>5
                <5> QED
                    BY <5>1, <5>6
            <4>3. q \in Z
                <5>1. q \in H
                    BY <3>6
                <5> QED
                    BY <5>1, <1>5
            <4> QED
                BY <4>1, <4>2, <4>3
        <3>9. Leq[u, q]
            BY <3>7, <3>8, LeqTransitive DEF IsTransitive, Z
        <3> QED
            <4>1. Leq[u, q] /\ (q \in H)
                BY <3>9, <3>6
            <4> QED  (* goal from <3>4 *)
                BY <4>1
    <2>5. Refines(Xinit, X \cup E, Leq)
        OBVIOUS
    <2>6. IsACover(H, Xinit, Leq)  (* TODO *)
        <3>1. H \subseteq Z
            BY <1>5
        <3>2. Xinit \subseteq Z
            BY ProblemInput
        <3>3. (X \cup E) \subseteq Z
            BY <1>6
        <3>4. /\ IsACover(X \cup E, Xinit, Leq)
              /\ IsACover(H, X \cup E, Leq)
            BY <2>4, <2>5, RefinesMeansCover
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, LeqTransitive,
                CoveringIsTransitive DEF Z
    <2> QED
        <3>1. IsAHat(H, C \cup E, Yinit, Leq)  =>  (H \subseteq Yinit)
            BY DEF IsAHat
        <3>2. H \subseteq Yinit
            BY <3>1, <1>7
        <3> QED
            BY <2>6, <3>2 DEF IsACoverFrom
<1> DEFINE H2 == Hat(C, Y, Leq)
<1>9. /\ C \subseteq MaxFloors(Y, X, Leq)
      /\ C \subseteq Z
    <2>1. C \subseteq Y'
        BY <1>3, MinCoverProperties
    <2>2. Y' = MaxFloors(Y, X, Leq)
        <3>1. Y' = ColRed(X, Y)
            BY DEF ReduceColumns
        <3> QED
            BY <3>1 DEF ColRed
    <2>3. Y' \in SUBSET Z
        BY DEF TypeInv
    <2> QED
        BY <2>1, <2>2, <2>3
<1>10. IsFiniteSet(C)
    <3>1. IsFiniteSet(Z)
        BY ProblemInput
    <3>2. C \subseteq Z
        BY <1>9
    <3> QED
        BY <3>1, <3>2, FS_Subset
<1>11. /\ C = Floors(H2, X, Leq)
       /\ C \subseteq MaxFloors(Y, X, Leq)
       /\ Card(C) = Card(H2)
    <2>1. X \in SUBSET Z /\ Y \in SUBSET Z
        BY DEF TypeInv
    <2>2. C \subseteq MaxFloors(Y, X, Leq)
        BY <1>9
    <2>4. IsACompleteLattice(Leq)
        BY ProblemInput
    <2> QED
        BY <2>1, <2>2, <1>10, <2>4,
            MaxFloorsHatIsUnfloor DEF H2, Z, Card
<1> DEFINE
    Yf == Floors(Y, X, Leq)
<1>12. H2 \subseteq Y
    <2>1. SUFFICES
            ASSUME NEW u \in C
            PROVE \E r \in Y:  Leq[u, r]
        BY DEF H2, Hat, SomeAbove
    <2>2. C \subseteq MaxFloors(Y, X, Leq)
        BY <1>11
    <2>3. C \subseteq Maxima(Floors(Y, X, Leq), Leq)
        BY <2>2 DEF MaxFloors
    <2>4. C \subseteq Floors(Y, X, Leq)
        BY <2>3 DEF Maxima
    <2>5. u \in Floors(Y, X, Leq)
        BY <2>1, <2>4
    <2>6. PICK r \in Y:  u = Floor(r, X, Leq)
        BY <2>5 DEF Floors
    <2>7. r \in Z
        BY <2>6 DEF TypeInv
    <2>8. X \subseteq Z
        BY DEF TypeInv
    <2>9. /\ IsACompleteLattice(Leq)
          /\ Z = Support(Leq)
        BY ProblemInput DEF Z
    <2>10. Leq[u, r]
        BY <2>6, <2>7, <2>8, <2>9, FloorIsSmaller
    <2> QED  (* goal from <2>1 *)
        BY <2>6, <2>10
<1>13. IsAMinCover(H2, X, Y, Leq)
    <2>1. IsAMinCover(H2, X, Y, Leq) <=> IsAMinCover(C, X, Yf, Leq)
        <3>1. IsACompleteLattice(Leq)
            BY ProblemInput
        <3>2. CardinalityAsCost(Z)
            BY HaveCardAsCost
        <3>3. X \subseteq Z
            BY DEF TypeInv
        <3>4. Y \subseteq Z /\ IsFiniteSet(Y)
            <4>1. Y \in SUBSET Z
                BY DEF TypeInv
            <4>2. IsFiniteSet(Z)
                BY ProblemInput
            <4> QED
                BY <4>1, <4>2, FS_Subset
        <3>5. H2 \subseteq Y
            BY <1>12
        <3>6. C = Floors(H2, X, Leq)
            BY <1>11
        <3>8. Cardinality(H2) <= Cardinality(C)
            <4>1. Card(C) = Card(H2)
                BY <1>11
            <4>2. IsFiniteSet(C)
                BY <1>10
            <4>3. IsFiniteSet(H2)
                <5>1. Y \in SUBSET Z
                    BY DEF TypeInv
                <5>2. IsFiniteSet(Z)
                    BY ProblemInput
                <5>3. IsFiniteSet(Y)
                    BY <5>1, <5>2, FS_Subset
                <5>4. H2 \subseteq Y
                    BY <1>12
                <5> QED
                    BY <5>3, <5>4, FS_Subset
            <4> QED BY <4>1, <4>2, <4>3, FS_CardinalityType DEF Card
        <3>9. Z = Support(Leq)
            BY DEF Z
        <3>10. Yf = Floors(Y, X, Leq)
            BY DEF Yf
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>8,
                <3>9, <3>10, MinCoverPreservedIfFloors
    <2>2. IsAMinCover(C, X, Y', Leq)
        BY <1>7
    <2>5. Y' = Maxima(Yf, Leq)
        <3>1. Y' = MaxFloors(Y, X, Leq)
            BY DEF ReduceColumns, ColRed
        <3>2. Y' = Maxima(Floors(Y, X, Leq), Leq)
            BY <3>1 DEF MaxFloors
        <3> QED
            BY <3>2 DEF Yf
    <2>6. IsAMinCover(C, X, Yf, Leq)
        <3>1. X \subseteq Z /\ Y \subseteq Z
            BY DEF TypeInv
        <3>2. Yf \subseteq Z
            <4>1. Yf = Floors(Y, X, Leq)
                BY DEF Yf
            <4> QED
                BY <4>1, <3>1, ProblemInput, FloorsIsSubset DEF Z
        <3> QED
            BY <2>2, <2>5, <3>1, <3>2, ProblemInput, LeqIsPor,
                HaveCardAsCost, MinCoversFromMaxSuffice DEF Z
                (* Max <- Y', Y <- Yf *)
    <2> QED
        BY <2>1, <2>6
<1>14. ASSUME
         NEW Cnew, NEW Hnew,
         /\ IsAMinCover(Cnew, X, Y, Leq)
         /\ IsAHat(Hnew, Cnew \cup E, Yinit, Leq)
       PROVE
         /\ IsAMinCover(Hnew, Xinit, Yinit, Leq)
         /\ Card(Hnew) = Card(Cnew) + Card(E)
    BY <1>14 DEF HatIsMinCover, Card
<1>15. ASSUME
         NEW Hnew,
         IsAHat(Hnew, H2 \cup E, Yinit, Leq)
       PROVE
         /\ IsAMinCover(Hnew, Xinit, Yinit, Leq)
         /\ Card(Hnew) = Card(H2) + Card(E)
    BY <1>13, <1>14, <1>15  (* Cnew <- H2 *)
<1>16. PICK H3:  IsAHat(H3, H2 \cup E, Yinit, Leq)
    <2>1. H2 \subseteq Y
        BY <1>12
    <2>2. (H2 \cup E)  \subseteq  (Y \cup E)
        BY <2>1
    <2>3. Refines(Y \cup E, Yinit, Leq)
        OBVIOUS
    <2>4. Refines(H2 \cup E, Yinit, Leq)
        BY <2>2, <2>3 DEF Refines  (* can refine this proof *)
    <2> DEFINE
        W == Hat(H2 \cup E, Yinit, Leq)
    <2>6. Card(W) <= Card(H2 \cup E)
        <3> DEFINE S == H2 \cup E
        <3>1. IsFiniteSet(S)
            <4>1. H2 \subseteq Y
                BY <1>12
            <4>2. Y \in SUBSET Z /\ E \in SUBSET Z
                BY DEF TypeInv
            <4>3. (H2 \cup E) \subseteq Z
                BY <4>1, <4>2
            <4>4. IsFiniteSet(Z)
                BY ProblemInput
            <4> QED
                BY <4>3, <4>4, FS_Subset DEF S
        <3>2. W = { SomeAbove(y, Yinit, Leq):  y \in S }
            BY DEF W, Hat, S
        <3> HIDE DEF H2, W, S
        <3>3. Cardinality({ SomeAbove(y, Yinit, Leq):  y \in S })
                <= Cardinality(S)
            BY <3>1, ImageOfFinite
        <3> QED
            BY <3>2, <3>3 DEF S, Card
    <2>7. IsAHat(W, H2 \cup E, Yinit, Leq)
        <3>5. \A u \in (H2 \cup E):  \E y \in Yinit:  Leq[u, y]
            BY <2>4 DEF Refines
        <3>4. \A u \in (H2 \cup E):  \E y \in Yinit:
                /\ y = SomeAbove(u, Yinit, Leq)
                /\ Leq[u, y]
            BY <3>5 DEF SomeAbove
        <3>1. W \subseteq Yinit
            <4>3. \A y \in Hat(H2 \cup E, Yinit, Leq):  y \in Yinit
                BY <3>4 DEF Hat
            <4>4. \A y \in W:  y \in Yinit
                BY <4>3 DEF W
            <4> QED
                BY <4>4
        <3>2. Refines(H2 \cup E, W, Leq)
            <4>1. SUFFICES
                    ASSUME NEW u \in (H2 \cup E)
                    PROVE \E y \in W:  Leq[u, y]
                BY DEF Refines
            <4>2. PICK y \in Yinit:  /\ y = SomeAbove(u, Yinit, Leq)
                                     /\ Leq[u, y]
                BY <3>4
            <4>3. y \in W
                BY <4>2 DEF W, Hat
            <4> QED  (* goal from <4>1 *)
                BY <4>2, <4>3
        <3>3. Card(W) <= Card(H2 \cup E)
            BY <2>6
        <3> QED
            BY <3>1, <3>2, <3>3 DEF IsAHat, Card
    <2> QED
        BY <2>7
<1>17. /\ IsAMinCover(H3, Xinit, Yinit, Leq)
       /\ Card(H3) = Card(H2) + Card(E)
    BY <1>15, <1>16
<1>18. Card(H3) = Card(C) + Card(E)
    BY <1>11, <1>17
<1>19. Card(H) \in Nat /\ Card(H3) \in Nat
    <2>1. IsFiniteSet(H) /\ IsFiniteSet(H3)
        <3>1. IsFiniteSet(H)
            <4>1. H \subseteq Z
                BY <1>5
            <4>2. IsFiniteSet(Z)
                BY ProblemInput
            <4> QED
                BY <4>1, <4>2, FS_Subset
        <3>2. IsFiniteSet(H3)
            <4>1. H3 \subseteq Yinit
                BY <1>17, MinCoverProperties
            <4>2. IsFiniteSet(Yinit)
                <5>1. (Yinit \in SUBSET Z) /\ IsFiniteSet(Z)
                    BY ProblemInput
                <5> QED
                    BY <5>1, FS_Subset
            <4> QED
                BY <4>1, <4>2, FS_Subset
        <3> QED
            BY <3>1, <3>2
    <2> QED
        BY <2>1, FS_CardinalityType DEF Card
<1>20. SUFFICES
        ASSUME ~ IsAMinCover(H, Xinit, Yinit, Leq)
        PROVE FALSE
    <2>1. IsAMinCover(H, Xinit, Yinit, Leq)
        BY <1>20
    <2>2. IsAMinCover(H3, Xinit, Yinit, Leq)
        BY <1>17
    <2>3. Card(H) = Card(H3)
        <3>3. \/ Card(H) <= Card(H3)
              \/ Card(H) >= Card(H3)
            BY <1>19
        <3> QED
            BY <2>1, <2>2, <3>3, HaveCardAsCost,
                ProblemInput, FS_Subset,
                AllMinCoversSameCard DEF Card
    <2>4. Card(H) = Card(C) + Card(E)
        BY <1>18, <2>3
    <2>5. Card(H) = Card(C) + Card(E')
        BY <2>4, <1>4
    <2> QED  (* goal from <1>3 *)
        BY <2>1, <2>5
<1>21. H \in CoversOf(Xinit, Yinit, Leq)
    BY <1>8 DEF IsACoverFrom, CoversOf
<1>22. Card(H) > Card(H3)
    <2>1. Card(H) >= Card(H3)
        <3>1. H \in CoversOf(Xinit, Yinit, Leq)
            BY <1>21
        <3>2. IsAMinCover(H3, Xinit, Yinit, Leq)
            BY <1>17
        <3> QED
            BY <3>1, <3>2, <1>19, HaveCardAsCost,
                MinCoverHasMinCard, ProblemInput
                DEF Card, CoversOf
    <2>2. ASSUME Card(H) = Card(H3)
          PROVE FALSE
        <3>4. IsAMinCover(H, Xinit, Yinit, Leq)
            BY <1>17, HaveCardAsCost, <1>21, <2>2,
                MinCoverEquivCoverCard, ProblemInput,
                FS_Subset DEF CoversOf, Card
        <3> QED
            BY <3>4, <1>20
    <2> QED
        BY <2>1, <2>2, <1>19
<1>23. IsFiniteSet(C) /\ IsFiniteSet(E)
    <2>1. (C \subseteq Y') /\ (Y' \subseteq Z) /\ IsFiniteSet(Z)
        BY <1>7, ProblemInput, MinCoverProperties
            DEF IsAMinCover, TypeInv
    <2>2. IsFiniteSet(C)
        BY <2>1, FS_Subset
    <2>3. (E \in SUBSET Z) /\ IsFiniteSet(Z)
        BY ProblemInput DEF TypeInv
    <2>4. IsFiniteSet(E)
        BY <2>3, FS_Subset
    <2> QED
        BY <2>2, <2>4
<1>24. Card(H) > Card(C) + Card(E)
    BY <1>18, <1>22
<1>25. Card(H) <= Card(C) + Card(E)
    <2>1. (C \cap E) = {}
        <3>1. (Y' \cap E') = {}
            OBVIOUS
        <3>2. (Y' \cap E) = {}
            BY <3>1, <1>4
        <3>3. C \subseteq Y'
            BY <1>3, MinCoverProperties
        <3> QED
            BY <3>2, <3>3
    <2>2. Card(C \cup E) = Card(C) + Card(E)
        <3>1. Cardinality(C \cup E) = Cardinality(C) + Cardinality(E)
                - Cardinality(C \cap E)
            BY <1>23, FS_Union
        <3>2. /\ Cardinality(C) \in Nat
              /\ Cardinality(E) \in Nat
              /\ Cardinality(C \cap E) = 0
            BY <1>23, FS_CardinalityType, <2>1, FS_EmptySet
        <3> QED
            BY <3>1, <3>2 DEF Card
    <2>3. Card(H) <= Card(C \cup E)
        BY <1>7 DEF IsAHat, Card
    <2> QED
        BY <2>2, <2>3
<1> QED  (* goal from <1>20 *)
    BY <1>24, <1>25, <1>19, <1>23, FS_CardinalityType DEF Card


(* Row reduction leaves the set of (minimal) covers unchanged. *)
THEOREM HatIsMinCoverUnchangedByReduceRows ==
    ASSUME
        /\ HatIsMinCover /\ TypeInv
        /\ ReduceRows
    PROVE
        HatIsMinCover'
PROOF
<1>1. SUFFICES
        ASSUME NEW C, NEW H,
            /\ IsAMinCover(C, X', Y', Leq)
            /\ IsAHat(H, C \cup E', Yinit, Leq)
        PROVE
            /\ IsAMinCover(H, Xinit, Yinit, Leq)
            /\ Card(H) = Card(C) + Card(E')
    BY DEF HatIsMinCover, Card
<1>2. /\ E' = E
      /\ X' = RowRed(X, Y)
      /\ Y' = Y
    BY DEF ReduceRows
<1>3. IsAMinCover(C, X, Y, Leq)
    <2>1. IsAMinCover(C, X', Y, Leq)
        BY <1>1, <1>2
    <2>2. X' = MaxCeilings(X, Y, Leq)
        BY <1>2 DEF RowRed
    <2> QED
        BY <2>1, <2>2, ProblemInput, MinCoverProperties,
            MinCoverUnchangedByMaxCeil DEF Z, TypeInv
<1>4. IsAHat(H, C \cup E, Yinit, Leq)
    <2>1. IsAHat(H, C \cup E', Yinit, Leq)
        BY <1>1
    <2>2. E' = E
        BY <1>2
    <2> QED
        BY <2>1, <2>2
<1>5. /\ IsAMinCover(C, X, Y, Leq)
      /\ IsAHat(H, C \cup E, Yinit, Leq)
    BY <1>3, <1>4
<1>6. /\ IsAMinCover(H, Xinit, Yinit, Leq)
      /\ Card(H) = Card(C) + Card(E)
    BY <1>5 DEF HatIsMinCover, Card
<1>7. Card(H) = Card(C) + Card(E')
    <2>1. Card(H) = Card(C) + Card(E)
        BY <1>6
    <2>2. E' = E
        BY <1>2
    <2> QED
        BY <2>1, <2>2
<1>8. QED  (* goal from <1>1 *)
    BY <1>6, <1>7


(* If C is a cover after, then C \cup E' is a cover before. *)
THEOREM HatIsMinCoverUnchangedByRemoveEssential ==
    ASSUME
        /\ TypeInv /\ TypeInv'
        /\ (Y \cap E) = {}
        /\ (i = 3) => /\ X = RowRed(Xold, Y)
                      /\ Y = ColRed(Xold, Yold)
        /\ HatIsMinCover
        /\ RemoveEssential
    PROVE
        HatIsMinCover'
PROOF
<1>14. /\ X = Maxima(X, Leq)
       /\ Y = Maxima(Y, Leq)
    <2>1. /\ X = RowRed(Xold, Y)
          /\ Y = ColRed(Xold, Yold)
        BY DEF RemoveEssential
    <2> QED
        BY <2>1, MaxIsIdempotent DEF RowRed, MaxCeilings, ColRed, MaxFloors
<1> USE DEF Card
<1>1. SUFFICES
        ASSUME NEW Ce, NEW H,
            /\ IsAMinCover(Ce, X', Y', Leq)
            /\ IsAHat(H, Ce \cup E', Yinit, Leq)
        PROVE
            /\ IsAMinCover(H, Xinit, Yinit, Leq)
            /\ Card(H) = Card(Ce) + Card(E')
    BY DEF HatIsMinCover
        (* applied for HatIsMinCover' *)
<1> DEFINE
    Ess == X \cap Y
    C == Ce \cup Ess
<1>2. /\ X' = X \ Ess
      /\ Y' = Y \ Ess
    BY DEF RemoveEssential
<1>3. (Ce \cap Ess) = {}
    <2>1. Ce \subseteq Y'
        BY <1>1, MinCoverProperties
    <2>2. (Y' \cap Ess) = {}
        <3>1. Y' = Y \ Ess
            BY <1>2
        <3> QED
            BY <3>1
    <2> QED
        BY <2>1, <2>2
<1>4. IsAMinCover(C, X, Y, Leq)
    <2>1. X = Maxima(X, Leq)
        BY <1>14
    <2>2. Y = Maxima(Y, Leq)
        BY <1>14
    <2> DEFINE
        Xe == X'
        Ye == Y'
    <2>4. /\ IsAMinCover(Ce, Xe, Ye, Leq)
          /\ Ess = X \cap Y
          /\ Xe = X \ Ess
          /\ Ye = Y \ Ess
        BY <1>1, <1>2 DEF Xe, Ye, Ess

    <2>5. /\ C = Ce \cup Ess
          /\ Ce = C \ Ess

        <3>1. C = Ce \cup Ess
            BY DEF C
        <3>2. Ce = C \ Ess
            <4>1. SUFFICES (Ce \cap Ess) = {}
                BY DEF C
            <4> QED  (* goal from <4>1 *)
                BY <1>3
        <3> QED
            BY <3>1, <3>2
    <2> HIDE DEF C
    <2> QED
        BY <2>1, <2>2, <2>4, <2>5, HaveCardAsCost, ProblemInput,
            MinCoverUnchangedByEssential DEF TypeInv, Z
<1>5. ASSUME
        /\ IsAMinCover(C, X, Y, Leq)
        /\ IsAHat(H, C \cup E, Yinit, Leq)
      PROVE
        /\ IsAMinCover(H, Xinit, Yinit, Leq)
        /\ Card(H) = Card(C) + Card(E)
    BY <1>5 DEF HatIsMinCover
        (* applied for HatIsMinCover *)
<1>6. (Ce \cup E') = (C \cup E)
    <2>1. (Ce \cup E') = (Ce \cup (E \cup Ess))
        <3>1. E' = E \cup Ess
            BY DEF RemoveEssential, Ess
        <3> QED
            BY <3>1
    <2>2. (Ce \cup (E \cup Ess)) = ((Ce \cup Ess) \cup E)
        OBVIOUS
    <2>3. ((Ce \cup Ess) \cup E) = (C \cup E)
        BY DEF C
    <2> QED
        BY <2>1, <2>2, <2>3
<1>7. IsAHat(H, C \cup E, Yinit, Leq)
    <2>1. IsAHat(H, Ce \cup E', Yinit, Leq)
        BY <1>1
    <2>2. (Ce \cup E') = (C \cup E)
        BY <1>6
    <2> QED
        BY <2>1, <2>2
<1>8. /\ IsAMinCover(C, X, Y, Leq)
      /\ IsAHat(H, C \cup E, Yinit, Leq)
    BY <1>4, <1>7
<1>9. /\ IsAMinCover(H, Xinit, Yinit, Leq)
      /\ Card(H) = Card(C) + Card(E)
    BY <1>8, <1>5
<1>10. /\ IsFiniteSet(H) /\ IsFiniteSet(Ce)
       /\ IsFiniteSet(E) /\ IsFiniteSet(Ess)
    <2>1. H \subseteq Yinit
        BY <1>1 DEF IsAHat
    <2>2. Ess \subseteq Y
        BY DEF Ess
    <2>3. Ce \subseteq Y'
        BY <1>1, MinCoverProperties
    <2>4. Y \in SUBSET Z /\ E \in SUBSET Z
        BY DEF TypeInv
    <2>5. Y' \in SUBSET Z
        BY DEF TypeInv
    <2>6. Yinit \subseteq Z
        BY ProblemInput
    <2>7. IsFiniteSet(Z)
        BY ProblemInput
    <2>8. /\ IsFiniteSet(Y) /\ IsFiniteSet(Yinit)
          /\ IsFiniteSet(Y') /\ IsFiniteSet(E)
        BY <2>4, <2>5, <2>6, <2>7, FS_Subset
    <2>9. /\ IsFiniteSet(Ce) /\ IsFiniteSet(Ess) /\ IsFiniteSet(H)
        BY <2>1, <2>2, <2>3, <2>8, FS_Subset
    <2> QED
        BY <2>8, <2>9
<1>11. Card(C) = Card(Ce) + Card(Ess)
    <2>1. C = Ce \cup Ess
        BY DEF C
    <2>2. (Ce \cap Ess) = {}
        BY <1>3
    <2>3. IsFiniteSet(Ce)
        BY <1>10
    <2>4. IsFiniteSet(Ess)
        BY <1>10
    <2> QED
        BY <2>1, <2>2, <2>3, <2>4, FS_UnionDisjoint
<1>12. Card(H) = (Card(Ce) + Card(Ess)) + Card(E)
    <2>1. Card(H) = Card(C) + Card(E)
        BY <1>9
    <2>2. Card(C) = Card(Ce) + Card(Ess)
        BY <1>11
    <2> QED
        BY <2>1, <2>2
<1>13. /\ (Card(H) \in Nat) /\ (Card(Ce) \in Nat)
       /\ (Card(E) \in Nat) /\ (Card(Ess) \in Nat)
    BY <1>10, FS_CardinalityType
<1>15. Card(H) = Card(Ce) + Card(E')
    <2>1. Card(H) = Card(Ce) + (Card(Ess) + Card(E))
        BY <1>12, <1>13
    <2>2. Card(E') = Card(Ess) + Card(E)
        <3>1. E' = (Ess \cup E)
            BY DEF RemoveEssential, Ess
        <3>2. (Ess \cap E) = {}
            <4>1. Ess = (X \cap Y)
                BY DEF Ess
            <4>2. Ess \subseteq Y
                BY <4>1
            <4>3. (Y \cap E) = {}
                OBVIOUS
            <4> QED
                BY <4>2, <4>3
        <3>3. IsFiniteSet(E) /\ IsFiniteSet(Ess)
            BY <1>10
        <3> QED
            BY <3>1, <3>2, <3>3, FS_UnionDisjoint
    <2> QED
        BY <2>1, <2>2
<1> QED  (* goal from <1>1 *)
    BY <1>9, <1>15


(* Any minimal covers of X, Y yield (via Hat) a minimal cover
of the initial problem Xinit, Yinit.
*)
THEOREM RecoveringMinCover ==
    Spec => []HatIsMinCover
PROOF
<1> DEFINE
    InvYE == (Y \cap E) = {}
    InvMaxAtEss == (i = 3) => /\ X = RowRed(Xold, Y)
                              /\ Y = ColRed(Xold, Yold)
    Nx ==
        /\ Next
        /\ TypeInv /\ TypeInv'
        /\ InvYE /\ InvYE'
        /\ InvMaxAtEss
        /\ Refines(Xinit, X \cup E, Leq)
        /\ Refines(Y \cup E, Yinit, Leq)
<1> HIDE DEF InvYE, InvMaxAtEss, Nx
<1>1. ASSUME
        /\ Nx
        /\ HatIsMinCover
      PROVE
        HatIsMinCover'
    BY <1>1, HatIsMinCoverUnchangedByReduceColumns,
        HatIsMinCoverUnchangedByReduceRows,
        HatIsMinCoverUnchangedByRemoveEssential
        DEF Next, InvYE, InvMaxAtEss, Nx
<1>2. ASSUME /\ HatIsMinCover
             /\ [Nx]_vars
      PROVE HatIsMinCover'
    BY <1>1, <1>2 DEF HatIsMinCover, vars
<1>3. (HatIsMinCover /\ [][Nx]_vars)  =>  []HatIsMinCover
    BY <1>2, PTL
<1>4. (Init /\ [][Nx]_vars)  =>  []HatIsMinCover
    BY <1>3, HatIsMinCoverInit
<1>5. \/ ~ /\ Spec
           /\ []TypeInv
           /\ []InvYE
           /\ []InvMaxAtEss
           /\ []Refines(Xinit, X \cup E, Leq)
           /\ []Refines(Y \cup E, Yinit, Leq)
      \/ []HatIsMinCover
    BY <1>4, PTL DEF Nx, Spec
<1>6. Spec => []InvMaxAtEss
    <2>1.  \/ ~ \/ i # 3
                \/ /\ X = RowRed(Xold, Y)
                   /\ Y = ColRed(Xold, Yold)
           \/ InvMaxAtEss
        BY DEF InvMaxAtEss
    <2> QED
        BY <2>1, MaximalAtEss, PTL
<1> QED
    BY <1>5, TypeOK, noYcapE, <1>6,
        XinitRefinesXE, YERefinesYinit, PTL
        DEF InvYE

--------------------------------------------------------------------------------
(* Proof that covering X with elements from Y remains feasible. *)


THEOREM RemainsFeasible ==
    Spec  =>  []IsFeasible
PROOF
<1> DEFINE
    InvMaxAtEss == (i = 3) => /\ X = RowRed(Xold, Y)
                              /\ Y = ColRed(Xold, Yold)
<1>1. ASSUME InitIsFeasible /\ Init /\ TypeInv
      PROVE IsFeasible

    <2> DEFINE
        Covers == CoversOf(X, Y, Leq)
        PZ == SUBSET Z
    <2> HIDE DEF Covers, PZ
    <2>1. SUFFICES \E Q \in Covers:  IsMinimal(Q, Covers, CostLeq)
        BY <2>1 DEF IsFeasible, IsAMinCover, Covers
    <2>2. Covers # {}
        <3>1. PICK C:  IsACoverFrom(C, Xinit, Yinit, Leq)
            BY <1>1 DEF InitIsFeasible
        <3>2. (X = Xinit)  /\  (Y = Yinit)
            BY <1>1 DEF Init
        <3> QED
            BY <3>1, <3>2, MinCoverProperties
                DEF Covers, CoversOf, IsACoverFrom
    <2>3. /\ Covers \subseteq SUBSET Z
          /\ IsFiniteSet(Covers)
          /\ IsFiniteSet(Z)
        <3>1. Covers \subseteq SUBSET Y
            BY DEF Covers, CoversOf
        <3>2. /\ Y \subseteq Z
              /\ IsFiniteSet(Z)
            BY <1>1, ProblemInput, FS_Subset DEF TypeInv
        <3> QED
            BY <3>1, <3>2, FS_SUBSET, FS_Subset

    <2> DEFINE
        S == {Cardinality(u):  u \in Covers}
        leq == [c \in S \X S |-> c[1] <= c[2]]
    <2> HIDE DEF S, leq
    <2>7. /\ S \in SUBSET Nat
          /\ S # {}
          /\ IsFiniteSet(S)
          /\ S = Support(leq)
        <4>1. S \in SUBSET Nat
            <5>1. SUFFICES ASSUME NEW u \in Covers
                           PROVE Cardinality(u) \in Nat
                BY <5>1 DEF S
            <5>2. u \in SUBSET Z
                BY <5>1, <2>3
            <5> QED  (* goal from <5>1 *)
                BY <2>3, FS_Subset, FS_CardinalityType
        <4>2. S = Support(leq)
            BY SupportOfSymmetricDomain DEF leq
        <4>3. S # {}
            BY <2>2 DEF S
        <4>4. IsFiniteSet(S)
            BY ImageOfFinite, <2>3 DEF S
        <4> QED
            BY <4>1, <4>2, <4>3, <4>4
    <2>4. PICK v \in S:  IsMinimal(v, S, leq)
        <3>2. IsTransitive(leq)
            <4>1. SUFFICES
                    ASSUME
                        NEW x \in S, NEW y \in S, NEW z \in S,
                        leq[ << x, y >> ] /\ leq[ << y, z >> ]
                    PROVE
                        leq[ << x, z >> ]
                BY <4>1, <2>7 DEF IsTransitive
            <4>2. x <= y  /\  y <= z
                BY <4>1 DEF leq
            <4>3. x \in Nat  /\  y \in Nat  /\  z \in Nat
                BY <4>1, <2>7
            <4>4. x <= z
                BY <4>2, <4>3
            <4> QED  (* goal from <4>1 *)
                BY <4>1, <4>4 DEF leq
        <3>3. IsAntiSymmetric(leq)
            <4>1. SUFFICES
                    ASSUME
                        NEW x \in S, NEW y \in S,
                        leq[x, y]  /\  x # y
                    PROVE
                        ~ leq[y, x]
                BY <4>1, <2>7 DEF IsAntiSymmetric
            <4>2. x <= y
                BY <4>1 DEF leq
            <4>3. x < y
                BY <4>1, <4>2, <2>7
            <4>4. ~ (y <= x)
                <5>1. x \in Nat  /\  y \in Nat
                    BY <4>1, <2>7
                <5> QED
                    BY <4>3, <5>1
            <4> QED
                BY <4>4, <4>1 DEF leq
        <3> QED
            BY <2>7, <3>2, <3>3, FiniteSetHasMinimal

    <2>5. PICK Q \in Covers:  v = Cardinality(Q)
        BY <2>4 DEF S
    <2>6. ASSUME NEW W \in Covers, CostLeq[ << W, Q >> ]
          PROVE CostLeq[ << Q, W >> ]
        <3> DEFINE u == Cardinality(W)
        <3> HIDE DEF u
        <3>1. u \in S
            BY <2>6 DEF u, S
        <3>2. leq[u, v] => leq[v, u]
            BY <2>4, <3>1 DEF IsMinimal
        <3>3. v <= u
            <4>1. u \in Nat  /\  v \in Nat
                BY <2>4, <3>1, <2>7
            <4>2. (u <= v)  =>  (v <= u)
                BY <3>2, <2>4, <3>1 DEF leq
            <4> QED
                BY <4>1, <4>2
        <3>4. Cardinality(Q) <= Cardinality(W)
            BY <3>3, <2>5 DEF u
        <3> QED
            BY <2>5, <2>6, <3>4, HaveCardAsCost,
                <2>3, CostLeqToCard DEF Z
    <2> QED  (* goal from <2>1 *)
        BY <2>5, <2>6 DEF IsMinimal

<1>2. ASSUME
        /\ IsFeasible
        /\ TypeInv /\ TypeInv'
        /\ InvMaxAtEss
        /\ Next
      PROVE IsFeasible'

    <2>1. ASSUME
            IsFeasible /\ TypeInv /\ ReduceColumns
          PROVE
            IsFeasible'
        <3>1. PICK C:  IsAMinCover(C, X, Y, Leq)
            BY <2>1 DEF IsFeasible
        <3> DEFINE
            Cf == Floors(C, X, Leq)
            Yf == Floors(Y, X, Leq)
            Cm == MaxHat(Cf, Yf, Leq)
            Ymf == Maxima(Yf, Leq)
        <3> HIDE DEF Cf, Yf, Cm, Ymf
        <3>2. /\ IsACompleteLattice(Leq)
              /\ IsAPartialOrder(Leq)
              /\ CardinalityAsCost(Z)
              /\ X \subseteq Z
              /\ Y \subseteq Z
              /\ Yf \subseteq Z
              /\ IsFiniteSet(Y)
              /\ IsFiniteSet(Z)
            BY <2>1, ProblemInput, HaveCardAsCost,
                FS_Subset, FloorsIsSubset
                DEF IsACompleteLattice, TypeInv, Z, Yf
        <3>3. IsAMinCover(Cf, X, Yf, Leq)
            BY <3>1, <3>2, MinCoverProperties,
                FloorPreservesMinCover DEF Cf, Yf, Z
        <3>4. IsAMinCover(Cm, X, Ymf, Leq)
            BY <3>2, <3>3, MaxHatOfMinCoverIsAMinCover DEF Cm, Ymf, Z
        <3>5. /\ X' = X
              /\ Y' = Ymf
            BY <2>1 DEF ReduceColumns, ColRed, Ymf, Yf, MaxFloors
        <3> QED
            BY <3>4, <3>5 DEF IsFeasible

    <2>2. ASSUME
            IsFeasible /\ TypeInv /\ ReduceRows
          PROVE
            IsFeasible'
        BY <2>2, MinCoverUnchangedByMaxCeil,
            ProblemInput, MinCoverProperties
            DEF ReduceRows, RowRed, Z, TypeInv, IsFeasible

    <2>3. ASSUME
            /\ IsFeasible /\ RemoveEssential
            /\ TypeInv /\ TypeInv'
            /\ InvMaxAtEss
          PROVE
            IsFeasible'
        <3>1. /\ X = Maxima(X, Leq)
              /\ Y = Maxima(Y, Leq)
            BY <2>3, MaxIsIdempotent
                DEF InvMaxAtEss, RemoveEssential,
                RowRed, MaxCeilings, ColRed, MaxFloors
        <3>2. /\ IsFiniteSet(Z)
              /\ CardinalityAsCost(Z)
              /\ IsACompleteLattice(Leq)
            BY ProblemInput, HaveCardAsCost
        <3>3. /\ X \subseteq Z
              /\ Y \subseteq Z
            BY <2>3 DEF TypeInv
        <3>4. PICK C:  IsAMinCover(C, X, Y, Leq)
            BY <2>3 DEF IsFeasible
        <3> DEFINE
            Ess == X \cap Y
            Ce == C \ Ess
        <3>6. /\ X' = X \ Ess
              /\ Y' = Y \ Ess
            BY <2>3 DEF RemoveEssential
        <3>5. IsAMinCover(Ce, X', Y', Leq)
            BY <3>1, <3>2, <3>3, <3>4, <3>6,
                RemainsMinCoverAfterRemovingEssential
                DEF Ce, Ess, Z
        <3> QED
            BY <3>5 DEF IsFeasible
    <2> QED
        BY <1>2, <2>1, <2>2, <2>3 DEF Next
<1>3. ASSUME /\ IsFeasible
             /\ [TypeInv /\ TypeInv' /\ InvMaxAtEss /\ Next]_vars
      PROVE IsFeasible'
    BY <1>2, <1>3 DEF IsFeasible, vars
<1> QED
    <2>1. \/ ~ /\ IsFeasible
               /\ [][TypeInv /\ TypeInv' /\ InvMaxAtEss /\ Next]_vars
          \/ []IsFeasible
        BY <1>3, PTL
    <2>2. \/ ~ /\ Init /\ TypeInv
               /\ [][TypeInv /\ TypeInv' /\ InvMaxAtEss /\ Next]_vars
          \/ []IsFeasible
        BY <1>1, <2>1, ProblemInput
    <2>3. \/ ~ /\ Init
               /\ []TypeInv
               /\ []InvMaxAtEss
               /\ [][Next]_vars
          \/ []IsFeasible
        BY <2>2, PTL
    <2>4. \/ ~ /\ Spec
               /\ []TypeInv
               /\ []InvMaxAtEss
          \/ []IsFeasible
        BY <2>3 DEF Spec
    <2>5. Spec  =>  []InvMaxAtEss
        <3>1.  \/ ~ \/ i # 3
                    \/ /\ X = RowRed(Xold, Y)
                       /\ Y = ColRed(Xold, Yold)
               \/ InvMaxAtEss
            BY DEF InvMaxAtEss
        <3> QED
            BY <3>1, MaximalAtEss, PTL
    <2> QED
        BY <2>4, <2>5, TypeOK, PTL

================================================================================
(* Proofs checked with TLAPS version 1.4.3 *)




(* The below theorem has been checked by a human. *)
--------------------------------------------------------------------------------
(* Reasoning about termination using the variant. *)


(* Suppose that the cardinalities of both X and Y remained unchanged.
It should be E = {}, otherwise both X and Y would have decreased in
cardinality. So X, Y have unchanged cardinality through the row and column
reductions. BY Fixpoint, the reductions leave both X and Y unchanged.
*)
THEOREM Termination ==
    Spec => ReachesFixpoint
PROOF
<1> USE DEF Spec, Next, ReduceColumns, ReduceRows, RemoveEssential,
        Cardinality
<1> Spec  =>  []<><< Next >>_i
    <2>1. Spec => [] ENABLED Next
        OMITTED
    <2>2. Spec => []<><< Next >>_vars
        BY <2>1
    <2>3. Next => (i' # i)
        BY DEF Next, ReduceColumns, ReduceRows, RemoveEssential
    <2>4. << Next >>_vars  =>  << Next >>_i
        BY <2>3 DEF vars
    <2> QED
        BY <2>2, <2>3
<1>1. Spec => [](X \subseteq Z /\ Y \subseteq Z)
    OMITTED
<1>2. /\ Xinit \subseteq Z /\ Yinit \subseteq Z
      /\ IsFiniteSet(Xinit) /\ IsFiniteSet(Yinit)
    OMITTED
<1>3. Spec => <>[][ /\ Cardinality(X) = Cardinality(X')
                    /\ Cardinality(Y) = Cardinality(Y') ]_vars
    <2>1. Spec => [](IsFiniteSet(X) /\ IsFiniteSet(Y))
        <3>1. IsFiniteSet(Z)
            OBVIOUS
        <3> QED
            BY <1>1, <3>1
    <2>2. [][ /\ Cardinality(X') <= Cardinality(X)
              /\ Cardinality(X) \in Nat ]_vars
        BY <2>1, MaxCeilSmaller
            (* ReduceColumns => (Card(X') = Card(X)) *)
            (* ReduceRows => (Card(X') <= Card(X)) *)
            (* RemoveEssential => (Card(X') <= Card(X)) *)
    <2>3. [][ /\ Cardinality(Y') <= Cardinality(Y)
              /\ Cardinality(Y) \in Nat ]_vars
        BY <2>1, MaxFloorSmaller
            (* ReduceColumns => (Card(Y') <= Card(Y)) *)
            (* ReduceRows => (Card(Y') = Card(Y)) *)
            (* RemoveEssential => (Card(Y') <= Card(Y)) *)
    <2> QED
        BY <2>2, <2>3  (* Well-founded induction *)
<1>4. \/ ~ Spec
      \/ [] \/ i # 3
            \/ /\ X = MaxCeilings(Xold, Y, Leq)
               /\ Y = MaxFloors(Yold, Xold, Leq)
    OMITTED
<1>5. \/ ~ Spec
      \/ <>[] \/ i # 3
              \/ /\ X = MaxCeilings(Xold, Y, Leq)
                 /\ Y = MaxFloors(Yold, Xold, Leq)
    BY <1>3, <1>4
<1>6. \/ ~ Spec
      \/ <>[] \/ i # 3
              \/ (X \cap Y) = {}
    BY <1>3 DEF RemoveEssential  (* otherwise X, Y would decrease
        because Ess == X \cap Y would be non-empty. *)
<1>7. \/ ~ Spec
      \/ <>[] \/ i # 3
              \/ /\ X = MaxCeilings(Xold, Y, Leq)
                 /\ Y = MaxFloors(Yold, Xold, Leq)
                 /\ (X \cap Y) = {}
    BY <1>5, <1>6
<1>8. \/ ~ Spec
      \/ <>[][ \/ i # 3
               \/ /\ X = MaxCeilings(Xold, Y, Leq)
                  /\ Y = MaxFloors(Yold, Xold, Leq)
                  /\ UNCHANGED << X, Y >> ]_vars
    BY <1>7
<1>9. \/ ~ Spec
      \/ <>[][ \/ i # 3
               \/ /\ X = MaxCeilings(X, Y, Leq)
                  /\ Y = MaxFloors(Y, X, Leq)
                  /\ UNCHANGED << X, Y >> ]_vars
    BY <1>8, Fixpoint
<1>10. \/ ~ Spec
       \/ <>[][ \/ i # 1
                \/ /\ X = MaxCeilings(X, Y, Leq)
                   /\ Y = MaxFloors(Y, X, Leq) ]_vars
    BY <1>9 DEF Next, RemoveEssential
<1>11. \/ ~ Spec
       \/ <>[][ \/ i # 1
                \/ /\ X = MaxCeilings(X, Y, Leq)
                   /\ Y = MaxFloors(Y, X, Leq)
                   /\ Y' = MaxFloors(Y, X, Leq)
                   /\ UNCHANGED X ]_vars
    BY <1>10 DEF ReduceColumns, ColRed
<1>12. \/ ~ Spec
       \/ <>[][ \/ i # 1
                \/ /\ X = MaxCeilings(X, Y, Leq)
                   /\ Y = MaxFloors(Y, X, Leq)
                   /\ UNCHANGED << X, Y >> ]_vars
    BY <1>11
<1>13. \/ ~ Spec
       \/ <>[][ \/ i # 2
                \/ /\ X = MaxCeilings(X, Y, Leq)
                   /\ Y = MaxFloors(Y, X, Leq)
                   /\ X' = MaxCeilings(X, Y, Leq)
                   /\ UNCHANGED Y ]_vars
    BY <1>12 DEF ReduceRows, RowRed
<1>14. \/ ~ Spec
       \/ <>[][ \/ i # 2
                \/ /\ X = MaxCeilings(X, Y, Leq)
                   /\ Y = MaxFloors(Y, X, Leq)
                   /\ UNCHANGED << X, Y >> ]_vars
    BY <1>13
<1>15. Spec => <>[][ (i \in 1..3) => UNCHANGED << X, Y >> ]_vars
    BY <1>9, <1>12, <1>14
<1>16. Spec => [](i \in 1..3)
    BY TypeOK
<1> QED
    BY <1>15, <1>16 DEF vars, ReachesFixpoint


================================================================================
