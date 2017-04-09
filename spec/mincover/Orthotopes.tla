------------------------------ MODULE Orthotopes -------------------------------
(* Definitions of discrete orthotopic covers.

Author: Ioannis Filippidis

--------------------------------------------------------------------------------
Copyright 2017 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
*)
EXTENDS
    FiniteSets,
    Reals
CONSTANTS Variables, Domain, CareSet


ASSUME IsFiniteSet(Variables)

N == Cardinality(Variables)
Assignments == [Variables -> Int]
ASSUME
    /\ Domain \subseteq Assignments
    /\ Domain # {}
    /\ IsFiniteSet(Domain)
    /\ CareSet \subseteq Domain

Point == Domain \cap CareSet

EndPoint(k) == [1..k -> Assignments]
IsInOrthotope(x, a, b) == \A var \in Variables:
    (a[var] <= x[var]) /\ (x[var] <= b[var])
IsNonEmpty(a, b) == \E x \in Assignments:  IsInOrthotope(x, a, b)
IsInRegion(x, p, q) == \E i \in DOMAIN p:  IsInOrthotope(x, p[i], q[i])
OrthotopicSet(a, b) == { x \in Assignments:  IsInOrthotope(x, a, b) }
Orthotope(Dom) == { OrthotopicSet(a, b):  a, b \in Dom }
SameOver(f, p, q, S) == \A x \in S:  f[x] \equiv IsInRegion(x, p, q)

CONSTANT f
(* p, q define a cover that contains k orthotopes *)
IsMinDNF(k, p, q) ==
    /\ SameOver(f, p, q, Point)
    /\ \A r \in Nat:  \A u, v \in EndPoint(r):  (* u, v define a cover that
            contains r orthotopes *)
        \/ ~ SameOver(f, u, v, Point)  (* not a cover, or *)
        \/ r >= k  (* u, v has at least as many disjuncts as p, q *)


(* Problem: Minimal orthotopic formula in disjunctive normal form for BDD. *)
(* Assumptions about the characteristic function f to cover. *)
ASSUME
    /\ f \in [Assignments -> BOOLEAN]
    /\ \A x \in Assignments \ CareSet:  f[x] = FALSE
THEOREM
    \E k \in Nat:  \E p, q \in EndPoint(k):  IsMinDNF(k, p, q)
PROOF OMITTED  (* some DNF exists, by finiteness of CareSet *)
================================================================================
