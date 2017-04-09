---------------------------- MODULE FiniteSetFacts -----------------------------
(* Additions to the module `FiniteSetTheorems` from the library of TLAPS.
Some theorems from the module `FiniteSetTheorems` can be found also in
the module `NaiadClockProofFiniteSets` [1, C.5 on p.57].


Author:  Ioannis Filippidis


Reference
=========

[1] Thomas L. Rodeheffer
    "The Naiad Clock Protocol:
        Specification, Model Checking, and Correctness Proof"
    MSR-TR-2013-20, Microsoft Research, Silicon Valley, 2013

--------------------------------------------------------------------------------
Copyright 2017 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
*)
EXTENDS
    FiniteSetTheorems,
    Naturals
(* In order to ensure independence from builtin support of Sequences by TLAPS,
these modules have been developed and checked by replacing the modules
FiniteSets, FiniteSetTheorems, Sequences, SequencesTheorems
with renamed copies, (FiniteSets_copy etc.), and appropriately adjusting
EXTENDS statements where needed. *)


(* Special case of `FS_Union`. *)
COROLLARY FS_UnionDisjoint ==
    ASSUME
        NEW S, NEW T,
        /\ IsFiniteSet(S) /\ IsFiniteSet(T)
        /\ (S \cap T) = {}
    PROVE
        Cardinality(S \cup T) = Cardinality(S) + Cardinality(T)
    PROOF
    <1>1. Cardinality(S \cup T) =
               Cardinality(S) + Cardinality(T) - Cardinality(S \cap T)
        BY FS_Union
    <1>2. Cardinality(S \cap T) = 0
        BY FS_EmptySet
    <1> QED
        BY <1>1, <1>2, FS_CardinalityType


(* A corollary of FS_AddElement. *)
COROLLARY FS_AddElementUpperBound ==
    ASSUME
        NEW S, NEW x,
        IsFiniteSet(S)
    PROVE
        LET Q == S \cup {x}
        IN /\ IsFiniteSet(Q)
           /\ Cardinality(Q) <= Cardinality(S) + 1
    PROOF
    <1> DEFINE Q == S \cup {x}
    <1>1. IsFiniteSet(S)
        OBVIOUS
    <1>2. /\ IsFiniteSet(Q)
          /\ \/ Cardinality(Q) = Cardinality(S)
             \/ Cardinality(Q) = Cardinality(S) + 1
        BY <1>1, FS_AddElement
    <1>3. /\ Cardinality(Q) \in Nat
          /\ Cardinality(S) \in Nat
        BY <1>1, <1>2, FS_CardinalityType
    <1> QED
        BY <1>2, <1>3


(* Using this lemma directly works well. *)
LEMMA ImageOfFinite ==
    ASSUME
        NEW S, NEW Op(_),
        IsFiniteSet(S)
    PROVE
        LET
            Img == { Op(x):  x \in S }
        IN
            /\ IsFiniteSet(Img)
            /\ Cardinality(Img) <= Cardinality(S)
    PROOF
    <1> DEFINE
        Img == { Op(x):  x \in S }
        f == [x \in S |-> Op(x)]
    <1>1. f \in Surjection(S, Img)
        BY DEF Surjection
    <1> QED
        BY <1>1, FS_Surjection


COROLLARY ImageOfFinite2 ==
    ASSUME
        NEW S, NEW arg2, NEW Op(_, _),
        IsFiniteSet(S)
    PROVE
        LET
            Img == { Op(x, arg2):  x \in S }
        IN
            /\ IsFiniteSet(Img)
            /\ Cardinality(Img) <= Cardinality(S)
    PROOF
    BY ImageOfFinite


COROLLARY ImageOfFinite3 ==
    ASSUME
        NEW S, NEW arg2, NEW arg3, NEW Op(_, _, _),
        IsFiniteSet(S)
    PROVE
        LET
            Img == { Op(x, arg2, arg3):  x \in S }
        IN
            /\ IsFiniteSet(Img)
            /\ Cardinality(Img) <= Cardinality(S)
    PROOF
    BY ImageOfFinite

================================================================================
(* Proofs checked with TLAPS version 1.4.3 *)
