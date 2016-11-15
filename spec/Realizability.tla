------------------------- MODULE Realizability -------------------------------
(* A definition of what it means for a function to realize a property.

A synthesizer first proves:
  THEOREM Realizability(phi, mu)!IsRealizable


References
==========

Ioannis Filippidis, Richard M. Murray
    "Formalizing synthesis in TLA+"
    Technical Report CaltechCDSTR:2016.004
    California Institute of Technology, Pasadena, CA, 2016
    http://resolver.caltech.edu/CaltechCDSTR:2016.004

Leslie Lamport
    "Miscellany"
    21 April 1991, note sent to TLA mailing list
    http://lamport.org/tla/notes/91-04-21.txt
*)
EXTENDS FiniteSets
CONSTANTS phi(_, _), mu(_, _)
(*
STATE mu(_, _)
TEMPORAL phi(_, _)
*)

IsAFunction(f) ==
    f = [u \in DOMAIN f |-> f[u]]

------------------------- MODULE Inner ---------------------------------------
VARIABLES x, y
CONSTANTS f, g, m0

Realization(m) ==
    LET
        v == << m, x, y >>
        A == /\ x' = f[v]
             /\ m' = g[v]
    IN
        /\ m = m0
        /\ [][ mu(v, v') => A ]_v
        /\ WF_<< m, x >> ( mu(v, v') /\ A)

Realize ==
        /\ IsAFunction(f) /\ IsFiniteSet(DOMAIN f)
        /\ IsAFunction(g) /\ IsFiniteSet(DOMAIN g)
        /\ (\EE m:  Realization(m)) => phi(x, y)
==============================================================================

Inner(f, g, m0, x, y) == INSTANCE Inner

IsRealization(f, g, m0) ==
    \AA x, y:
        Inner(f, g, m0, x, y)!Realize

IsRealizable ==
    \E f, g, m0:
        IsRealization(f, g, m0)

==============================================================================
