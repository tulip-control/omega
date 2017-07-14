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

IsAFunction(f) == f = [u \in DOMAIN f |-> f[u]]
IsAFiniteFcn(f) == /\ IsAFunction(f)
                   /\ IsFiniteSet(DOMAIN f)

------------------------- MODULE Inner ---------------------------------------
VARIABLES x, y
CONSTANTS f, g, mem0

Realization(mem) ==
    LET
        v == << mem, x, y >>
        A == /\ x' = f[v]
             /\ mem' = g[v]
    IN
        /\ mem = mem0
        /\ [][ mu(v, v') => A ]_v
        /\ WF_<< mem, x >> ( mu(v, v') /\ A)

Realize ==
        /\ IsAFiniteFcn(f) /\ IsAFiniteFcn(g)
        /\ (\EE mem:  Realization(mem)) => phi(x, y)
==============================================================================

Inner(f, g, mem0, x, y) == INSTANCE Inner

IsRealization(f, g, mem0) ==
    \AA x, y:
        Inner(f, g, mem0, x, y)!Realize

IsRealizable ==
    \E f, g, mem0:
        IsRealization(f, g, mem0)

==============================================================================
