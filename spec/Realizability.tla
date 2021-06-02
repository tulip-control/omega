------------------------- MODULE Realizability -------------------------------
(* A definition of what it means for a function to realize a property.


References
==========

Ioannis Filippidis, Richard M. Murray
    "Formalizing synthesis in TLA+"
    Technical Report, California Institute of Technology, 2016
    https://resolver.caltech.edu/CaltechCDSTR:2016.004

Leslie Lamport
    "Miscellany"
    21 April 1991, note sent to TLA mailing list
    https://lamport.azurewebsites.net/tla/notes/91-04-21.txt
*)
EXTENDS FiniteSets

IsAFunction(f) == f = [u \in DOMAIN f |-> f[u]]
IsAFiniteFcn(f) == /\ IsAFunction(f)
                   /\ IsFiniteSet(DOMAIN f)

------------------------- MODULE Inner ---------------------------------------
VARIABLES x, y
CONSTANTS f, g, mem0

Realization(mem, e(_, _)) ==
    LET
        v == << mem, x, y >>
        A == /\ x' = f[v]
             /\ mem' = g[v]
    IN
        /\ mem = mem0
        /\ [][ e(v, v') => A ]_v
        /\ WF_<< mem, x >> ( e(v, v') /\ A)

Realize(Phi(_, _), e(_, _)) ==
        /\ IsAFiniteFcn(f) /\ IsAFiniteFcn(g)
        /\ (\EE mem:  Realization(mem, e)) => Phi(x, y)
==============================================================================

Inner(f, g, mem0, x, y) == INSTANCE Inner

IsARealization(f, g, mem0, Phi(_, _), e(_, _)) ==
    \AA x, y:
        Inner(f, g, mem0, x, y)!Realize(Phi, e)

IsRealizable(Phi(_, _), e(_, _)) ==
    \E f, g, mem0:
        IsARealization(f, g, mem0, Phi, e)
==============================================================================
