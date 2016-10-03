------------------------------- MODULE OpenSystems -----------------------------
(* Operators for creating open systems. *)


(* The TLA+ operator -+-> expressed within the logic [1, p.337].
[1] Leslie Lamport, "Specifying systems", Addison-Wesley, 2002
*)
WhilePlus(A(_, _), G(_, _), x, y) ==
    \AA b:  \/ ~ /\ b \in BOOLEAN
                 /\ [][b' = FALSE]_b
                 /\ \EE u, v:  /\ A(u, v)
                               /\ [] (b => (<< u, v >> = << x, y >>))
            \/ \EE u, v:
                /\ G(u, v)
                /\ << u, v >> = << x, y >>
                /\ [][ b => (<< u', v' >> = << x', y' >>) ]_<< b, u, v, x, y >>

(* A variant of the WhilePlus operator. *)
WhilePlusHalf(A(_, _), G(_, _), x, y) ==
    \AA b:  \/ ~ /\ b \in BOOLEAN     (* b starts in BOOLEAN and *)
                 /\ [][b' = FALSE]_b  (* if b ever changes, it becomes FALSE *)
                 /\ \EE u, v:  /\ A(u, v)
                               /\ [] (b => (<< u, v >> = << x, y >>))
            \/ \EE u, v:
                /\ G(u, v)
                /\ [] (b => (<< u, v >> = << x, y >>))
                /\ [][ b => (v' = y') ]_<< b, v, y >>

(* An operator that forms an open system from the closed system that the
temporal property P(x, y) describes.
*)
Unzip(P(_, _), x, y) == WhilePlusHalf(P, P, x, y)

================================================================================
(* Copyright 2016-2017 by California Institute of Technology. *)
(* All rights reserved. Licensed under BSD-3. *)
