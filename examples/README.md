The examples are:

- `bdd_howto.py`: manipulating formulas that involve integer variables
  using binary decision diagrams, in both ordinary and modal logic.

- `gr1_synthesis_intro.py`: how to specify a Moore system and synthesize
  an implementation using the GR(1) synthesis algorithm.

- `minimal_formula_from_bdd.py`: decompile a BDD as a minimal formula
  in disjunctive normal form (DNF). The BDD encodes a predicate that
  depends on integer-valued variables, so the minimal DNF formula
  involves integers.

- `reachability_solver.py`: writing fixpoint computations to find those
  states from where a particular goal is reachable.

- `symbolic.py`: specify using a graph data structure and create an
  implementation using GR(1) synthesis.

- `choosing_type_hints.py`: The importance of picking sufficiently large
  bitfields to represent each integer-valued variable.

- `inverter`: synthesis of an inverter from a GR(1) specification

- `moore_moore`: synthesis of two Moore implementations, and simulation of
  their assembly.

- `while_plus_half`: realizability of properties expressed with the operator
  `WhilePlusHalf`.
