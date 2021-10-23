[![Build Status][build_img]][ci]


About
=====

A package of symbolic algorithms using binary decision diagrams (BDDs)
for synthesizing implementations from [temporal logic specifications][specs].
This is useful for designing systems, especially vehicles that carry humans.


- [Synthesis][synthesis] algorithms for [Moore][moore] or [Mealy][mealy]
  implementations of:

  - [generalized Streett(1)][streett1] specifications (known as [GR(1)][gr1])
  - generalized Rabin(1) specifications ([counter-strategies][rabin1] to GR(1))
  - detection of trivial realizability in GR(1) specifications.

  See `omega.games.gr1` and the example `gr1_synthesis_intro`.


- Enumeration of state machines (as `networkx` graphs) from the synthesized
  symbolic implementations. See `omega.games.enumeration`.


- Facilities to simulate the resulting implementations with little and
  readable user code. See `omega.steps` and the example `moore_moore`.


- Code generation for the synthesized *symbolic* implementations.
  This code is correct-by-construction. See `omega.symbolic.codegen`.


- *Minimal covering* with a symbolic algorithm to find a minimal cover, and to
  enumerate all minimal covers. Used to convert BDDs to *minimal* formulas.
  See `omega.symbolic.cover` and `omega.symbolic.cover_enum`, and the
  example `minimal_formula_from_bdd`.


- [First-order][fol] [linear temporal logic][LTL] (LTL) with
  [rigid quantification][rigid quantification] and substitution.
  See `omega.logic.lexyacc`, `omega.logic.ast`, and `omega.logic.syntax`.


- [Bitblaster][bitblasting] of quantified integer arithmetic (integers -> bits).
  See `omega.logic.bitvector`.


- Translation from [past][past LTL] to future LTL, using
  [temporal testers][temporal testers]. See `omega.logic.past`.


- Symbolic automata that manage first-order formulas by seamlessly using
  [binary decision diagrams][bdd] (BDDs) underneath. You can:

  - declare variables and constants
  - translate:
    1. formulas to BDDs and
    2. BDDs to *minimal* formulas via minimal covering
  - quantify
  - substitute
  - prime/unprime variables
  - get the support of predicates
  - pick satisfying assignments (or work with iterators)
  - define operators

  See `omega.symbolic.temporal` and `omega.symbolic.fol` for more details.


- Facilities to write symbolic fixpoint algorithms.
  See `omega.symbolic.fixpoint` and `omega.symbolic.prime`, and the example
  `reachability_solver`.


- Conversion from graphs annotated with formulas to temporal logic formulas.
  These graphs can help specify transition relations.
  The translation is in the spirit of
  [predicate-action diagrams][tla-in-pictures].

  See `omega.symbolic.logicizer` and `omega.automata` for more details, and
  the example `symbolic`.


- Enumeration and plotting of state predicates and actions represented as BDDs.
  See `omega.symbolic.enumeration`.


Documentation
=============

In  [`doc/doc.md`][doc].


Examples
========

```python
import omega.symbolic.fol as _fol

ctx = _fol.Context()
ctx.declare(
    x=(0, 10),
    y=(-2, 5),
    z='bool')
u = ctx.add_expr(
    r'(x <= 2) /\ (y >= -1)')
v = ctx.add_expr(
    r'(y <= 3) => (x > 7)')
r = u & ~ v
expr = ctx.to_expr(r)
print(expr)
```


Installation
============

```
pip install omega
```

The package and its dependencies are pure Python.

For solving demanding games, install the [Cython][cython] module `dd.cudd`
that interfaces to [CUDD][cudd].
Instructions are available [at `dd`][dd].


License
=======
[BSD-3][bsd3], see `LICENSE` file.


[specs]: https://lamport.azurewebsites.net/tla/book-02-08-08.pdf
[synthesis]: https://doi.org/10.1007/BFb0035748
[moore]: https://web.archive.org/web/20120216141113/http://people.mokk.bme.hu/~kornai/termeszetes/moore_1956.pdf
[mealy]: https://doi.org/10.1002/j.1538-7305.1955.tb03788.x
[streett1]: https://doi.org/10.1016/j.ic.2005.01.006
[gr1]: https://doi.org/10.1007/11609773_24
[rabin1]: https://online.tugraz.at/tug_online/voe_main2.getvolltext?pCurrPk=47554
[fol]: https://en.wikipedia.org/wiki/First-order_logic
[past LTL]: https://doi.org/10.1007/3-540-15648-8_16
[LTL]: https://doi.org/10.1109/SFCS.1977.32
[temporal testers]: https://doi.org/10.1007/978-3-540-69850-0_11
[rigid quantification]: https://doi.org/10.1007/978-1-4612-4222-2
[bitblasting]: https://doi.org/10.1007/978-3-540-74105-3
[bdd]: https://doi.org/10.1109/TC.1986.1676819
[tla-in-pictures]: https://doi.org/10.1109/32.464544
[doc]: https://github.com/tulip-control/omega/blob/main/doc/doc.md
[cython]: https://en.wikipedia.org/wiki/Cython
[cudd]: http://vlsi.colorado.edu/~fabio/CUDD
[dd]: https://github.com/tulip-control/dd#cython-bindings
[bsd3]: https://opensource.org/licenses/BSD-3-Clause

[build_img]: https://github.com/tulip-control/omega/actions/workflows/main.yml/badge.svg?branch=main
[ci]: https://github.com/tulip-control/omega/actions
