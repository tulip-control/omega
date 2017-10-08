[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]


About
=====

A package of symbolic algorithms using binary decision diagrams (BDDs)
for synthesizing implementations from [temporal logic specifications][specs].
This is useful for designing systems, especially vehicles that carry humans.


Features
========

- [Synthesis][synthesis] algorithms for [Moore][moore] or [Mealy][mealy]
  implementations of:

  - [generalized Streett(1)][streett1] specifications (known as [GR(1)][gr1])
  - generalized Rabin(1) specifications ([counter-strategies][rabin1] to GR(1))
  - detection of trivial realizability in GR(1) specifications.

  See `omega.games.gr1`.


- Enumeration of state machines (as `networkx` graphs) from the synthesized
  symbolic implementations. See `omega.games.enumeration`.


- Facilities to simulate the resulting implementations with little and
  readable user code. See `omega.steps`.


- Code generation for the synthesized *symbolic* implementations.
  This code is correct-by-construction.


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
  See `omega.symbolic.fixpoint` and `omega.symbolic.prime`.


- Conversion from graphs annotated with formulas to temporal logic formulas.
  These graphs can help specify transition relations.
  The translation is in the spirit of
  [predicate-action diagrams][tla-in-pictures].

  See `omega.symbolic.logicizer` and `omega.automata` for more details.


- Enumeration and plotting of state predicates and actions represented as BDDs.
  See `omega.symbolic.enumeration`.


Documentation
=============

In  [`doc/doc.md`][doc].


Installation
============

```
pip install omega
```

or

```
python setup.py install
```

The package and its dependencies are pure Python.

For solving demanding games, install the [Cython][cython] module `dd.cudd`
that interfaces to [CUDD][cudd].
Instructions are available [at `dd`][dd].


License
=======
[BSD-3][bsd3], see `LICENSE` file.


[specs]: http://research.microsoft.com/en-us/um/people/lamport/tla/book-02-08-08.pdf
[synthesis]: http://dx.doi.org/10.1007/BFb0035748
[moore]: https://web.archive.org/web/20120216141113/http://people.mokk.bme.hu/~kornai/termeszetes/moore_1956.pdf
[mealy]: http://dx.doi.org/10.1002/j.1538-7305.1955.tb03788.x
[streett1]: http://dx.doi.org/10.1016/j.ic.2005.01.006
[gr1]: http://dx.doi.org/10.1007/11609773_24
[rabin1]: https://online.tugraz.at/tug_online/voe_main2.getvolltext?pCurrPk=47554
[fol]: https://en.wikipedia.org/wiki/First-order_logic
[past LTL]: http://dx.doi.org/10.1007/3-540-15648-8_16
[LTL]: http://dx.doi.org/10.1109/SFCS.1977.32
[temporal testers]: http://doi.org/10.1007/978-3-540-69850-0_11
[rigid quantification]: http://dx.doi.org/10.1007/978-1-4612-4222-2
[bitblasting]: http://dx.doi.org/10.1007/978-3-540-74105-3
[bdd]: http://dx.doi.org/10.1109/TC.1986.1676819
[tla-in-pictures]: http://dx.doi.org/10.1109/32.464544
[doc]: https://github.com/johnyf/omega/blob/master/doc/doc.md
[cython]: https://en.wikipedia.org/wiki/Cython
[cudd]: http://vlsi.colorado.edu/~fabio/CUDD
[dd]: https://github.com/johnyf/dd#cython-bindings
[bsd3]: http://opensource.org/licenses/BSD-3-Clause

[build_img]: https://travis-ci.org/johnyf/omega.svg?branch=master
[travis]: https://travis-ci.org/johnyf/omega
[coverage]: https://coveralls.io/repos/johnyf/omega/badge.svg?branch=master
[coveralls]: https://coveralls.io/r/johnyf/omega?branch=master
