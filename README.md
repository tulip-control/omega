[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]


About
=====

A package of symbolic algorithms for solving games of infinite duration.
It can be used to generate software from [temporal logic specifications][specs].
This is useful for designing systems, especially vehicles that carry humans.

It contains:

- [Synthesis][synthesis] algorithms of [Moore][moore] or [Mealy][mealy] strategies for:
  - [generalized Streett(1)][streett1] games (known as [GR(1)][gr1])
  - generalized Rabin(1) games ([counter-strategies][rabin1] to GR(1))
  - detection of trivial realizability in GR(1) games.
- [First-order][fol] [linear temporal logic][LTL] (LTL) with
  [rigid quantification][rigid quantification] and substitution.
- [Bitblaster][bitblasting] of quantified integer arithmetic (integers -> bits).
- Translation from [past][past LTL] to future LTL, using [temporal testers][temporal testers].
- Symbolic automata that include:
  - methods that compile first-order logic to, and maintain, the underlying [binary decision diagrams][bdd] (BDDs)
  - functions for generatining primed variables, and BDD orderings.
- [Semi-enumerated automata][tla-in-pictures] (and "transition systems").
- Flattening of semi-enumerated transition systems to LTL.
- Enumeration / plotting of BDDs representing sets and actions.


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
