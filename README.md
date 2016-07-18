[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]


About
=====

A package of symbolic algorithms for solving games of infinite duration.
It can be used to generate software from temporal logic specifications.
This is useful for designing systems, especially vehicles that carry humans.

It contains:

- Synthesis algorithms for:
  - generalized Streett(1) games (known as GR(1))
  - generalized Rabin(1) games (counter-strategies to GR(1))
  - detection of trivial realizability in GR(1) games.
- Parser of [linear temporal logic](http://dx.doi.org/10.1109/SFCS.1977.32) (LTL).
- Translation from past to future LTL, using [temporal testers](http://doi.org/10.1007/978-3-540-69850-0_11).
- Bitblaster of first-order temporal logic (integers -> bits).
- Symbolic automata that include:
  - methods that compile to, and maintain, the underlying binary decision diagrams (BDDs)
  - functions for generatining primed variables, and BDD orderings.
- Semi-enumerated automata (and "transition systems").
- Flattening of semi-enumerated transition systems to LTL.
- Enumeration / plotting of BDDs representing sets and (transition) relations.


Documentation
=============

In  [`doc/doc.md`](https://github.com/johnyf/omega/blob/master/doc/doc.md).


Installation
============

Either with:

```
pip install omega
```

or

```
python setup.py install
```

The package and its dependencies are pure Python.

For solving demanding games, install the [Cython](https://en.wikipedia.org/wiki/Cython) module `dd.cudd`, which links to [CUDD](http://vlsi.colorado.edu/~fabio/CUDD). Instructions are available [at `dd`](https://github.com/johnyf/dd#cython-bindings).


License
=======
[BSD-3](http://opensource.org/licenses/BSD-3-Clause), see `LICENSE` file.


[build_img]: https://travis-ci.org/johnyf/omega.svg?branch=master
[travis]: https://travis-ci.org/johnyf/omega
[coverage]: https://coveralls.io/repos/johnyf/omega/badge.svg?branch=master
[coveralls]: https://coveralls.io/r/johnyf/omega?branch=master
