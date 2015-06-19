[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]


About
=====

A package for automata-theoretic and symbolic algorithms that manipulate omega-regular languages.
It contains:

- synthesis algorithm that solves GR(1) games
- parser of temporal logic
- translation from past to future LTL, using temporal testers
- classes for enumerated and semi-symbolic automata and transition systems
- class for symbolic automata that includes compiling methods that take care for initializing and maintaining the underlying BDDs via bitblasting of first-order temporal logic
- flattening of semi-symbolic transition systems to LTL

User documentation can be found in [`doc/doc.md`](https://github.com/johnyf/omega/blob/master/doc/doc.md).


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


License
=======
[BSD-3](http://opensource.org/licenses/BSD-3-Clause), see `LICENSE` file.


[build_img]: https://travis-ci.org/johnyf/omega.svg?branch=master
[travis]: https://travis-ci.org/johnyf/omega
[coverage]: https://coveralls.io/repos/johnyf/omega/badge.svg?branch=master
[coveralls]: https://coveralls.io/r/johnyf/omega?branch=master