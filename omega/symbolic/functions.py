"""Functional synthesis.

Convert a predicate over input and output variables to multiple predicates
that depend only on input variables, one predicate for each output variable.

For example, given a BDD for the predicate `f(x1, x2, y1, y2)` where `x1, x2`
are regarded as inputs and `y1, y2` as outputs, create two BDDs for the
predicates `g(x1, x2)` and `h(x1, x2)` such that

```
\/ ~ /\ y1 = g(x1, x2)
     /\ y2 = h(x1, x2)
\/ f(x1, x2, y1, y2)
```


References
==========

Roderick Bloem, Barbara Jobstmann, Nir Piterman,
Amir Pnueli, Yaniv Sa'ar
    "Synthesis of reactive(1) designs"
    Journal of Computer and System Sciences
    Vol.78, No.3, pp.911--938, 2012
"""
# Copyright 2016-2017 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
try:
    from dd import cudd as _bdd
except ImportError:
    _bdd = None


def make_functions(r, vrs, bdd):
    """Extract functions for `vrs` from relation `r`.

    @param r: relation
    @param vrs: variables to extract functions for.
        These variables should be Boolean-valued, and
        declared in the manager `bdd`.
    @type bdd: `BDD`

    @return: `dict(function=g, care_set=care)` where
        `g` and `care` are BDD nodes.
    """
    supp = bdd.support(r)
    outputs = set(vrs)
    outputs &= supp
    functions = dict()
    for yp in set(outputs):
        outputs.remove(yp)
        g, care = extract_function(r, yp, outputs, bdd)
        sub = {yp: g}
        r = bdd.let(sub, r)
        functions[yp] = dict(function=g, care_set=care)
        # assert
        support = bdd.support(r)
        assert yp not in support, (yp, support)
        support = bdd.support(g)
        assert yp not in support, (yp, support)
    # no `vrs` in any support
    for d in functions.values():
        g = d['function']
        support = bdd.support(g)
        common = support.intersection(vrs)
        assert not common, (common, support)
    return functions


def extract_function(f, yp, outputs, bdd):
    """Extract function for variabe `yp`."""
    u = bdd.exist(outputs, f)
    p = bdd.let({yp: True}, u)
    n = bdd.let({yp: False}, u)
    # subtract overlap
    p = p & ~ n
    n = n & ~ p
    # optimize cofactors
    supp_p = bdd.support(p)
    supp_u = bdd.support(n)
    inputs = supp_p | supp_u
    for z in inputs:
        pz = bdd.exist(inputs, p)
        nz = bdd.exist(inputs, n)
        disjoint = ((pz & nz) == bdd.false)
        if disjoint:
            p, n = pz, nz
    # restrict
    care = (p & ~ n) | (n & ~ p)
    if _bdd is None:
        g = p
    else:
        g = _bdd.restrict(p, care)
    return g, care


def collect_functions(functions, r=None):
    """Return functions for next values of latches.

    @param functions: `dict` as returned by `make_functions`
    """
    if r is None:
        r = dict()
    r.update(
        (var, d['function'])
        for var, d in functions.items())
    return r


def report_function_statistics(outputs, memory):
    """Print BDD sizes for output and memory BDDs."""
    care = next(outputs.values())['care_set']
    print('care set nodes: {n}'.format(n=len(care)))
    # collect all flip-flops
    functions = list()
    functions.extend(d['function'] for d in outputs.values())
    functions.extend(d['function'] for d in memory.values())
    n = _bdd.count_nodes(functions)
    print('total nodes (shared) in functions: {n}'.format(n=n))
