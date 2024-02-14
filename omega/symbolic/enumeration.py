"""Enumerate symbolically represented sets and relations.

Integers are decoded from binary to decimal.
"""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import copy
import logging
import math

import natsort
import networkx as nx

import omega.logic.bitvector as bv
import omega.logic.syntax as stx
import omega.symbolic.prime as scope


logger = logging.getLogger(__name__)


def dump_relation(
        u, aut,
        care_source=None,
        care_target=None,
        fname='edges.pdf'):
    """Dump graph of relation as PDF."""
    g = relation_to_graph(u, aut, care_source, care_target)
    h, umap = _format_nx(g)
    pd = nx.drawing.nx_pydot.to_pydot(h)
    pd.set_overlap(False)
    pd.write_pdf(fname, prog='neato')


def relation_to_graph(
        u, aut,
        care_source=None,
        care_target=None,
        care_bits=None):
    """Return enumerated graph from relation.

    @param u:
        relation as BDD node
    @param care_source:
        care set for source nodes
    @param care_target:
        care set for target nodes
    @type u, care_source, care_target:
        node in `aut.bdd`
    @rtype:
        `networkx.DiGraph`
    """
    assert u != aut.bdd.false
    t, care_relation = _make_table(u, aut, care_source,
                                   care_target, care_bits)
    c = _enumerate_bdd(u, aut.bdd, t,
                       care_relation, care_bits)
    # to nx graph
    g = nx.DiGraph()
    # fix an order of keys for lookup
    keys = [k for k in aut.vars if not stx.isprimed(k)]
    umap = dict()
    for model in c:
        # model = model of relation = edge
        # source = model of set = node
        source = dict()
        target = dict()
        for var, value in model.items():
            if stx.isprimed(var):
                target[var] = value
            else:
                source[var] = value
        # map valuation to g node
        target = _unprime_any_primed(target)
        u = _find_or_add_model(source, umap, keys)
        v = _find_or_add_model(target, umap, keys)
        g.add_node(u, **source)
        g.add_node(v, **target)
        g.add_edge(u, v)
    return g


def print_nodes(
        u, dvars, bdd,
        care_set=None,
        care_bits=None):
    """Enumerate first-order models of a set.

    A set of nodes is defined over unprimed variables.

    @param dvars:
        table of unprimed variables
    @type bdd:
        `BDD`
    """
    assert scope.is_state_predicate(u), u.support
    if u == bdd.false:
        print('empty set')
        return
    if care_bits is not None:
        assert scope.support_issubset(u, care_bits, bdd), (
            support, care_bits)
    _print_enumeration(u, bdd, dvars, care_set, care_bits)


def print_edges(
        u, aut,
        care_set=None,
        care_bits=None):
    """Enumerate first-order models of a relation.

    A relation is defined over both primed and
    unprimed variables.

    @param `aut.vars`:
        table of unprimed variables
    @type `aut.bdd`:
        `BDD`
    """
    source = care_set
    target = care_set
    t, care_relation = _make_table(u, aut, source,
                                   target, care_bits)
    _print_enumeration(u, aut.bdd, t, care_relation,
                       care_bits)


def _print_enumeration(
        u, bdd, t,
        care_set,
        care_bits):
    """Print first-order models."""
    c = _enumerate_bdd(u, bdd, t, care_set, care_bits)
    r = list()
    keys = natsort.natsorted(t)
    for product in c:
        w = list()
        for x in keys:
            if x not in product:
                continue
            i = product[x]
            s = f'({x} = {i})'
            w.append(s)
        s = r' /\ '.join(w)
        r.append(s)
    e = '\n'.join(r)
    logger.debug(
        'enumeration of BDD node '
        f'{u} with care set {care_set}\n')
    print(f'contains {len(c)} expressions:\n\n{e}\n')


def _make_table(
        u, aut,
        care_source=None,
        care_target=None,
        care_bits=None):
    """Return symbol table with primed vars and care relation.

    The variables in `a.vars` should be unprimed.
    """
    bdd = aut.bdd
    care_relation = _care_relation(care_source, care_target, bdd)
    t = copy.deepcopy(aut.vars)
    if care_bits is not None:
        assert scope.support_issubset(u, care_bits, bdd), (
            support, care_bits)
    return t, care_relation


def _care_relation(source, target, bdd):
    """Return product `source` with primed `target`.

    @param source:
        care set for source nodes
    @param target:
        care set for target nodes
    @type source, target:
        BDD over unprimed variables
    """
    # Cartesian product of `care_set`
    if source is None or target is None:
        care_relation = None
        return care_relation
    primed_target = _prime_bits(target)
    care_relation = source & primed_target
    return care_relation


def _prime_bits(u):
    """Prime the bits in `u.support` that are not constants.

    This function is similar to the function
    `omega.symbolic.prime.prime`, with the difference that
    the latter works with variables of
    `omega.symbolic.fol.Context.vars`.

    @param u:
        `dd.autoref.Function` or
        `dd.cudd.Function`
    """
    support = u.support  # bits
    assert not any(stx.isprimed(name) for name in support), support
    # omit constants
    var_bits = {bit for bit in support if stx.prime(bit) in u.bdd.vars}
    let = {bit: stx.prime(bit) for bit in var_bits}
    return u.let(**let)


def _enumerate_bdd(
        u, bdd, t,
        care_set=None,
        care_bits=None):
    """Enumerate first-order models of BDD `u`.

    @param care_set:
        enumerate only models in this set
    @param care_bits:
        enumerate over at least these bits
    """
    if u == bdd.false:
        return
    if care_set is not None:
        u &= care_set
        logging.debug(
            f'enumerating BDD node {u}, '
            f'with care set = {care_set}')
    c = list()
    for dbit in bdd.pick_iter(u, care_bits):
        dint = _bitfields_to_int_iter(dbit, t)
        c.extend(dint)
    return c


def _bitfields_to_int_iter(bits, t):
    """Enumerate set of integers (and Booleans).

    @param bits:
        partial assignment that maps
        bits to values
    @type bits:
        `dict`
    @param t:
        symbol table (with bitnames)
    @type t:
        `dict`
    """
    # any bits missing ?
    t_bits = set()
    for flatname, d in t.items():
        dt = d['type']
        if dt == 'bool':
            t_bits.add(flatname)
        elif dt == 'int':
            t_bits.update(d['bitnames'])
        else:
            raise Exception(
                f'unknown type "{dt}"')
    missing = set(bits).difference(t_bits)
    assert not missing, (
        f'WARNING: missing bits:\n {missing}\n'
        f'from concrete table:\n {t}')
    # init
    bits = dict(bits)
    model = dict()
    # bool first
    for flatname, d in t.items():
        if d['type'] != 'bool':
            continue
        if flatname in bits:
            model[flatname] = bits.pop(flatname)
    # integers
    sets = dict()
    for flatname, d in t.items():
        if d['type'] == 'bool':
            continue
        bitnames = d['bitnames']
        # missing ?
        if not set(bitnames).intersection(bits):
            continue
        # partial bitvector valuation
        bitvalues = list(map(bits.get, bitnames))
        bv._append_sign_bit(bitvalues, flatname, d)
        values = _enumerate_int(bitvalues)
        sets[flatname] = list(values)
    return _take_product_iter(sets, model)


def _enumerate_int(bitvalues, j=0):
    """Enumerate from a partial bitvector assignment.

    @param bitvalues:
        partial assignment to bits
    @type bitvalues:
        `list` of `str` or `None`
    @param j:
        index of current bit
    """
    n = len(bitvalues)
    assert j < n, (j, n)
    b = bitvalues[j]
    # sign ?
    if j == n - 1:
        if b is None:
            yield -2**j
            yield 0
        else:
            b = int(b)
            yield -b * 2**j
        return
    assert j < n - 1, (j, n)
    for v in _enumerate_int(bitvalues, j + 1):
        if b is None:
            yield v
            yield v + 2**j
        else:
            b = int(b)
            yield v + 2**j * b


def _take_product_iter(sets, model):
    """Iterate over all combinations of values in `sets`.

    The resulting combinations of values are
    used to complete the `model`.

    @param sets:
        map from variables to
        sets of values
    @type sets:
        `dict` of `set`
    @param model:
        partial assignment to Boolean variables
    @type model:
        `dict`
    """
    if not sets:
        yield model
        return
    var, values = sets.popitem()
    for m in _take_product_iter(sets, model):
        for v in values:
            m = dict(m)
            m[var] = v
            yield m


def _unprime_any_primed(model):
    """Trim any primed variables."""
    d = dict(model)
    suffix = "'"
    for k in list(d.keys()):
        if k.endswith(suffix):
            s = k[:-1]
            d[s] = d.pop(k)
    return d


def _find_or_add_model(model, umap, keys):
    """Return integer node for given valuation.

    If absent, then a fresh node is created.

    @type model:
        `dict`
    @type umap:
        `dict`
    """
    u = tuple(model[k] for k in keys)
    u = umap.setdefault(u, len(umap))
    return u


def _dump_graph_as_figure(g, fname):
    """Create a PDF file showing the graph `g`."""
    h, _ = _format_nx(g)
    pd = nx.drawing.nx_pydot.to_pydot(h)
    pd.write_pdf(fname)


def _format_nx(g, keys=None):
    """Return graph ready to be dumped.

    Nodes with same label over `keys` are identified.
    Edge attributes are copied.

    @type g:
        `networkx.DiGraph`
    @param keys:
        `list` of keys in node attributes `dict` to
        show as label, in the given order.
        Attributes outside `keys` remain attributes.
        By default all keys are shown.
    @rtype:
        `pydot.Graph`
    """
    h = nx.DiGraph()
    umap = dict()
    for u, d in g.nodes(data=True):
        if keys is None:
            keys = sorted(d)
        c = [f'{var}={d[var]}'
             for var in keys if var in d]
        s = _square_conj(c)
        attr = {k: v for k, v in d.items() if k not in keys}
        h.add_node(s, **attr)
        umap[u] = s
    for u, v, attr in g.edges(data=True):
        us = umap[u]
        vs = umap[v]
        h.add_edge(us, vs, **attr)
    assert len(g) >= len(h), (g.nodes, h.nodes)
    assert len(g) == len(umap), (g.nodes, umap)
    return h, umap


def _square_conj(p, n=None, op=r'&and;'):
    """Return conjunction arranged vertically.

    The number of conjuncts per line is
    picked to make the result more balanced,
    closer to a square.
    The formatting characters are for `dot`.

    @param p:
        iterable of conjuncts
    @param n:
        number of items in `p`
        (useful when `p` is a generator)
    """
    if n is None:
        n = len(p)
    assert n > 0, n
    m = math.ceil(n**0.5)
    c = list()
    for i, s in enumerate(natsort.natsorted(p)):
        c.append(op)
        s = f' ({s}) '
        c.append(s)
        if (i + 1) % m == 0:
            c.append(r'\l')
    # single line ?
    if n <= 2:
        c.pop(0)
    return ''.join(c)
