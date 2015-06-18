"""Enumerate symbolically represented sets and relations.

Integers are decoded from binary to decimal.
"""
import logging
from dd import bdd as _bdd
import networkx as nx
from omega.logic.syntax import linear_conj as conj
from omega.symbolic import symbolic


logger = logging.getLogger(__name__)


def dump_relation(
        u, aut, care_source=None,
        care_target=None, fname=None):
    """Dump graph of relation as PDF."""
    if fname is None:
        fname = 'edges.pdf'
    g = relation_to_graph(u, aut, care_source, care_target)
    pd = _nx_to_pydot(g)
    pd.write_pdf(fname, prog='dot')


def relation_to_graph(
        u, aut, care_source=None,
        care_target=None, care_bits=None):
    """Return enumerated graph from relation.

    @param u: relation as BDD node
    @param care_source: care set for source nodes
    @param care_target: care set for target nodes
    @type u, care_source, care_target: node in `aut.bdd`
    @rtype: `networkx.DiGraph`
    """
    t, care_relation = _make_table(u, aut, care_source,
                                   care_target, care_bits)
    c = _enumerate_bdd(u, aut.bdd, t, care_relation, care_bits, full=True)
    # to nx graph
    level_to_var = {d['level']: var for var, d in t.iteritems()}
    sorted_vars = [level_to_var[i] for i in xrange(len(level_to_var))]
    g = nx.DiGraph()
    g.sorted_vars = sorted_vars
    umap = dict()
    for model in c:
        # model = model of relation = edge
        # source = model of set = node
        source = dict()
        target = dict()
        for var, value in model.iteritems():
            if var in aut.vars:
                source[var] = value
            else:
                target[var] = value
        # map valuation to g node
        target = _unprime(target)
        u = _find_or_add_model(source, umap)
        v = _find_or_add_model(target, umap)
        g.add_node(u, **source)
        g.add_node(v, **target)
        g.add_edge(u, v)
    return g


def print_nodes(
        u, dvars, bdd, care_set=None,
        care_bits=None, full=False):
    """Enumerate first-order models of a set.

    A set of nodes is defined over unprimed variables.

    @param dvars: table of unprimed variables
    @type bdd: `BDD`
    """
    if u == -1:
        print('empty set')
        return
    t = symbolic._prime_and_order_table(dvars)
    if care_bits is not None:
        support = bdd.support(u)
        assert support.issubset(care_bits), (support, care_bits)
    _print_enumeration(u, bdd, t, care_set, care_bits, full)


def print_edges(
        u, aut, care_set=None,
        care_bits=None, full=False):
    """Enumerate first-order models of a relation.

    A relation is defined over both primed and
    unprimed variables.

    @param `aut.vars`: table of unprimed variables
    @type `aut.bdd`: `BDD`
    """
    source = care_set
    target = care_set
    t, care_relation = _make_table(u, aut, source,
                                   target, care_bits)
    _print_enumeration(u, aut.bdd, t, care_relation, care_bits, full)


def _print_enumeration(u, bdd, t, care_set, care_bits, full):
    """Print first-order models."""
    c = _enumerate_bdd(u, bdd, t, care_set, care_bits, full)
    r = list()
    for product in c:
        w = list()
        for x, i in product.iteritems():
            s = '({x} = {i})'.format(x=x, i=i)
            w.append(s)
        s = ' & '.join(w)
        r.append(s)
    e = '\n'.join(r)
    logger.debug(
        'enumeration of BDD node {u} with care set {c}\n'.format(
            u=u, c=care_set))
    s = (
        'contains {n} elements:\n\n{e}\n').format(
            e=e,
            n=len(c))
    print(s)


def _make_table(
        u, a, care_source=None,
        care_target=None, care_bits=None):
    """Return `dict` models.

    The variables in `a.vars` should be unprimed.
    """
    bdd = a.bdd
    care_relation = _care_relation(care_source, care_target,
                                   a.prime, bdd)
    t = symbolic._prime_and_order_table(a.vars)
    if care_bits is not None:
        # check `care_vars`
        support = bdd.support(u)
        assert support.issubset(care_bits), (support, care_bits)
    return t, care_relation


def _care_relation(source, target, prime, bdd):
    """Return product `source` with primed `target`.

    @param source: care set for source nodes
    @param target: care set for target nodes
    @type source, target: BDD over unprimed variables
    """
    # Cartesian product of `care_set`
    if source is None or target is None:
        care_relation = None
        return care_relation
    primed_target = _bdd.rename(target, bdd, prime)
    care_relation = bdd.apply('and', source, primed_target)
    return care_relation


def _enumerate_bdd(
        u, bdd, t, care_set=None,
        care_bits=None, full=False):
    """Enumerate first-order models of BDD `u`.

    @param care_set: enumerate only models in this set
    @param care_bits: enumerate only over these bits
    @param full: if `True`, return minterms, else cubes
    """
    if u == bdd.add_expr('False'):
        return
    if care_set is not None:
        u = bdd.apply('and', u, care_set)
        logging.debug(
            'enumerating BDD node {u}, with care set = {c}'.format(
                u=u, c=care_set))
    c = list()
    for dbit in bdd.sat_iter(u, full, care_bits):
        dint = _bitfields_to_int_iter(dbit, t)
        c.extend(dint)
    return c


def _bitfields_to_int_iter(bits, t):
    """Enumerate set of integers (and Booleans).

    @param bits: partial assignment that maps bits to values
    @type bits: `dict`
    @param t: symbol table (with bitnames)
    @type t: `dict`
    """
    # any bits missing ?
    t_bits = set()
    for flatname, d in t.iteritems():
        dt = d['type']
        if dt == 'bool':
            t_bits.add(flatname)
        elif dt == 'int':
            t_bits.update(d['bitnames'])
        else:
            raise Exception('unknown type "{dt}"'.format(dt=dt))
    missing = set(bits).difference(t_bits)
    if missing:
        print(('WARNING (synthesizer):'
               ' missing bits:\n{b}').format(b=missing))
    # init
    bits = dict(bits)
    model = dict()
    # bool first
    for flatname, d in t.iteritems():
        if d['type'] == 'bool':
            if flatname in bits:
                model[flatname] = bits.pop(flatname)
    # integers
    sets = dict()
    for flatname, d in t.iteritems():
        if d['type'] == 'bool':
            continue
        # missing ?
        if not set(d['bitnames']).intersection(bits):
            continue
        # partial bitvector valuation
        bitvalues = map(bits.get, d['bitnames'])
        if not d['signed']:
            # TODO: update this
            bitvalues += ['0']
        values = _enumerate_int(bitvalues)
        sets[flatname] = list(values)
    return _take_product_iter(sets, model)


def _enumerate_int(bitvalues, j=0):
    """Enumerate from a partial bitvector assignment.

    @param bitvalues: partial assignment to bits
    @type bitvalues: `list` of `str` or `None`
    @param j: index of current bit
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

    @param sets: map from variables to sets of values
    @type sets: `dict` of `set`
    @param model: partial assignment to Boolean variables
    @type model: `dict`
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


def _unprime(model):
    """Trim primed variables."""
    d = dict(model)
    suffix = "'"
    for k in d:
        if k.endswith(suffix):
            s = k[:-1]
            d[s] = d.pop(k)
    return d


def _find_or_add_model(model, umap):
    """Return integer node for given valuation.

    If absent, then a fresh node is created.

    @type model: `dict`
    @type umap: `dict`
    """
    u = tuple(model.iteritems())
    u = umap.setdefault(u, len(umap))
    return u


def _care_bits(u, aut):
    """Return unprimed bits together with support of `u`.

    @type u: node in `aut.bdd`
    @type aut: `symbolic.Automaton`
    """
    bdd = aut.bdd
    care_bits = set(map(bdd.level_to_variable, aut.ubvars))
    support = bdd.support(u)
    care_bits.update(support)
    return care_bits


def _nx_to_pydot(g):
    """Return graph ready to be dumped.

    @type g: `networkx.DiGraph`
    @rtype: `pydot.Graph`
    """
    h = nx.DiGraph()
    umap = dict()
    for u, d in g.nodes_iter(data=True):
        gen = ('{var}={val}'.format(var=var, val=d[var])
               for var in g.sorted_vars if var in d)
        s = conj(gen, op='&')
        h.add_node(s)
        umap[u] = s
    for u, v in g.edges_iter():
        us = umap[u]
        vs = umap[v]
        h.add_edge(us, vs)
    pd = nx.to_pydot(h)
    return pd
