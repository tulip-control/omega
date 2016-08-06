"""Convert relation predicate to predicate-action diagram.

Reference
=========

Leslie Lamport
    "TLA in pictures"
    IEEE Transactions on Software Engineering
    Vol.21, No.9, pp.768--775, 1995
    doi: 10.1109/32.464544
"""
import logging

import networkx as nx

from omega.logic import syntax as stx
from omega.symbolic import fol as _fol
from omega.symbolic import symbolic


log = logging.getLogger(__name__)


def action_to_steps(aut, qinit=None):
    r"""Return enumerated graph with steps as edges.

    @param qinit:
        '\A \A' == forall env values: forall sys values
        '\A \E' == forall env values: exist sys values
        '\E \A' == exist sys values: forall env values
    """
    if qinit is None:
        qinit = '\A \A'
    bdd = aut.bdd
    assert aut.action['sys'][0] != bdd.false
    fol = _fol.Context()
    fol.bdd = bdd
    fol.vars = symbolic._prime_and_order_table(aut.vars)
    # fol.add_vars(table)
    aut.control = dict(env=set(), sys=set())
    aut.primed_vars = dict(env=set(), sys=set())
    for var, d in aut.vars.iteritems():
        pvar = stx.prime(var)
        owner = d['owner']
        assert owner in aut.players, owner
        aut.control[owner].add(var)
        aut.primed_vars[owner].add(pvar)
    # prime_vars = {var: stx.prime(var) for var in aut.vars}
    unprime_vars = {stx.prime(var): var for var in aut.vars}
    keys = list(aut.vars)  # fix an order for tupling
    umap = dict()  # map assignments -> node numbers
    g = nx.DiGraph()
    g.sorted_vars = keys
    # danger of blowup due to sparsity
    # implement enumerated equivalent to compare
    if qinit == '\A \E':
        queue, visited = _forall_exist_init(g, fol, aut, umap, keys)
    elif qinit == '\A \A':
        queue, visited = _forall_init(g, fol, aut, umap, keys)
    elif qinit == '\E \E':
        queue, visited = _exist_init(g, fol, aut, umap, keys)
    elif qinit == '\E \A':
        queue, visited = _exist_forall_init(g, fol, aut, umap, keys)
    else:
        raise Exception('unknown qinit "{q}"'.format(q=qinit))
    log.info('{n} initial nodes'.format(n=len(queue)))
    # search
    while queue:
        node = queue.pop()
        values = g.node[node]
        log.debug('at node: {d}'.format(d=values))
        assert set(values) == set(aut.vars), (values, aut.vars)
        (u,) = aut.action['env']
        u = fol.replace(u, values)
        # apply Mealy controller function
        env_iter = fol.sat_iter(
            u, full=True, care_vars=aut.primed_vars['env'])
        (u,) = aut.action['sys']
        sys = fol.replace(u, values)
        for next_env in env_iter:
            log.debug('next_env: {r}'.format(r=next_env))
            u = fol.replace(sys, next_env)
            u = fol.replace(u, unprime_vars)
            env_values = {unprime_vars[var]: value
                          for var, value in next_env.iteritems()}
            v = fol.replace(visited, env_values)
            # prefer already visited nodes
            v = bdd.apply('and', u, v)
            if v == bdd.false:
                log.info('cannot remain in visited nodes')
                v = u
                remain = False
            else:
                remain = True
            assert v != bdd.false
            sys_values = fol.pick(
                v, full=True, care_vars=aut.control['sys'])
            d = dict(env_values)
            d.update(sys_values)
            # assert
            u = fol.replace(visited, d)
            assert u == bdd.true or u == bdd.false
            assert remain == (u == bdd.true), remain
            # find or add node
            if remain:
                next_node = _find_node(d, umap, keys)
            else:
                next_node = _add_new_node(d, g, queue, umap, keys)
                visited = _add_to_visited(d, visited, aut)
            g.add_edge(node, next_node)
            log.debug((
                'next env: {e}\n'
                'next sys: {s}\n').format(
                    e=env_values,
                    s=sys_values))
    return g


def _forall_init(g, fol, aut, umap, keys):
    r"""Enumerate initial states with \A \A vars."""
    aut.assert_consistent(built=True)
    assert fol.bdd is aut.bdd
    bdd = fol.bdd
    (env_init,) = aut.init['env']
    assert env_init != bdd.false
    init_iter = fol.sat_iter(
        env_init, full=True,
        care_vars=aut.vars)
    visited = bdd.false
    queue = list()
    for d in init_iter:
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _exist_init(g, fol, aut, umap, keys):
    r"""Enumerate initial states with \E env, sys vars."""
    aut.assert_consistent(built=True)
    assert fol.bdd is aut.bdd
    bdd = fol.bdd
    (env_init,) = aut.init['env']
    assert env_init != bdd.false
    d = fol.pick(env_init, full=True, care_vars=aut.vars)
    visited = bdd.false
    queue = list()
    _add_new_node(d, g, queue, umap, keys)
    visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _forall_exist_init(g, fol, aut, umap, keys):
    r"""Enumerate initial states with \A env: \E sys vars.

    Note that each initial "state" is a class of
    initial states in ZF set theory.
    """
    aut.assert_consistent(built=True)
    assert fol.bdd is aut.bdd
    bdd = fol.bdd
    (env_init,) = aut.init['env']
    assert env_init != bdd.false
    only_env_init = fol.exist(aut.control['sys'], env_init)
    env_iter = fol.sat_iter(
        only_env_init, full=True, care_vars=aut.control['env'])
    visited = bdd.false
    queue = list()
    for env_0 in env_iter:
        u = fol.replace(env_init, env_0)
        sys_0 = fol.pick(u, full=True,
                         care_vars=aut.control['sys'])
        d = dict(env_0)
        d.update(sys_0)
        # confirm `sys_0` picked properly
        u = fol.replace(env_init, d)
        assert u == bdd.true, u
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _exist_forall_init(g, fol, aut, umap, keys):
    r"""Enumerate initial states with \E sys: \A env vars."""
    # this function can be merged with `_forall_exist_init`
    # by constraining initial sys assignments,
    # then enumerating the same way
    aut.assert_consistent(built=True)
    assert fol.bdd is aut.bdd
    bdd = fol.bdd
    (env_init,) = aut.init['env']
    assert env_init != bdd.false
    # pick `sys_0` so that it work for all
    # env assignments alowed by `env_init`
    only_env_init = fol.exist(aut.control['sys'], env_init)
    u = fol.apply('->', only_env_init, env_init)
    u = fol.forall(aut.control['env'], u)
    assert u != bdd.false
    sys_0 = fol.pick(u, full=True, care_vars=aut.control['sys'])
    # iterate over env initial assignments
    # independently of sys
    env_iter = fol.sat_iter(
        only_env_init, full=True, care_vars=aut.control['env'])
    visited = bdd.false
    queue = list()
    for env_0 in env_iter:
        d = dict(env_0)
        d.update(sys_0)
        # confirm `sys_0` works for all `env_0`
        u = fol.replace(env_init, d)
        assert u == bdd.true, u
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _find_node(d, umap, keys):
    """Return node in `umap` with assignment `d`."""
    key = tuple(d[k] for k in keys)
    assert key in umap, (key, umap)
    u = umap[key]
    return u


def _add_new_node(d, g, queue, umap, keys):
    """Add node to graph `g` for the assignment `d`."""
    u = len(g)
    assert u not in g, u
    g.add_node(u, **d)
    key = tuple(d[k] for k in keys)
    assert key not in umap, (key, umap)
    umap[key] = u
    queue.append(u)
    log.debug(d)
    return u


def _add_to_visited(values, visited, aut):
    """Return BDD `visted` updated with assignment `values`."""
    bdd = aut.bdd
    c = list()
    for var, value in values.iteritems():
        if aut.vars[var]['type'] == 'bool':
            assert value in (True, False), value
            if bool(value):
                c.append(var)
            else:
                c.append('! ' + var)
            continue
        # integer
        s = '{var} = {value}'.format(var=var, value=value)
        c.append(s)
    s = stx.conj(c)
    u = aut.add_expr(s)
    visited = bdd.apply('or', visited, u)
    return visited
