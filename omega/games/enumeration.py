"""Convert relation predicate to predicate-action diagram.

Reference
=========

Leslie Lamport
    "TLA in pictures"
    IEEE Transactions on Software Engineering
    Vol.21, No.9, pp.768--775, 1995
    doi: 10.1109/32.464544
"""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import collections
import logging

import networkx as nx

from omega.logic import syntax as stx
from omega.symbolic import fol as _fol
from omega.symbolic import symbolic


log = logging.getLogger(__name__)


def action_to_steps(aut, qinit='\A \A'):
    r"""Return enumerated graph with steps as edges.

    Only `aut.init['env']` considered.
    The predicate `aut.init['sys']` is ignored.

    `qinit` has different meaning that in `omega.games.gr1`.
    Nonetheless, for synthesized `aut.init['env']`,
    the meaning of `qinit` here yields the expected result.

    Enumeration is done based on `qinit`:

    - `'\A \A'`: pick all states that satisfy `aut.init['env']`
    - `'\E \E'`: pick one state that satisfies `aut.init['env']`
    - `'\A \E'`: for all states that satisfy `aut.init['env']`,
      pick a unique state for each env state `x`
    - `'\E \A'`: pick a sys state `u` and enumerate all
      states that satisfy `aut.init['env']` and `y = u`
    """
    assert 'env' in aut.players, aut.players
    assert 'sys' in aut.players, aut.players
    assert aut.action['sys'] != aut.false
    fol.vars = symbolic._prime_and_order_table(aut.vars)
    control, primed_vars = _split_vars_per_quantifier(
        aut.vars, aut.players)
    aut.control = control
    # prime_vars = {var: stx.prime(var) for var in aut.vars}
    unprime_vars = {stx.prime(var): var for var in aut.vars}
    keys = list(aut.vars)  # fix an order for tupling
    umap = dict()  # map assignments -> node numbers
    g = nx.DiGraph()
    queue, visited = _init_search(g, aut, umap, keys, qinit)
    varnames = set(aut.vars)
    symbolic._assert_support_moore(aut)
    # search
    while queue:
        node = queue.pop()
        values = g.node[node]
        log.debug('at node: {d}'.format(d=values))
        assert set(values) == varnames, (values, aut.vars)
        u = aut.action['env']
        u = aut.let(values, u)
        # apply Mealy controller function
        env_iter = aut.pick_iter(
            u, care_vars=primed_vars['env'])
        u = aut.action['sys']
        assert u != aut.false
        sys = aut.let(values, u)
        for next_env in env_iter:
            log.debug('next_env: {r}'.format(r=next_env))
            # no effect if `aut.moore`
            u = aut.let(next_env, sys)
            u = aut.let(unprime_vars, u)
            env_values = {unprime_vars[var]: value
                          for var, value in next_env.items()}
            v = aut.let(env_values, visited)
            # prefer already visited nodes
            v &= u
            if v == aut.false:
                log.info('cannot remain in visited nodes')
                v = u
                remain = False
            else:
                remain = True
            assert v != aut.false
            sys_values = aut.pick(
                v, care_vars=aut.control['sys'])
            d = dict(env_values)
            d.update(sys_values)
            # assert
            u = aut.let(d, visited)
            assert u == aut.true or u == aut.false
            assert remain == (u == aut.true), remain
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


def _split_vars_per_quantifier(dvars, players):
    """Return controllability `dict` and primed vars `dict`."""
    control = {owner: set() for owner in players}
    primed_vars = {owner: set() for owner in players}
    for var, d in dvars.items():
        pvar = stx.prime(var)
        owner = d['owner']
        assert owner in players, (owner, players)
        control[owner].add(var)
        primed_vars[owner].add(pvar)
    return control, primed_vars


def _init_search(g, aut, umap, keys, qinit):
    """Enumerate initial states according to `qinit`."""
    # danger of blowup due to sparsity
    # implement enumerated equivalent to compare
    if qinit == '\A \E':
        queue, visited = _forall_exist_init(g, aut, umap, keys)
    elif qinit == '\A \A':
        queue, visited = _forall_init(g, aut, umap, keys)
    elif qinit == '\E \E':
        queue, visited = _exist_init(g, aut, umap, keys)
    elif qinit == '\E \A':
        queue, visited = _exist_forall_init(g, aut, umap, keys)
    else:
        raise Exception('unknown qinit "{q}"'.format(q=qinit))
    log.info('{n} initial nodes'.format(n=len(queue)))
    return queue, visited


def _forall_init(g, aut, umap, keys):
    r"""Enumerate initial states with \A \A vars."""
    env_init = aut.init['env']
    assert env_init != aut.false
    init_iter = aut.pick_iter(
        env_init, care_vars=aut.vars)
    visited = aut.false
    queue = list()
    for d in init_iter:
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _exist_init(g, aut, umap, keys):
    r"""Enumerate initial states with \E env, sys vars."""
    env_init = aut.init['env']
    assert env_init != aut.false
    d = aut.pick(env_init, care_vars=aut.vars)
    visited = aut.false
    queue = list()
    _add_new_node(d, g, queue, umap, keys)
    visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _forall_exist_init(g, aut, umap, keys):
    r"""Enumerate initial states with \A env: \E sys vars.

    Note that each initial "state" is a class of
    initial states in ZF set theory.
    """
    env_init = aut.init['env']
    assert env_init != aut.false
    only_env_init = aut.exist(aut.control['sys'], env_init)
    env_iter = aut.pick_iter(
        only_env_init, care_vars=aut.control['env'])
    visited = aut.false
    queue = list()
    for env_0 in env_iter:
        u = aut.let(env_0, env_init)
        sys_0 = aut.pick(u, care_vars=aut.control['sys'])
        d = dict(env_0)
        d.update(sys_0)
        # confirm `sys_0` picked properly
        u = aut.let(d, env_init)
        assert u == aut.true, u
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _exist_forall_init(g, aut, umap, keys):
    r"""Enumerate initial states with \E sys: \A env vars."""
    # this function can be merged with `_forall_exist_init`
    # by constraining initial sys assignments,
    # then enumerating the same way
    env_init = aut.init['env']
    assert env_init != aut.false
    # pick `sys_0` so that it work for all
    # env assignments alowed by `env_init`
    only_env_init = aut.exist(aut.control['sys'], env_init)
    u = ~ only_env_init | env_init
    u = aut.forall(aut.control['env'], u)
    assert u != aut.false
    sys_0 = aut.pick(u, care_vars=aut.control['sys'])
    # iterate over env initial assignments
    # independently of sys
    env_iter = aut.pick_iter(
        only_env_init, care_vars=aut.control['env'])
    visited = aut.false
    queue = list()
    for env_0 in env_iter:
        d = dict(env_0)
        d.update(sys_0)
        # confirm `sys_0` works for all `env_0`
        u = aut.let(d, env_init)
        assert u == aut.true, u
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _find_node(d, umap, keys):
    """Return node in `umap` with assignment `d`."""
    assert isinstance(keys, collections.Sequence), keys
    key = _node_tuple(d, keys)
    assert key in umap, (key, umap)
    u = umap[key]
    return u


def _add_new_node(d, g, queue, umap, keys):
    """Add node to graph `g` for the assignment `d`."""
    assert isinstance(keys, collections.Sequence), keys
    u = len(g)
    assert u not in g, u
    g.add_node(u, **d)
    key = _node_tuple(d, keys)
    assert key not in umap, (key, umap)
    umap[key] = u
    queue.append(u)
    log.debug(d)
    return u


def _add_to_visited(values, visited, aut):
    """Return BDD `visted` updated with assignment `values`."""
    c = list()
    for var, value in values.items():
        t = aut.vars[var]['type']
        if t == 'bool':
            assert value in (True, False), value
            if bool(value):
                c.append(var)
            else:
                c.append('! ' + var)
            continue
        # integer
        assert t in ('int', 'saturating', 'modwrap'), t
        s = '{var} = {value}'.format(var=var, value=value)
        c.append(s)
    s = stx.conj(c)
    u = aut.add_expr(s)
    visited |= u
    return visited


def _node_tuple(d, keys):
    """Return `tuple` of `d` values ordered by `keys`.

    @type d: `dict`
    @type keys: `tuple`
    """
    return tuple(d[k] for k in keys)
