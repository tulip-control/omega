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
try:
    from collections.abc import Sequence
except ImportError:
    from collections import Sequence
import copy
from itertools import chain
import logging

import networkx as nx

from omega.logic import syntax as stx
from omega.symbolic import prime as prm
from omega.symbolic import symbolic


log = logging.getLogger(__name__)


def action_to_steps(aut, env, sys, qinit='\A \A'):
    r"""Return enumerated graph with steps as edges.

    Only `aut.init['env']` considered.
    The predicate `aut.init['sys']` is ignored.

    `qinit` has different meaning that in `omega.games.gr1`.
    Nonetheless, for synthesized `aut.init['env']`,
    the meaning of `qinit` here yields the expected result.

    Enumeration is done based on `qinit`:

    - `'\A \A'`: pick all states that satisfy `aut.init[env] /\ aut.init[sys]`,
      where the conjunct `aut.init[sys]` is included for the internal variables

    - `'\E \E'`: pick one state that satisfies `aut.init[sys]`

    - `'\A \E'`: for each environment state `x` that satisfies
      `\E y:  aut.init[env]`,
      pick a system state `y` that satisfies `aut.init[sys]`

    - `'\E \A'`: pick a system state `y` that satisfies
      `\A x:  aut.init[sys]`,
      and enumerate all environment states `x` that satisfy `aut.init['env']`.
    """
    _aut = copy.copy(aut)
    _aut.moore = aut.moore
    _aut.varlist.update(
        env=aut.varlist[env],
        sys=aut.varlist[sys])
    _aut.init.update(
        env=aut.init[env],
        sys=aut.init[sys])
    _aut.action.update(
        env=aut.action[env],
        sys=aut.action[sys])
    _aut.prime_varlists()
    return _action_to_steps(_aut, qinit)


def enumerate_state_machine(init, action, aut):
    """Return graph of `action` steps enumerated from `init`.

    @rtype: `networkx.DiGraph`
    """
    assert init != aut.false
    assert action != aut.false
    vrs = (
        prm.vars_in_support(init, aut) |
        prm.vars_in_support(action, aut))
    g = nx.DiGraph()
    keys = list(vrs)
    umap = dict()
    init_iter = aut.pick_iter(init, vrs)
    visited = aut.false
    queue = list()
    for d in init_iter:
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    while queue:
        node = queue.pop()
        values = g.nodes[node]
        u = aut.let(values, action)
        u = prm.unprime(u, aut)
        for d in aut.pick_iter(u, vrs):
            if aut.let(d, visited) != aut.true:
                next_node = _add_new_node(d, g, queue, umap, keys)
                visited = _add_to_visited(d, visited, aut)
            next_node = _find_node(d, umap, keys)
            g.add_edge(node, next_node)
    return g


def _action_to_steps(aut, qinit):
    assert aut.action['sys'] != aut.false
    primed_vars = _primed_vars_per_quantifier(aut.varlist)
    vrs = set(aut.varlist['env']).union(aut.varlist['sys'])
    unprime_vars = {stx.prime(var): var for var in vrs}
    # fix an order for tupling
    keys = list(vrs)
    umap = dict()  # map assignments -> node numbers
    g = nx.DiGraph()
    queue, visited = _init_search(g, aut, umap, keys, qinit)
    g.initial_nodes = set(queue)
    varnames = set(keys)
    symbolic._assert_support_moore(aut.action['sys'], aut)
    # search
    while queue:
        node = queue.pop()
        values = g.nodes[node]
        log.debug('at node: {d}'.format(d=values))
        assert set(values) == varnames, (values, varnames)
        u = aut.action['env']
        u = aut.let(values, u)
        # apply Mealy controller function
        env_iter = aut.pick_iter(
            u, care_vars=primed_vars['env'])
        u = aut.action['sys']
        assert u != aut.false
        sys = aut.let(values, u)
        assert sys != aut.false
        for next_env in env_iter:
            log.debug('next_env: {r}'.format(r=next_env))
            # no effect if `aut.moore`
            u = aut.let(next_env, sys)
            u = aut.let(unprime_vars, u)
            env_values = {unprime_vars[var]: value
                          for var, value in next_env.items()}
            v = aut.let(env_values, visited)
            v, remain = _select_candidate_nodes(
                u, v, aut, visited=True)
            sys_values = aut.pick(
                v, care_vars=aut.varlist['sys'])
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


def _select_candidate_nodes(
        next_nodes, visited_nodes, aut, visited=True):
    """Return set of next nodes to choose from, as BDD."""
    u = next_nodes
    v = visited_nodes
    # prefer already visited nodes ?
    if visited:
        v &= u
        if v == aut.false:
            log.info('cannot remain in visited nodes')
            v = u
            remain = False
        else:
            remain = True
    else:
        v = u & ~ v
        if v == aut.false:
            log.info('cannot visit new nodes')
            v = u
            remain = True
        else:
            remain = False
    assert v != aut.false
    return v, remain


def _primed_vars_per_quantifier(varlist):
    """Return `dict` that maps each player to set of primed vars.

    @return: `dict` that maps
          player name -> set of primed vars
    """
    assert 'env' in varlist, varlist
    assert 'sys' in varlist, varlist
    primed_vars = dict(
        env={stx.prime(var) for var in varlist['env']},
        sys={stx.prime(var) for var in varlist['sys']})
    return primed_vars


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
    sys_init = aut.init['sys']  # to constrain only the
        # initial value of the internal memory variables
    assert env_init != aut.false
    care_vars = chain(aut.varlist['env'], aut.varlist['sys'])
    init_iter = aut.pick_iter(
        env_init & sys_init,
        care_vars=list(care_vars))
    visited = aut.false
    queue = list()
    for d in init_iter:
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _exist_init(g, aut, umap, keys):
    r"""Enumerate initial states with \E env, sys vars."""
    sys_init = aut.init['sys']
    assert sys_init != aut.false
    care_vars = chain(aut.varlist['env'], aut.varlist['sys'])
    d = aut.pick(
        sys_init,
        care_vars=list(care_vars))
    visited = aut.false
    queue = list()
    _add_new_node(d, g, queue, umap, keys)
    visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _forall_exist_init(g, aut, umap, keys):
    r"""Enumerate initial states with \A env:  \E sys vars.

    Note that each initial "state" is a class of
    initial states in ZF set theory.
    """
    env_init = aut.init['env']
    sys_init = aut.init['sys']
    assert env_init != aut.false
    assert sys_init != aut.false
    # `env_init` should not depend on sys vars
    only_env_init = aut.exist(aut.varlist['sys'], env_init)
    env_iter = aut.pick_iter(
        only_env_init, care_vars=aut.varlist['env'])
    visited = aut.false
    queue = list()
    for env_0 in env_iter:
        u = aut.let(env_0, sys_init)
        sys_0 = aut.pick(u, care_vars=aut.varlist['sys'])
        d = dict(env_0)
        d.update(sys_0)
        # confirm `sys_0` picked properly
        u = aut.let(d, env_init)
        assert u == aut.true, u
        _add_new_node(d, g, queue, umap, keys)
        visited = _add_to_visited(d, visited, aut)
    return queue, visited


def _exist_forall_init(g, aut, umap, keys):
    r"""Enumerate initial states with \E sys:  \A env vars."""
    # this function can be merged with `_forall_exist_init`
    # by constraining initial sys assignments,
    # then enumerating the same way
    env_init = aut.init['env']
    sys_init = aut.init['sys']
    assert env_init != aut.false
    assert sys_init != aut.false
    # pick `sys_0` so that it work for all
    # env assignments allowed by `env_init`
    u = aut.forall(aut.varlist['env'], sys_init)
    assert u != aut.false
    sys_0 = aut.pick(u, care_vars=aut.varlist['sys'])
    # iterate over env initial assignments
    # allow `EnvInit` that depends on sys vars (Mealy env)
    env_iter = aut.pick_iter(
        env_init, care_vars=aut.varlist['env'])
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
    assert isinstance(keys, Sequence), keys
    key = _node_tuple(d, keys)
    assert key in umap, (key, umap)
    u = umap[key]
    return u


def _add_new_node(d, g, queue, umap, keys):
    """Add node to graph `g` for the assignment `d`."""
    assert isinstance(keys, Sequence), keys
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
    """Return BDD `visited` updated with assignment `values`."""
    c = list()
    for var, value in values.items():
        t = aut.vars[var]['type']
        if t == 'bool':
            assert value in (True, False), value
            if bool(value):
                c.append(var)
            else:
                c.append(' ~ ' + var)
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
