"""Conversion of semi-symbolic to symbolic automata.

Re-implementation of `tulip.synth`.
"""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from __future__ import absolute_import
import logging
import warnings

from omega.logic import syntax as stx
from omega.symbolic.symbolic import Automaton


logger = logging.getLogger(__name__)


def graph_to_logic(g, nodevar, ignore_initial,
                   receptive=False, self_loops=False):
    """Flatten labeled graph to temporal logic formulae.

    @param g: `TransitionSystem`

    The attribute `g.owner` defines who selects the next node.
    The attribute `g.env_vars` determines who controls each variable.

    @param g: `TransitionSystem`
    @param nodevar: variable that stores current node
    @type nodevar: `str`
    @param ignore_initial: if `False`, then add initial condition
        using `g.initia_nodes`.
    @type ignore_initial: `bool`
    @param receptive: if `True`, then add assumptions to
        ensure receptiveness at each node.
    @param self_loops: if `True`, then add all self-loops

    @return: temporal formulae representing `g`.
    @rtype: `Automaton`
    """
    assert g.assert_consistent()
    assert len(g) > 0
    t = _vars_to_symbol_table(g, nodevar)
    # add primed copies -- same `dict` value
    dvars = dict(t)
    p, _ = _prime_dict(dvars)
    dvars.update(p)
    # convert to logic
    init = _init_from_ts(g.initial_nodes, nodevar,
                         dvars, ignore_initial)
    tmp_init, nodepred = _node_var_trans(g, nodevar, dvars)
    sys_tran = list()
    env_tran = list()
    if g.owner == 'sys':
        sys_init = init + tmp_init
        r = _sys_trans(g, nodevar, dvars)
        if self_loops:
            r = "({r}) \/ ({var}' = {var})".format(
                r=r, var=nodevar)
        sys_tran.append(r)
        sys_tran.extend(nodepred)
        env_init = list()
        if receptive:
            r = _env_trans_from_sys_ts(g, nodevar, dvars)
            env_tran.append(r)
    elif g.owner == 'env':
        sys_init = list()
        env_init = init + tmp_init
        r = _env_trans(g, nodevar, dvars, self_loops)
        if self_loops:
            r = "({r}) \/ ({var}' = {var})".format(
                r=r, var=nodevar)
        env_tran.append(r)
        env_tran.extend(nodepred)
    else:
        raise Exception('owner is neither "sys" nor "env".')
    a = Automaton()
    a.vars = t
    a.init['env'].extend(env_init)
    a.init['sys'].extend(sys_init)
    a.action['env'].extend(env_tran)
    a.action['sys'].extend(sys_tran)
    return a


def _vars_to_symbol_table(g, nodevar):
    """Return `dict` of integer and Boolean variables.

    Conforms to `openpromela.bitvector` input:
      - type: 'bool' or 'saturating'
      - dom: (min, max)
      - owner: 'env' or 'sys'
    """
    t = dict()
    for var, dom in g.vars.items():
        # type and domain
        if dom == 'bool':
            dtype = 'bool'
            dom = None
        elif dom == 'boolean':
            raise Exception('replace "boolean" with "bool"')
        else:
            assert isinstance(dom, tuple), (var, dom)
            dtype = 'saturating'
        # owner
        if var in g.env_vars:
            owner = 'env'
        else:
            owner = 'sys'
        t[var] = dict(type=dtype, dom=dom, owner=owner)
    assert all(isinstance(u, int) for u in g)
    dtype = 'saturating'
    dom = (min(g), max(g))
    t[nodevar] = dict(type=dtype, dom=dom, owner=g.owner)
    return t


def _node_var_trans(g, nodevar, dvars):
    """Return data flow constraint on variables labeling nodes."""
    init = list()
    trans = list()
    # no AP labels ?
    if not dvars:
        return (init, trans)
    for u, d in g.nodes_iter(data=True):
        pre = _assign(nodevar, u, dvars)
        r = _to_action(d, dvars)
        if r == 'True':
            continue
        # initial node vars
        init.append('~ ({pre}) \/ ({r})'.format(pre=pre, r=r))
        # transitions of node vars
        trans.append("((({pre}) => ({r}))')".format(pre=pre, r=r))
    return (init, trans)


def _init_from_ts(initial_nodes, nodevar,
                  dvars, ignore_initial=False):
    """Return initial condition."""
    if ignore_initial:
        return list()
    if not initial_nodes:
        raise Exception('Transition system without initial states.')
    return [stx.disj(_assign(nodevar, u, dvars) for u in initial_nodes)]


def _sys_trans(g, nodevar, dvars):
    """Convert transition relation to safety formula."""
    logger.debug('modeling sys transitions in logic')
    sys_trans = list()
    for u in g:
        pre = _assign(nodevar, u, dvars)
        # no successors ?
        if not g.succ.get(u):
            logger.debug('node: {u} is deadend !'.format(u=u))
            sys_trans.append('({pre}) -> False'.format(pre=pre))
            continue
        post = list()
        for u, v, d in g.edges_iter(u, data=True):
            t = dict(d)
            t[stx.prime(nodevar)] = v
            r = _to_action(t, dvars)
            post.append(r)
        c = '({pre}) => ({post})'.format(pre=pre, post=stx.disj(post))
        sys_trans.append(c)
    s = stx.conj(sys_trans, sep='\n')
    return s


def _env_trans_from_sys_ts(g, nodevar, dvars):
    """Return safety assumption to prevent env from blocking sys."""
    denv = {k: v for k, v in dvars.items() if k in g.env_vars}
    env_trans = list()
    for u in g:
        # no successor states ?
        if not g.succ.get(u):
            continue
        # collect possible next env actions
        c = set()
        for u, w, d in g.edges_iter(u, data=True):
            t = _to_action(d, denv)
            if not t:
                continue
            c.add(t)
        # no next env actions ?
        if not c:
            continue
        post = stx.disj(c)
        pre = _assign(nodevar, u, dvars)
        env_trans.append('(({pre}) => ({post}))'.format(
            pre=pre, post=post))
    s = stx.conj(env_trans, sep='\n')
    return s


def _env_trans(g, nodevar, dvars, self_loops):
    """Convert environment transitions to safety formula.

    @type g: `networkx.MultiDigraph`
    @param nodevar: name of variable representing current node
    @type nodevar: `str`
    @type dvars: `dict`
    """
    env_trans = list()
    for u in g:
        pre = _assign(nodevar, u, dvars)
        # no successors ?
        if not g.succ.get(u):
            env_trans.append('{pre} => False'.format(pre=pre))
            if not self_loops:
                warnings.warn(
                    'Environment dead-end found.\n'
                    'If sys can force env to dead-end,\n'
                    'then GR(1) assumption becomes False,\n'
                    'and spec trivially True.')
            continue
        post = list()
        sys = list()
        for u, v, d in g.out_edges_iter(u, data=True):
            # action
            t = dict(d)
            t[stx.prime(nodevar)] = v
            r = _to_action(t, dvars)
            post.append(r)
            # what sys vars ?
            t = {k: v for k, v in d.items()
                 if k not in g.env_vars}
            r = _to_action(t, dvars)
            sys.append(r)
        # avoid sys winning env by blocking all edges
        # post.append(stx.conj_neg(sys))
        env_trans.append('({pre}) => ({post})'.format(
            pre=pre, post=stx.disj(post)))
    s = stx.conj(env_trans, sep='\n')
    return s


def _to_action(d, dvars):
    """Return `str` conjoining assignments and `"formula"` in `d`.

    @param d: (partial) mapping from variables in `dvars`
        to values in their range, defined by `dvars`
    @type d: `dict`
    @type dvars: `dict`
    """
    c = list()
    if 'formula' in d:
        c.append(d['formula'])
    for k, v in d.items():
        if k not in dvars:
            continue
        s = _assign(k, v, dvars)
        c.append(s)
    return stx.conj(c)


def _assign(k, v, dvars):
    """Return `str` of equality of variable `k` to value `v`.

    @type k: `str`
    @type v: `str` or `int`
    @type dvars: `dict`
    """
    dtype = dvars[k]['type']
    if dtype in ('int', 'saturating', 'modwrap'):
        s = '{k} = {v}'.format(k=k, v=v)
    elif dtype == 'str':
        s = '{k} = "{v}"'.format(k=k, v=v)
    elif dtype == 'bool':
        s = '{k} <=> {v}'.format(k=k, v=v)
    else:
        raise Exception('dtype is: {dtype}'.format(
            dtype=dtype))
    return _pstr(s)


def _prime_dict(d):
    """Return `dict` with primed keys and `dict` mapping to them."""
    p = dict((stx.prime(k), d[k]) for k in d)
    d2p = {k: stx.prime(k) for k in d}
    return p, d2p


def _pstr(x):
    return '({x})'.format(x=x)
