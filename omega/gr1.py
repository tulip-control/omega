"""Syntactic check for GR(1) fragment."""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from __future__ import absolute_import

import networkx as nx

from omega.logic import lexyacc
from omega.logic.ast import Nodes
from omega.logic import syntax as stx
from omega.symbolic import symbolic
from omega.logic import transformation as tx


parser = lexyacc.Parser()


def ltl_to_automaton(f):
    """Return `Automaton` from LTL formula `f` as `str`.

    Formula `f` must be in the form:

      A -+-> G

    where each of A, G is a conjunction of terms: `B`, `[]C`, `[]<>B`.
    For more details on `B, C`, see `split_gr1`.

    @type f: `str`
    @rtype: `symbolic.Automaton`
    """
    t = parser.parse(f)
    assert t.operator == '-+->'
    env, sys = t.operands
    d = {'assume': split_gr1(env),
         'assert': split_gr1(sys)}
    a = symbolic.Automaton()
    a.init['env'] = d['assume']['init']
    a.init['sys'] = d['assert']['init']
    a.action['env'] = d['assume']['[]']
    a.action['sys'] = d['assert']['[]']
    a.win['env'] = d['assume']['[]<>']
    a.win['sys'] = d['assert']['[]<>']
    return a


def split_gr1(s):
    """Return `dict` of GR(1) subformulae.

    The formula `f` is assumed to be a conjunction of expressions
    of the form:
      `B`, `[]C` or `[]<>B`
    where:
      - `C` can contain "next"
      - `B` cannot contain "next"

    @param f: temporal logic formula
    @type f: `str` or AST

    @return: conjunctions of formulae A, B as `str`,
    grouped by keys:
        `'init', '[]', '[]<>'`
    @rtype: `dict` of `str`: `list` of `str`
    """
    u = parser.parse(s)
    init = _split_gr1(u, 'init')
    action = _split_gr1(u, 'action')
    gf = list()
    _split_gr1(u, 'win', gf=gf)
    win = [v.flatten() for v in gf]
    d = dict(init=[init.flatten()],
             G=[action.flatten()],
             GF=win)
    _assert_admissible_operators(d)
    return d


def _split_gr1(u, context, gf=None):
    # terminal ?
    if hasattr(u, 'value'):
        if context == 'init':
            return u
        else:
            return Nodes.Bool('True')
    # operator
    if u.operator == '/\\':
        v, w = u.operands
        p = _split_gr1(v, context, gf)
        q = _split_gr1(w, context, gf)
        return Nodes.Binary('/\\', p, q)
    assert u.operator != '/\\', u.operator
    if context == 'init':
        if u.operator == '[]':
            return Nodes.Bool('True')
        else:
            return u
    if u.operator != '[]':
        return Nodes.Bool('True')
    assert u.operator == '[]'
    (v,) = u.operands
    # terminal ?
    if hasattr(v, 'value'):
        if context == 'action':
            return v
        else:
            return Nodes.Bool('True')
    assert hasattr(v, 'operator'), v
    if context == 'action':
        # GF ?
        if v.operator == '<>':
            return Nodes.Bool('True')
        return v
    elif context == 'win':
        if v.operator != '<>':
            return
        assert v.operator == '<>'
        (w,) = v.operands
        gf.append(w)


def _assert_admissible_operators(d):
    action_ops = {'[]', '<>', 'U', 'V', 'R'}
    init_ops = set(action_ops)
    init_ops.add('X')
    operators = dict(init=init_ops, G=action_ops, GF=init_ops)
    for part, f in list(d.items()):
        ops = operators[part]
        for s in f:
            op = has_operator(s, ops)
            if op is None:
                continue
            raise AssertionError((
                'found inadmissible operator "{op}" '
                'in "{p}" formula. Parts:\n {d}').format(
                    op=op, p=part, d=d))


def has_operator(s, operators):
    u = parser.parse(s)
    return _has_operator(u, operators)


def _has_operator(u, operators):
    # terminal ?
    if hasattr(u, 'value'):
        return None
    # operator
    assert hasattr(u, 'operator')
    if u.operator in operators:
        return u.operator
    for v in u.operands:
        op = _has_operator(v, operators)
        if op is not None:
            return op
    return None


def split_gr1_old(f):
    """Earlier implementation of `split_gr1`.

    Does not preserve formula structure.
    Instead, it arranges conjunction operators as a
    binary tree.
    """
    # TODO: preprocess by applying syntactic identities: [][] = [] etc
    if stx.isinstance_str(f):
        t = f
    else:
        t = parser.parse(f)
    g = tx.Tree.from_recursive_ast(t)
    # collect boundary of conjunction operators
    Q = [g.root]
    b = list()  # use lists to preserve as much given syntactic order
    while Q:
        u = Q.pop()
        # terminal ?
        if not g.succ.get(u):
            b.append(u)
            continue
        # operator
        if u.operator == '/\\':
            # use `u.operands` instead of `g.successors`
            # to preserve original order
            Q.extend(u.operands)
        else:
            b.append(u)
    d = dict(init=list(), G=list(), GF=list())
    for u in b:
        # terminal ?
        if not g.succ.get(u):
            d['init'].append(u)
            continue
        # some operator
        if u.operator != '[]':
            d['init'].append(u)
            continue
        # G
        (v,) = u.operands
        # terminal in G ?
        if not g.succ.get(v):
            d['[]'].append(v)
            continue
        # some operator in G
        if v.operator == '<>':
            (w,) = v.operands
            d['[]<>'].append(w)
        else:
            # not a GF
            d['[]'].append(v)
    # assert only admissible temporal operators
    ops = {'[]', '<>', 'U', 'V', 'R'}
    operators = dict(G=ops)
    ops = set(ops)
    ops.add('X')
    operators.update(init=ops, GF=ops)
    for part, f in d.items():
        ops = operators[part]
        for u in f:
            op = has_operator(u, g, ops)
            if op is None:
                continue
            raise AssertionError((
                'found inadmissible operator "{op}" '
                'in "{f}" formula. Parts:\n {d}').format(
                    op=op, f=part, d=d))
    # conjoin (except for progress)
    init = conj(u.flatten() for u in reversed(d['init']))
    d['init'] = [init]
    safe = conj(u.flatten() for u in reversed(d['[]']))
    d['[]'] = [safe]
    # flatten individual progress formulae
    d['[]<>'] = [u.flatten() for u in d['[]<>']]
    return d


def conj(x):
    return ' /\ '.join(x)


def has_operator_old(u, g, operators):
    """Return `True` if AST `u` contains any `operators`."""
    try:
        if u.operator in operators:
            return u.operator
    except AttributeError:
        pass
    for v in nx.descendants(g, u):
        # terminal
        if not g.succ.get(v):
            continue
        # operator
        # is it temporal except for 'X' ?
        if v.operator in operators:
            return v.operator
    return None
