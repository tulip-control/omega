"""Syntactic check for GR(1) fragment."""
# Copyright 2015-2020 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
from __future__ import absolute_import

from omega.logic import lexyacc
from omega.logic.ast import Nodes
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import temporal as trl


TEMPORAL_OPERATORS = {'[]', '<>'}
parser = lexyacc.Parser()


def closed_system_to_automaton(formula):
    """Return `Automaton` from temporal formula `f`.

    @type formula: `str` describing a closed system with
        GR(1) liveness
    @rtype: `temporal.Automaton`
    """
    aut = trl.Automaton()
    d = split_gr1(formula)
    aut.init['sys'] = _to_bdd(d['init'], aut)
    aut.action['sys'] = _to_bdd(d['action'], aut)
    aut.win['sys'] = {
        '<>[]': [_to_bdd([t], aut) for t in d['persistence']],
        '[]<>': [_to_bdd([t], aut) for t in d['recurrence']]}
    return aut


def _to_bdd(conjuncts, aut):
    u = Nodes.Operator('/\\', conjuncts)
    flat_expr = u.flatten(t=aut.vars)  # with defs ?
    return sym_bdd.add_expr(flat_expr, aut.bdd)


def split_gr1(formula):
    """Return `dict` of GR(1) subformulas.

    The formula `f` is assumed to be a conjunction of:

    - `ACTION`
    - `[] ACTION`
    - one generalized Streett pair

    @param formula: temporal-level formula
    @type formula: `str`

    @return: `dict(init=list, action=list,
        recurrence=list, persistence=list)`
        where each `list` contains abstract syntax trees.
    """
    tree = parser.parse(formula)
    return _temporal_to_canonical(tree)


def _temporal_to_canonical(u):
    """Return state predicates of temporal formula.

    @param u: syntax tree
    """
    flat_conj = flatten_op(u, '/\\')
    init = list()
    action = list()
    recurrence = list()
    persistence = list()
    for v in flat_conj.operands:
        has_box = _has_operator(v, ['[]'])
        has_diamond = _has_operator(v, ['<>'])
        if has_box and not has_diamond:
            _split_always(v, action)
        elif has_box and has_diamond:
            _split_liveness(v, recurrence, persistence)
        else:
            # allow bare actions (raw TLA+)
            assert not (has_box or has_diamond)
            assert not _has_operator(v, ['X'])
            init.append(v)
    return dict(
        init=init, action=action,
        recurrence=recurrence, persistence=persistence)


def _split_always(u, action):
    op = u.operator
    assert op == '[]', op
    v, = u.operands
    assert not _has_operator(v, ['[]', '<>'])
    action.append(v)


def _split_liveness(u, recurrence, persistence):
    """Collect one generalized Streett pair."""
    assert not persistence  # GR(1), not GR(k)
    flat_disj = flatten_op(u, '\/')
    for v in flat_disj.operands:
        op = v.operator
        if op == '<>':
            w, = v.operands
            assert w.operator == '[]', w
            state, = w.operands
            assert not _has_operator(state, ['[]', '<>', 'X'])
            persistence.append(state)
        elif op in ('/\\', '[]'):
            _split_recurrence(v, recurrence)
        else:
            raise ValueError(op)


def _split_recurrence(u, recurrence):
    """Collect a conjunction of []<> formulas."""
    flat_conj = flatten_op(u, '/\\')
    for v in flat_conj.operands:
        op = v.operator
        assert op == '[]', op
        w, = v.operands
        assert w.operator == '<>', w
        state, = w.operands
        assert not _has_operator(state, ['[]', '<>', 'X'])
        recurrence.append(state)


def flatten_op(u, op):
    """Return n-ary conjunction, from nested one."""
    operands = list()
    _flatten_op(u, op, operands)
    return Nodes.Operator(op, *operands)


def _flatten_op(u, op, operands):
    """Recurse to flatten conjunction."""
    operator = getattr(u, 'operator', None)
    if operator == op:
        for v in u.operands:
            _flatten_op(v, op, operands)
    else:
        operands.append(u)


def _is_temporal(u):
    return _has_operator(u, TEMPORAL_OPERATORS)


def _has_operator(u, operators):
    # terminals and `list` allowed
    if not hasattr(u, 'operator'):
        return False
    return (
        u.operator in operators
        or any(_has_operator(v, operators)
               for v in u.operands))
