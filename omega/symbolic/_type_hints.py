"""Utilities for interval constraints.

This module may be better merged into `fol` or `bitvector`.
"""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging

import natsort

from omega.logic import syntax as stx


log = logging.getLogger(__name__)


def _clip_subrange(ab, dom, x):
    """Return `ab` clipped to `dom`."""
    a, b = ab
    u, v = dom
    assert a <= b, (a, b)
    assert u <= v, (u, v)
    # assert not disjoint ranges
    assert a <= v and b >= u, (ab, dom, x)
    a = max(a, u)
    b = min(b, v)
    assert a <= b, (a, b)
    if a == u and v == b:
        a, b = None, None
    return a, b


def _check_type_hint(a, b, hint, var):
    """Raise `AssertionError` and log warnings."""
    if a > b:
        raise AssertionError((
            'Empty orthotope interval `{a} .. {b}` for '
            'variable "{var}".').format(
                a=a, b=b, var=var))
    dom = hint['dom']
    limits = _bitfield_limits(hint)
    if a > dom[1] or b < dom[0]:
        log.warning((
            'Interval `a .. b = {a} .. {b}` is disjoint from '
            'type hint `dom = {dom[0]} .. {dom[1]}` for '
            'variable "{var}".\n'
            'Use type hint `dom` as care set.\n').format(
                a=a, b=b, dom=dom, var=var))
    # `a <= dom[0]` should imply `a = limits[0]`,
    # because otherwise only possible if some point
    # outside type hint matters, preventing prime to
    # extend to the limits of the bitfield
    if a <= dom[0] and a > limits[0]:
        log.warning((
            'a = {a} not in interior of type hint '
            '`dom = {dom[0]} .. {dom[1]}` but unequal to '
            'low of `limits = {limits[0]} .. {limits[1]}` '
            'for variable "{var}".\n'
            'Use type hint as care set.\n').format(
                a=a, dom=dom, limits=limits, var=var))
    if b >= dom[1] and b < limits[1]:
        log.warning((
            'b = {b} not in interior of type hint '
            '`dom = {dom[0]} .. {dom[1]}` but unequal to '
            'high of `limits = {limits[0]} .. {limits[1]}` '
            'for variable "{var}".\n'
            'Use type hint as care set.\n').format(
                b=b, dom=dom, limits=limits, var=var))


def _list_type_hints(variables, table):
    """Return `list` of set containment constraints.

    These are the high-level type invariant,
    as defined by the type hints (`"dom"`) in `table`.
    """
    assert variables, variables
    r = list()
    keys = natsort.natsorted(variables)
    for x in keys:
        dom = table[x]['dom']
        s = _format_range(x, *dom)
        r.append(s)
    return r


def _list_limits(vrs, table):
    """Return `list` of bitfield limits.

    Each limit has the form `x \in a .. b`

    @param table: must be bitblasted
    """
    assert vrs, vrs
    r = list()
    keys = natsort.natsorted(vrs)
    for x in keys:
        limits = _bitfield_limits(table[x])
        s = _format_range(x, *limits)
        r.append(s)
    return r


def _bitfield_limits(hint):
    """Return extremal integer values of bitfield."""
    width = hint['width']
    if hint['signed']:
        n = width - 1
        limits = (- 2**n, 2**n - 1)
        return limits
    # unsigned: so variable ranges over values of same sign
    min_, max_ = hint['dom']
    # flip ?
    if min_ >= 0:
        limits = (0, 2**width - 1)
    else:
        assert max_ < 0, max_
        limits = (- 2**width, -1)
    return limits


def _conjoin_type_hints(vrs, fol):
    """Return conjunction of type hints for `vrs` as BDD."""
    r = list()
    for var in vrs:
        hints = fol.vars[var]
        if hints['type'] == 'bool':
            # The constraint `var \in BOOLEAN` will
            # anyway dissapear at the BDD layer.
            continue
        assert hints['type'] == 'int', hints
        a, b = hints['dom']
        s = r'({a} <= {var}) /\ ({var} <= {b})'
        type_hints = s.format(a=a, b=b, var=var)
        r.append(type_hints)
    u = fol.add_expr(stx.conj(r))
    return u


def _format_range(var, a, b):
    """Return string for set containment `var \in a .. b`."""
    return r'{var} \in {a} .. {b}'.format(
        var=var, a=a, b=b)
