"""Fixpoint algorithms using decision diagrams.

- attractor computation (least fixpoint)
- control invariance (greatest fixpoint)
- controllable preimage
"""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging
from dd import bdd as _bdd
from omega.symbolic.bdd import is_state_predicate


SYS = 'sys'  # default player for existential image
logger = logging.getLogger(__name__)


def attractor(env_action, sys_action, target, aut,
              inside=None):
    """Return attractor for `target`.

    Keyword args as `step`.

    @param inside: remain in this set
    """
    logger.info('++ attractor')
    assert is_state_predicate(target), aut.support(target)
    # ancestors
    q = target
    qold = None
    while q != qold:
        qold = q
        pred = step(env_action, sys_action, q, aut)
        q |= pred
        if inside is not None:
            q &= inside
    assert is_state_predicate(q), aut.support(q)
    logger.info('-- attractor')
    return q


def trap(env_action, sys_action, safe, aut,
         unless=None):
    """Return subset of `safe` with contolled exit.

    @param unless: if `None`, then returned controlled invariant
        subset of `safe`. Otherwise, this defines an allowed set.
    @rtype: BDD node
    """
    logger.info('++ cinv')
    assert is_state_predicate(safe), aut.support(safe)
    q = aut.true  # if `unless is not None`,
                  # then `q = safe` is wrong
    qold = None
    while q != qold:
        qold = q
        pre = step(env_action, sys_action, q, aut)
        q = safe & pre
        if unless is not None:
            q |= unless
    assert is_state_predicate(q), aut.support(q)
    logger.info('-- cinv')
    return q


def step(env_action, sys_action, target, aut):
    r"""Return controllable predecessor set.

    Preimage with alternating quantification.
    Quantifier order: If `aut.moore`:

      - \E epvars: \A upvars, else
      - \A upvars: \E epvars

    Implication causality: If `aut.plus_one`:

      - /\ sys_action
        /\ env_action => target

      - env_action => /\ sys_action
                      /\ target
    """
    # TODO: use efficient substitution
    epvars = aut.epvars
    upvars = aut.upvars
    u = bdd.rename(target, aut.prime)
    if aut.plus_one:
        # sys_action /\ (env_action => target')
        u |= ~ env_action
        u &= sys_action
    else:
        # env_action => (sys_action /\ target')
        u &= sys_action
        u |= ~ env_action
    if aut.moore:
        # \E evars': \A uvars'
        u = bdd.forall(upvars, u)
        u = bdd.exist(epvars, u)
    else:
        # \A uvars': \E evars'
        u = bdd.exist(epvars, u)
        u = bdd.forall(upvars, u)
    return u


def preimage(trans, target, qvars, automaton, forall):
    """Preimage with non-mixed quantification."""
    return _bdd.preimage(
        trans, target, automaton.prime,
        qvars, automaton.bdd, forall)


def descendants(source, constrain, a, future=True):
    """Existential descendants of `source` in `constrain`."""
    if future:
        q = ee_image(source, a)
    else:
        q = source
    qold = None
    while q != qold:
        post = ee_image(q, a)
        qold = q
        q |= post
        q &= constrain
    return q


def ee_image(source, a):
    """Existential image."""
    u = a.action[SYS][0]
    v = source
    qvars = a.uevars
    bdd = a.bdd
    u &= v
    u = bdd.exist(qvars, u)
    u = bdd.rename(u, a.unprime)
    return u
