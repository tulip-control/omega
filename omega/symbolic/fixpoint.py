"""Fixpoint algorithms using decision diagrams.

- attractor computation (least fixpoint)
- control invariance (greatest fixpoint)
- controllable preimage
"""
import logging
from dd import bdd as _bdd


SYS = 'sys'  # default player for existential image
logger = logging.getLogger(__name__)


def attractor(env_action, sys_action, target, aut,
              evars=None, inside=None):
    """Return attractor for `target`.

    Keyword args as `ue_preimage`.

    @param inside: remain in this set
    """
    logger.info('++ attractor')
    # no free primed vars must remain after quantification
    # support = a.bdd.support(a.action)
    # support = {a.bdd.vars[k] for k in support}
    # primed_support = set(k for k in map(a.prime.get, support)
    # if k is not None)
    # unquantified = primed_support.difference(
    # a.uvars).difference(a.evars)
    # assert not unquantified, unquantified
    # ancestors
    bdd = aut.bdd
    q = target
    qold = None
    while q != qold:
        qold = q
        pred = ue_preimage(
            env_action, sys_action, q, aut, evars=evars)
        q = bdd.apply('or', qold, pred)
        if inside is not None:
            q = aut.bdd.apply('and', q, inside)
    logger.info('-- attractor')
    return q


def trap(env_action, sys_action, safe, aut,
         evars=None, unless=None):
    """Return subset of `safe` with contolled exit.

    @param unless: if `None`, then returned controlled invariant
        subset of `safe`. Otherwise, this defines an allowed set.
    @rtype: BDD node
    """
    logger.info('++ cinv')
    bdd = aut.bdd
    q = bdd.true  # if unless is not None, then q = safe is wrong
    qold = None
    while q != qold:
        qold = q
        pre = ue_preimage(env_action, sys_action, q, aut, evars=evars)
        q = bdd.apply('and', safe, pre)
        if unless is not None:
            q = bdd.apply('or', q, unless)
    logger.info('-- cinv')
    return q


def ue_preimage(env_action, sys_action, target, aut,
                evars=None):
    r"""Return controllable predecessor set.

    Preimage with alternating quantification.
    Quantifier order: If `aut.moore`:

      - \E \A, else
      - \A \E

    Implication causality: If `aut.plus_one`:

      - /\ sys_action
        /\ env_action => target

      - env_action => /\ sys_action
                      /\ target
    """
    # TODO: controllable predecessor operator implemented
    # efficiently like relational product
    bdd = aut.bdd
    if evars is None:
        evars = aut.epvars
        uvars = aut.upvars
    else:
        uvars = set(aut.unprime).difference(evars)
    u = bdd.rename(target, aut.prime)
    if aut.plus_one:
        u = bdd.apply('and', sys_action, u)
        u = bdd.apply('->', env_action, u)
    else:
        u = bdd.apply('->', env_action, u)
        u = bdd.apply('and', sys_action, u)
    if aut.moore:
        # \E \A
        u = bdd.forall(uvars, u)
        u = bdd.exist(evars, u)
    else:
        # \A \E
        u = bdd.exist(evars, u)
        u = bdd.forall(uvars, u)
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
        q = a.bdd.apply('or', qold, post)
        q = a.bdd.apply('and', q, constrain)
    return q


def ee_image(source, a):
    """Existential image."""
    u = a.action[SYS][0]
    v = source
    assert u in a.bdd
    qvars = a.uevars
    bdd = a.bdd
    u = bdd.apply('and', u, v)
    u = bdd.quantify(u, qvars, forall=False)
    u = bdd.rename(u, a.unprime)
    image = u
    return image
