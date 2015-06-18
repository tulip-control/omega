"""Fixpoint algorithms using decision diagrams.

- attractor computation (least fixpoint)
- control invariance (greatest fixpoint)
- controllable preimage
"""
import logging
from dd import bdd as _bdd


logger = logging.getLogger(__name__)


def attractor(env_action, sys_action, target, aut,
              evars=None, moore=False, inside=None):
    """Return attractor for `target`.

    Keyword args as `ue_preimage`.

    @param inside: remain in this set
    """
    logger.info('++ attractor')
    # no free primed vars must remain after quantification
    # support = a.bdd.support(a.action)
    # support = {a.bdd.ordering[k] for k in support}
    # primed_support = set(k for k in map(a.prime.get, support)
    # if k is not None)
    # unquantified = primed_support.difference(
    # a.uvars).difference(a.evars)
    # assert not unquantified, unquantified
    # ancestors
    bdd = aut.bdd
    q = target
    qold = bdd.False
    while q != qold:
        pred = ue_preimage(env_action, sys_action, q, aut,
                           evars=evars, moore=moore)
        qold = q
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
    q = aut.bdd.True  # if unless is not None, then q = safe is wrong
    qold = None
    while q != qold:
        qold = q
        q = ue_preimage(env_action, sys_action, q, aut, evars=evars)
        q = aut.bdd.apply('and', safe, q)
        if unless is not None:
            q = aut.bdd.apply('or', q, unless)
    logger.info('-- cinv')
    return q


def ue_preimage(env_action, sys_action, target, aut,
                evars=None, moore=False):
    """Return controllable predecessor set.

    Preimage with mixed quantification.
    For each input that satisfies `env_action`,
    there exists an output that satisfies `sys_action`,
    such that the successor is in `target`.

    @param moore: set to swap quantification order to:
        \exists \forall
    """
    # TODO: controllable predecessor operator implemented
    # efficiently like relational product
    bdd = aut.bdd
    if evars is None:
        evars = aut.epvars
        uvars = aut.upvars
    else:
        uvars = set(aut.unprime).difference(evars)
    u = _bdd.rename(target, bdd, aut.prime)
    if moore:
        # \exists \forall
        u = bdd.apply('->', env_action, u)
        u = bdd.apply('and', sys_action, u)
        u = bdd.quantify(u, uvars, forall=True)
        u = bdd.quantify(u, evars, forall=False)
    else:
        # \forall \exists
        u = bdd.apply('and', sys_action, u)
        u = bdd.apply('->', env_action, u)
        u = bdd.quantify(u, evars, forall=False)
        u = bdd.quantify(u, uvars, forall=True)
    # optimized Mealy
    # doesn't work if transition relations are swapped
    # u = _bdd.preimage(sys_action, target, aut.prime,
    #                   evars, bdd, forall=False)
    # u = bdd.quantify(u, evars, forall=False)
    # u = bdd.apply('->', env_action, u)
    # u = bdd.quantify(u, uvars, forall=True)
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
    u = a.action['sys'][0]
    v = source
    assert u in a.bdd
    qvars = a.uevars
    image = _bdd.image(u, v, a.unprime, qvars,
                       a.bdd, forall=False)
    return image
