"""Demonstrate counterexample to strong reduction of original algorithm."""
import omega.symbolic.fol as _fol
import omega.symbolic.cover as cov


def test_counterexample_to_strong_reduction():
    """Not all minimal solutions can be recovered.

    This counterexample shows that the minimal covering
    algorithm does not ensure strong reduction.
    The reason is that the minimal cover before
    unfloors has max floors elements that are
    incomparable to some elements from which we
    could build alternative minimal covers.
    """
    # For now `cov.minimize` creates the primes etc in
    # a specific way, for a specific basis.
    # This example doesn't fit in that recipe,
    # so we rewrite some of the code in `minimize`.
    fol = _fol.Context()
    fol.to_bdd = fol.add_expr
    x_vars = dict(x=(0, 8))
    p_vars = dict(p=(0, 8))
    q_vars = dict(q=(0, 8))
    u_vars = dict(p_cp=(0, 8))
    fol.declare(**x_vars, **p_vars, **q_vars, **u_vars)
    p_eq_q = fol.to_bdd(r'p \in 0..8  /\  q \in 0..8  /\ p = q')
    leq = r'''
    # (* layer 1 *)
    \/ (p = 0  /\  q = 6)
    \/ (p = 0  /\  q = 7)
    \/ (p = 0  /\  q = 8)
    # (* layer 2 *)
    \/ (p = 6  /\  q = 2)
    \/ (p = 6  /\  q = 3)
    \/ (p = 7  /\  q = 3)
    \/ (p = 7  /\  q = 4)
    \/ (p = 8  /\  q = 4)
    \/ (p = 8  /\  q = 5)
    # (* layer 3 *)
    \/ (p = 2  /\  q = 1)
    \/ (p = 3  /\  q = 1)
    \/ (p = 4  /\  q = 1)
    \/ (p = 5  /\  q = 1)
    # transitivity
    \/ (p = 0 /\ q = 2)
    \/ (p = 0 /\ q = 3)
    \/ (p = 0 /\ q = 4)
    \/ (p = 0 /\ q = 5)
    \/ (p = 0 /\ q = 1)

    \/ (p = 6 /\ q = 1)
    \/ (p = 7 /\ q = 1)
    \/ (p = 8 /\ q = 1)
    # equality
    \/ (p = q /\ p \in 0..8 /\ q \in 0..8)
    '''
    p_leq_q = fol.to_bdd(leq)
    u_leq_p = fol.to_bdd(leq.replace('p', 'p_cp').replace('q', 'p'))
    p_leq_u = fol.to_bdd(leq.replace('q', 'p_cp'))
    # bundle
    prm = Parameters()
    prm.x_vars = set(x_vars)
    prm.p_vars = set(p_vars)
    prm.q_vars = set(q_vars)
    prm.u_vars = set(u_vars)
    #
    prm.p_to_q = dict(p='q')
    prm.q_to_p = dict(q='p')
    prm.p_to_u = dict(p='p_cp')
    #
    prm.u_leq_p = u_leq_p
    prm.p_leq_u = p_leq_u
    prm.p_leq_q = p_leq_q
    prm.p_eq_q = p_eq_q
    #
    x = fol.add_expr(r'p \in 6..8')
    y = fol.add_expr(r'p \in 2..5')
    #
    path_cost = 0.0
    bab = cov._BranchAndBound(prm, fol)
    bab.upper_bound = cov._upper_bound(
        x, y, prm.p_leq_q, prm.p_to_q, fol)
    cover, _ = cov._traverse(x, y, path_cost, bab, fol)
    # assert that the result is indeed a cover
    f = x
    assert _covers(cover, f, prm, fol)
    # assert the cover is as expected
    primes = list(fol.pick_iter(cover))
    print(primes)
    primes_ = [dict(p=3), dict(p=4)]
    assert len(primes) == 2, primes
    for p in primes_:
        assert p in primes, (p, primes)


class Parameters:
    """Stores parameters values and lattice definition."""

    def __init__(self):
        x_vars = list()
        # variable type hints (as `set`)
        self.x_vars = None
        self.p_vars = None
        self.q_vars = None
        self.u_vars = None
        # mappings between variables
        self.p_to_q = None
        self.q_to_p = None
        self.p_to_u = None
        # relations
        self.u_leq_p = None
        self.p_leq_u = None
        self.p_leq_q = None
        self.p_eq_q = None
        self.fol = None


def _covers(
        cover_p, f, prm, fol):
    """See `omega.symbolic.cover._covers`."""
    fp = f  # x is p in this simple example
    cover_q = fol.let(prm.p_to_q, cover_p)
    # \A p:  \/ ~ f(p)
    #        \/ \E q:  cover(q) /\ (p <= q)
    r = cover_q & prm.p_leq_q
    r = fol.exist(prm.q_vars, r)
    r |= ~ fp
    r = fol.forall(prm.p_vars, r)
    return r == fol.true


if __name__ == '__main__':
    test_counterexample_to_strong_reduction()
