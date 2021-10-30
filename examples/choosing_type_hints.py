r"""If we pick too small a bitvector reasoning is unsound.

This script demonstrates the fundamental difference of
a typed language from an untyped language.
In TLA+, the formula:

(x \in 0..4) => (x \in 0..3)

is not valid.
"""
import omega.symbolic.fol as _fol


def unsound_reasoning():
    ctx = _fol.Context()
    ctx.declare(x=(0, 3))
    u = ctx.add_expr(r'x \in 0..3')
    v = ctx.add_expr(r'x \in 0..4')
    assert u == ctx.true
    assert v == ctx.true
    # (x \in 0..4) => (x \in 0..3)
    a = u | ~ v
    assert a == ctx.true
    # even more directly
    u = ctx.add_expr(r'\A x:  (x \in 0..4) => (x \in 0..3)')
    assert u == ctx.true
    #
    # Exercise: Restore soundness by changing 1 character.


if __name__ == '__main__':
    unsound_reasoning()
