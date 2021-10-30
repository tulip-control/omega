"""Manipulating first-order formulas using binary decision diagrams."""
import omega.symbolic.fol as _fol
import omega.symbolic.temporal as trl


def example_usage_of_ordinary_context():
    ctx = _fol.Context()
    ctx.declare(
        x=(1, 3),
        y='bool',
        z=(1, 3))
    u = ctx.add_expr(r' x = 1 /\ ~ y ')
    defs = dict(x='z')
    u = ctx.let(defs, u)


def example_uage_of_modal_context():
    aut = trl.Automaton()
    aut.declare_constants(a=(1, 5), b=(-3, 4), c='bool')
    aut.declare_variables(x=(4, 14), y=(-7, 8), z='bool')


if __name__ == '__main__':
    example_usage_of_ordinary_context()
    example_uage_of_modal_context()
