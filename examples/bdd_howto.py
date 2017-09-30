"""Manipulating first-order formulas using binary decision diagrams."""
from omega.symbolic import fol as _fol
from omega.symbolic import temporal as trl


def example_usage_of_ordinary_context():
    ctx = _fol.Context()
    ctx.declare(x=(1, 3), y='bool')


def example_uage_of_modal_context():
    aut = trl.Automaton()
    aut.declare_constants(a=(1, 5), b=(-3, 4), c='bool')
    aut.declare_variables(x=(4, 14), y=(-7, 8), z='bool')


if __name__ == '__main__':
    example_usage_of_ordinary_context()
    example_uage_of_modal_context()
