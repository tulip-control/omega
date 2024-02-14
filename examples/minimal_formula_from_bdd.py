"""Print a minimal formula from a BDD over integer variables.

Use this to read what BDDs your algorithms are computing,
including the synthesized controllers and contract specifications.
"""
import omega.symbolic.fol as _fol


def print_minimal_formula():
    """How to see what expression a BDD represents."""
    c = _fol.Context()
    c.declare(x=(1, 5), y=(0, 14))
    s = r'''
        \/ (x = 2  /\  y <= 13)
        \/ (1 <= x  /\ x <= 4  /\ y \in 5..10)
        '''
    u = c.add_expr(s)
    s = r'''
        /\ (1 <= x  /\  x <= 5)
        /\ (0 <= y  /\  y <= 14)
        '''
    care = c.add_expr(s)
    s = c.to_expr(u, care=care, show_dom=True)
    print(s)


if __name__ == '__main__':
    print_minimal_formula()
