#!/usr/bin/env python
"""Test `omega.fol_bdd`."""
from omega.symbolic import symbolic


def test_quantifiers():
    """Test quantifier syntax in LTL."""
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='int', dom=(0, 5), owner='sys'))
    aut = a.build()
    # TYPENESS !!!
    s = '\E x: (x = 7)'
    u = aut.add_expr(s)
    print(u)


if __name__ == '__main__':
    test_quantifiers()
