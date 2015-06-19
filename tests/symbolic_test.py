from omega.logic import bitvector as bv
from omega.symbolic import bdd as _bdd


def slugsin_parser(s, t):
    """Helper that converts prefix to infix syntax for readability."""
    slugs_table = t.to_slugs()
    ltl_parser = bv.Parser()
    p = ltl_parser.parse(s)
    bv.add_bitnames(slugs_table)
    s = p.flatten(t=slugs_table)
    slugsin_parser = _bdd.PrefixParser()
    print(slugsin_parser.parse(s))
