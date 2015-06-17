import openpromela.bdd
from openpromela import bitvector


def slugsin_parser(s, t):
    """Helper that converts prefix to infix syntax for readability."""
    slugs_table = t.to_slugs()
    ltl_parser = bitvector.Parser()
    p = ltl_parser.parse(s)
    bitvector.add_bitnames(slugs_table)
    s = p.flatten(t=slugs_table)
    slugsin_parser = openpromela.bdd.PrefixParser()
    print slugsin_parser.parse(s)
