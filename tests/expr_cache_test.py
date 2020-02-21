from omega.symbolic import fol
from omega.symbolic import temporal


aut = temporal.Automaton()
aut.declare_variables(x='bool', y='bool')
u = aut.add_expr('x /\ y')
aut._clear_invalid_cache()
aut._cache_expr('x /\ y')
aut._fetch_expr(u)
aut._fetch_expr(u)
aut._add_expr('x')
del u
fol._bdd.reorder(aut.bdd)
aut._add_expr('y')
aut._add_expr('x \/ ~ y')
assert len(aut._bdd_to_expr) == 1, aut._bdd_to_expr
aut._clear_invalid_cache()
assert not aut._bdd_to_expr
