from omega.symbolic import temporal
# from dd import cudd


aut = temporal.Automaton()
aut.declare_variables(x='bool', y='bool')
u = aut.add_expr('x /\ y')
aut._clear_invalid_cache()
aut._cache_expr('x /\ y')
aut._fetch_expr(u)
aut._fetch_expr(u)
aut._add_expr('x')
del u
# cudd.reorder(aut.bdd)
aut._add_expr('y')
aut._add_expr('x \/ ~ y')
print(aut._bdd_to_expr)
aut._clear_invalid_cache()
print(aut._bdd_to_expr)
