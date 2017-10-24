"""Synthesis of an inverter with thresholds."""
from omega.games import gr1
from omega.symbolic import temporal as trl


aut = trl.Automaton()
aut.declare_variables(foo=(1, 15), bar=(-15, -1))

aut.varlist.update(env=['foo'], sys=['bar'])
aut.prime_varlists()

# specify an inverter
aut.init['env'] = ' foo \in 1..15 '
aut.init['sys'] = ' bar \in -15..-1 '
aut.action['env'] = '''
    (* type invariant *)
    /\ foo \in 1..15
    /\ foo' \in 1..15
    '''
aut.action['sys'] = '''
    (* type invariant *)
    /\ (bar \in -15..-1)
    /\ (bar' \in -15..-1)

    (* inversion with one-step delay *)
    /\ (bar' + foo <= 0)
    /\ (bar' < -2)
    '''
aut.win['<>[]'] = aut.bdds_from(' ~ (foo = 3) ')
aut.win['[]<>'] = aut.bdds_from(' bar = - 3 ')

aut.plus_one = True  # strictly causal stepwise implication
aut.moore = True  # implementation reads current state; not x'
aut.qinit = '\E \A'  # disjoint-state throughout

fixpoint_iterates = gr1.solve_streett_game(aut)
gr1.make_streett_transducer(*fixpoint_iterates, aut)

synthesized_action = aut.action['impl']
care = aut.type_hint_for([
    "foo", "bar", "foo'", "bar'", "_goal", "_goal'"])
care = aut.to_bdd(care)
# restrict the environment to values of interest
u = synthesized_action & care
expr = aut.to_expr(u, care=care, show_dom=True)
print(expr)
