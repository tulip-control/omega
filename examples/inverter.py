"""Synthesis of an inverter with thresholds."""
import omega.games.gr1 as _gr1
import omega.symbolic.temporal as trl


def example_inverter():
    """Synthesize an inverter, and print its action."""
    aut = specify()
    synthesize(aut)
    print_synthesized_action(aut)


def specify():
    """Return specification of an inverter."""
    aut = trl.Automaton()
    aut.declare_variables(foo=(1, 15), bar=(-15, -1))
    aut.varlist.update(env=['foo'], sys=['bar'])
    aut.prime_varlists()
    # specify an inverter
    aut.init['env'] = r' foo \in 1..15 '
    aut.init['sys'] = r' bar \in -15..-1 '
    aut.action['env'] = r'''
        (* type invariant *)
        /\ foo \in 1..15
        /\ foo' \in 1..15
        '''
    aut.action['sys'] = r'''
        (* type invariant *)
        /\ (bar \in -15..-1)
        /\ (bar' \in -15..-1)

        (* inversion with one-step delay *)
        /\ (bar' + foo <= 0)
        /\ (bar' < -2)
        '''
    aut.win['<>[]'] = aut.bdds_from(' ~ (foo = 3) ')
    aut.win['[]<>'] = aut.bdds_from(' bar = - 3 ')
    # choose stepwise implication operator
    # and definition of realizability
    aut.plus_one = True
        # strictly causal stepwise implication
    aut.moore = True
        # implementation reads current state; not x'
    aut.qinit = r'\E \A'
        # disjoint-state throughout
    return aut


def synthesize(aut):
    """Create an implementation for `aut`."""
    fixpoint_iterates = _gr1.solve_streett_game(aut)
    _gr1.make_streett_transducer(*fixpoint_iterates, aut)


def print_synthesized_action(aut):
    """Print an expression for the transition formula."""
    synthesized_action = aut.action['impl']
    care = aut.type_hint_for([
        "foo", "bar", "foo'",
        "bar'", "_goal", "_goal'"])
    care = aut.to_bdd(care)
    # restrict the environment to values of interest
    u = synthesized_action & care
    expr = aut.to_expr(u, care=care, show_dom=True)
    print(expr)


if __name__ == '__main__':
    example_inverter()
