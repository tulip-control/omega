"""How to compute from where Alice can reach her destination."""
from omega.logic import syntax as stx
from omega.symbolic import fixpoint as fx
from omega.symbolic import prime as prm
from omega.symbolic import temporal as trl


def do_it_yourself():
    """Compute states *from* where we can reach a goal."""
    aut, goal, action = spec()
    # Compute the least fixpoint,
    # so the states from where we can reach the `goal`
    # with one or more steps, or we are already there.
    vrs = aut.varlist['sys']
    primed_vrs = stx.prime_vars(vrs)
    r = aut.false
    rold = None
    # for sure != r, thus at least one iteration
    assert r != rold
    while r != rold:
        rold = r  # memo
        target = aut.replace_with_primed(vrs, r)
        pre = aut.exist(primed_vrs, action & target)
        r |= goal | pre
    assert prm.is_state_predicate(r)
    print_expr(r, aut)


def use_fixpoint_module():
    aut, goal, sys_action = spec()
    aut.varlist['env'] = list()  # controls all variables
    env_action = aut.true
    aut.plus_one = True
    aut.moore = True
    aut.build()  # store primed varlists
    r = fx.attractor(env_action, sys_action, goal, aut)
    print_expr(r, aut)


def spec():
    aut = trl.Automaton()
    aut.declare_variables(x=(1, 3), y=(0, 5), z='bool')
    aut.varlist['sys'] = ['x', 'y', 'z']
    goal = aut.to_bdd('(x = 2) /\ (y = 1) /\ z')
    action = aut.to_bdd('''
        (* type invariant *)
        /\ x \in 1..3
        /\ y \in 0..5
        /\ ((z <=> TRUE) \/ (z <=> FALSE))

        (* primed type invariant *)
        /\ x' \in 1..3
        /\ y' \in 0..5
        /\ ((z' <=> TRUE) \/ (z <=> FALSE))

        (* allowed changes *)
        /\ (x' = x + 1)
        /\ (y' = y - 2)
        /\ (z' <=> ~ z)
        ''')
    return aut, goal, action


def print_expr(u, aut):
    """BDD to expr in case of int and bool vars."""
    # currently, `to_expr` works with only
    # integer-valued variables
    aut.declare_constants(tmp=(0, 1))
    s = '\E z:  ({u} /\ (z <=> (tmp = 1)) )'.format(u=u)
    v = aut.to_bdd(s)
    s = aut.type_hint_for(['x', 'y', 'tmp'])
    care = aut.to_bdd(s)
    expr = aut.to_expr(v, care)
    print(expr)


if __name__ == '__main__':
    do_it_yourself()
    use_fixpoint_module()
