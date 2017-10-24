"""Realizability of properties expressed with the operator `WhilePlusHalf`.

The operator `WhilePlusHalf` implies the stepwise form:

```tla
[] \/ ~ Earlier(EnvNext(x, y, x', y'))
   \/ /\ Earlier(SysNext(x, y, x', y'))
      /\ \E u:  SysNext(x, y, u, y')
```

The controllable step operator in `omega.symbolic.fixpoint` has the form:

```tla
\E v:  \A u:
    /\ SysNext(x, y, u, v)
    /\ EnvNext(x, y, u, v) => Target(u, v)
```

for the choice of options `moore=True, plus_one=True`.
This script adapts the specification to the synthesizer,
by preprocessing the specified actions to derive appropriate actions to
pass to the synthesizer.
"""
# Copyright 2017 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
from omega.games import gr1
from omega.symbolic import temporal as trl


aut = trl.Automaton()
aut.declare_variables(x=(1, 5), y=(1, 5))
aut.varlist['env'] = ['x']
aut.varlist['sys'] = ['y']
aut.prime_varlists()
# environment formulas
env_init = aut.to_bdd('x = 1')
env_next = aut.to_bdd('''
    \/ (x' \in 1..5)
    \/ (x' = x)
    ''')
env_live = aut.to_bdd(' x = 2 ')
# component formulas
sys_init = aut.to_bdd('y \in 1..5  /\  (y = x)')
sys_next = aut.to_bdd('''
    \/ (y' = x)
    \/ (x' = x  /\  y' = y)
    ''')
sys_live = aut.to_bdd(' y = 2 ')


def exist(*arg):
    *vrs, u = arg
    return aut.exist(vrs, u)

def forall(*arg):
    *vrs, u = arg
    return aut.forall(vrs, u)


sys_init_synth = exist('x', sys_init) | ~ exist('x', 'y', env_init)
sys_init_synth &= sys_init | ~ env_init

sys_next_synth = (
    exist("x'", sys_next) &
    forall("x'", sys_next | ~ env_next))

aut.moore = True  # a synthesis option that describes the implementation
aut.plus_one = True  # a specification formula option, affects
    # init form and
    # the steady state (win set via the controllable step operator)
aut.qinit = '\E \A'  # whether state is disjoint or initially shared:
    # a synthesis option that describes the kind of implementation

# initial conditions
aut.init['env'] = env_init
aut.init['sys'] = sys_init_synth
# actions
aut.action['env'] = env_next
aut.action['sys'] = sys_next_synth
# liveness requirements
aut.win['<>[]'] = [~ env_live]
aut.win['[]<>'] = [sys_live]


fx_iterates = gr1.solve_streett_game(aut)
gr1.make_streett_transducer(*fx_iterates, aut)
