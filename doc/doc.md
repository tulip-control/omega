# `omega` documentation


## Table of Contents


- [Overview](#overview)
    - [Specifications](#specifications)
    - [Synthesis tools in `omega`](#synthesis-tools-in-omega)
- [Writing specifications](#writing-specifications)
    - [The module `omega.symbolic.temporal`](#the-module-omegasymbolictemporal)
    - [The module `omega.symbolic.fol`](#the-module-omegasymbolicfol)
    - [Printing minimal formulas from BDDs](
          #printing-minimal-formulas-from-bdds)
- [Enumeration](#enumeration)
- [Annotating graphs with formulas](#annotating-graphs-with-formulas)
    - [Converting annotated graphs to symbolic automata](#converting-annotated-graphs-to-symbolic-automata)
- [Synthesizing implementations](#synthesizing-implementations)
    - [Determinism ?](#determinism)
    - [Symbolic function synthesis](#symbolic-function-synthesis)
    - [Enumerating a state machine](#enumerating-a-state-machine)
- [Assembling implementations for simulation](#assembling-implementations-for-simulation)
- [Writing your own symbolic algorithms](#writing-your-own-symbolic-algorithms)
- [Lower-level and internal details](#lower-level-and-internal-details)
    - [Table of variables](#table-of-variables)
        - [Simple format](#simple-format)
        - [Detailed and bitblasted formats](#detailed-and-bitblasted-formats)
    - [Bitblasting](#bitblasting)
    - [BDDizing](#bddizing)
    - [Parsing](#parsing)
- [Temporal logic syntax](#temporal-logic-syntax)
- [The deprecated class `omega.symbolic.symbolic.Automaton`](
      #the-deprecated-class-omegasymbolicsymbolicautomaton)
- [Some design notes](#some-design-notes)
- [Copying](#copying)


## Overview


Using the `omega` package you can write raw
[TLA+](https://en.wikipedia.org/wiki/Temporal_logic_of_actions) specifications,
synthesize implementations from these specifications, and write your own
symbolic algorithms that rely on binary decision diagrams. You can assemble
and simulate the synthesized implementations, and inspect the results of
symbolic computations as minimal formulas.


### Specifications


Writing a specification [does not mean](https://doi.org/10.1145/69624.357207)
that the specification is implementable. Implementable specifications are
called *realizable*. Instead of constructing an implementation by hand,
you can *synthesize* one by giving the specification to a synthesis algorithm
from those available in the module `omega.games.gr1`.
A more precise description of what we mean by synthesis is in the TLA+
module `spec/Realizability.tla`.


What is an implementation? How is it different from a specification?
A specification that pins down every single step-by-step detail of how the
state changes is an implementation. So the distinction between implementation
and specification relates to how much freedom of behavior each one allows.


Liveness formulas can specify behavior without saying what the next step
should be. In addition to liveness, temporal logic includes safety formulas.
You can think of safety formulas as a description of
a [state machine](https://doi.org/10.1016/0304-3975(91)90224-P):
which states can be initial, and how the state can change.


### Synthesis tools in `omega`


The computational cost of synthesis depends mainly on the liveness part of
the specification. Synthesis of implementations from specifications with
one generalized Streett pair as liveness formula has [reasonable complexity](
    https://doi.org/10.1007/11609773_24). This kind of liveness properties
is also known as GR(1). A Streett pair has the form:

```tla
\/ <>[] P
\/ []<> R
```

A *generalized* Streett pair has the form:

```tla
\/ <>[]P1 \/ <>[]P2 \/ ... \/ <>[]Pk
\/ []<>R1 /\ []<>R2 /\ ... /\ []<>Rm
```

The difference is the disjunction between Ps and the conjunction between Rs,
which cost little extra computation.
GR(1) synthesis is available in the module `omega.games.gr1`, mainly via the
functions:

- `solve_streett_game` and
- `make_streett_transducer`

Specifications with one generalized Rabin pair are also supported.
These have the form:

```tla
/\ <>[]P1 \/ <>[]P2 \/ ... \/ <>[]Pk
/\ []<>R1 /\ []<>R2 /\ ... /\ []<>Rm
```

Rabin synthesis is available via the functions:

- `solve_rabin_game`
- `make_rabin_transducer`

Synthesis creates a state machine for the implementation, in the form of
BDDs for the initial condition and action. These BDDs are stored in the
same automaton that was given to the `*_transducer` functions mentioned
above.

You can *enumerate* the state machine over all states that are relevant
to the assumed environment behavior by calling the function
`omega.games.enumeration.action_to_steps`.

The synthesized state machine in the literature is called also
strategy or controller (irrespective of how it is represented, i.e.,
BDDs, formulas, or enumeration of relevant states).


## Writing specifications


Since both specifications and implementations can be described by
a combination of a state machine with some liveness property, one data
structure suffices, namely the class `omega.symbolic.temporal`. Sometimes
it is easier to annotate a graph with formulas, and translate that to temporal
logic. The class `omega.automata.TransitionSystem` can be used for that
purpose. Below are examples of how to use these classes.


### The module `omega.symbolic.temporal`


Since specifications and implementations are both state machines, the same
data structure represents them in `omega`. This data structure is
`omega.symbolic.temporal.Automaton`, and has attributes that store liveness
too, to accommodate for specifications that do have a liveness part.
The interesting attributes of an `Automaton` are:

- `init`: stores initial conditions (state predicates)
- `action`: stores what steps the state machine can take
  (transition predicates)
- `win`: stores predicates that represent the liveness part.
  For example, expressions from recurrence formulas.

These attributes are binary decision diagrams (BDDs).
You can use formulas to set the values of these attributes.


A symbolic automaton provides a “context” for symbolic computation, in the
sense of a [symbol table](https://en.wikipedia.org/wiki/Symbol_table),
together with a translator from first-order formulas to BDDs.
This notion of context aligns with TLA+ contexts (see Sec. 17.3 on page 324
of the [TLA+ manual](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)).


```python
import omega.symbolic.temporal as trl

# declaration of context
aut = trl.Automaton()
aut.declare_variables(x='bool', y=(0, 5))
aut.varlist = dict(env=['x'], sys=['y'])
aut.prime_varlists()
# specification, as a stepwise implication
aut.init['env'] = ' ~ x'
aut.init['sys'] = 'y >= 2'
aut.action['env'] = " IF x THEN ~ x' ELSE x' "
aut.action['sys'] = r'''
    /\ (y < 5)
    /\ (y' > 0)
    /\ (x' => (y = y - 1))
    '''
aut.win['sys'] = aut.bdds_from('y = 3')
```


The method `declare_variables` registers both the unprimed identifiers
`x`, `y` and the primed identifiers `x'`, `y'` in the symbol table
`aut.vars` (as well as bits for representing the values designated by
the type hints using BDDs). Constants can be declared with the method
`declare_constants`.

Variables are defined in the attribute `vars`. Variables are untyped,
as in TLA+. The type hints provide guidance to the algorithms for
symbolically representing these variables using BDDs. Variables can take
integer and Boolean values, as demonstrated by the above example.

The dictionary `varlist` stores a mapping from each component name to
the variables that represent that component (as a `list`).
The method `prime_varlists` adds to `varlist` lists of primed variables,
which are useful during fixpoint computations.

Assigning a formula as value of `aut.init['env']` stores a BDD, and
similarly for the other atributes (except for `aut.win`, where we need
to do the conversion in user code). The formulas are memoized, together
with the resulting BDDs, and this relation is used to pretty print the
result, as follows:


```
>>> print(aut)

Automaton:
Variables:
 {'x': {'type': 'bool'},
 "x'": {'type': 'bool'},
 'y': {'bitnames': ['y_0', 'y_1', 'y_2'],
       'dom': (0, 5),
       'signed': False,
       'type': 'int',
       'width': 3},
 "y'": {'bitnames': ["y_0'", "y_1'", "y_2'"],
        'dom': (0, 5),
        'signed': False,
        'type': 'int',
        'width': 3}}
init[env] =  ~ x
init[sys] = y >= 2
action[env] =  IF x THEN ~ x' ELSE x'
action[sys] =
    /\ (y < 5)
    /\ (y' > 0)
    /\ (x' => (y = y - 1))

win =
{'sys': [Function (DdNode) with var index: 1, ref count: 1, int repr: 44909187]}
```


The methods `vars_of_players` and `vars_of_all_players` are convenient for
collecting variables of interest when needed. The methods `replace_with_primed`
and `replace_with_unprimed` are useful for priming and unpriming selected
variables that a BDD depends on.

By indexing formulas by player, an `Automaton` can serve also as
a multi-player game structure.


### The module `omega.symbolic.fol`


The class `omega.symbolic.temporal.Automaton` subclasses the class
`omega.symbolic.fol.Context`. This class provides a way of declaring
first-order variables, together with relevant type hints, representing
predicates as BDDs, and performing operations on them. The following
methods are useful:

- `declare` and `add_vars` for declaring (rigid) identifiers
- `support` for finding those variables that a BDD depends on
- `to_bdd` and `to_expr` for converting between BDDs and formulas (strings)
- `bdds_from` is the multi-argument counterpart of `to_bdd`
- `true` and `false` are properties that return BDDs for the Boolean constants
- `let` for substitution of variables by other variables or by values
- `forall` and `exist` for (bounded) quantification over the type hints
- `apply` for operating on BDDs (using syntax is slower but more convenient)
- `count` for finding how many assignments (relevant states) satisfy a BDD
- `pick` and `pick_iter` for enumerating satisfying assignments
- `define` for defining operators (currently nullary operators)
- `assign_from` is the integer analog of "cube" in BDD packages.

One of the most useful methods is `to_bdd`. It takes a first-order formula
and returns a BDD node:

```python
>>> u = aut.to_bdd(r"x' /\ (y = 5)")
Function (DdNode) with var index: 1, ref count: 1, int repr: 44909347
```


### Printing minimal formulas from BDDs


A BDD is a graph, sometimes with hundreds or thousands of nodes. This form
is not human-friendly. For BDDs that you create directly from expressions,
this may be irrelevant. But for BDDs that result from your
computations (not directly from expressions you give as input), being able
to understand what they represent counts.


Converting a BDD to a readable formula introduces structure and increases
information density, so it costs computation. Structuring arises due to
expressing the formula over integer-valued variables (of `fol.Context` or
`temporal.Automaton`), instead of BDD bits. Information is condensed due to
the formula being (typically) a construct smaller than the BDD itself.

`omega` solves a minimal covering problem in order to find the *minimal*
formula in disjunctive-normal form that corresponds to a given BDD.
It uses an algorithm that was originally proposed for
[two-level logic minimization](
    https://doi.org/10.1016/0167-9260(94)00007-7),
i.e., for Boolean-valued variables, but formulated for arbitrary complete
lattices. This general form is implemented for the lattice of integers in
the module `omega.symbolic.cover`. For those familiar with circuit design,
this algorithm addresses a problem similar to ESPRESSO.


How do you use this conversion from BDDs to formulas? Via the method
`fol.Context.to_expr`. There are details (care predicate, type hints, etc)
that need an understanding of minimal covering and untyped logic to
configure conveniently, but basic usage is simple:

```python
import omega.symbolic.fol as _fol

ctx = _fol.Context()
ctx.declare(x=(0, 3), y=(0, 7))
u = ctx.to_bdd(r'x \in 1..3  /\  y \in 4..6')
v = ctx.to_bdd(r'x \in 2..3 /\ y \in 2..5')
w = u | v
expr = ctx.to_expr(w)
print(expr)
```

gives the output:

```tla
 \/ (x \in 1 .. 3) /\ (y \in 4 .. 6)
 \/ (x \in 2 .. 3) /\ (y \in 2 .. 6)
```

This example demonstrates that we didn't know what formula corresponds to `w`
until calling the method `to_expr`, because the input was expressions for
`u` and `v`, not for `w`. The above example is simple, but when more
operations occur between input (here  `u, v`) and output (`w`), then being
able to read the result as a formula is more useful.


## Enumeration


A BDD represents some assignments of values to variables. Which assignments
depends on the relevant variables. Any variables that the BDD does not depend
on can be assigned arbitrary values. Enumeration is the process of creating
such satisfying assignments from a given BDD.

The module `omega.symbolic.enumeration` includes facilities for enumerating
satisfying assignments of integer and Boolean values to variables of
a `fol.Context`, from a BDD. For example:

```python
import omega.symbolic.fol as _fol

ctx = _fol.Context()
ctx.declare(x=(1, 5), y='bool')
u = ctx.to_bdd(r'x = 2  /\  ~ y')
# select a single satisfying assignment, if any
values = ctx.pick(u)
>>> values
{'x': 2, 'y': False}
```

The method `pick` returns a single assignment, or `None` if the BDD is `FALSE`.
To enumerate all satisfying assignments from those assignments allowed by the
type hints, use the method `pick_iter`:

```python
u = ctx.to_bdd(r'x < 2  /\  ~ y')
assignments = list(ctx.pick_iter(u))
>>> assignments
[{'x': 0, 'y': False}, {'x': 1, 'y': False}]
```

By default, the `pick_*` methods return assignments to all variables in the
support of a BDD (the support includes those variables that the BDD depends
on, and is returned by `ctx.support(u)`). You can reduce or increase the set
of variables that occur in all assignments, via the argument `care_vars`.
For example:

```python
u = ctx.to_bdd(r'x < 2  \/  ~ y')
assignments = list(ctx.pick_iter(u))
>>> assignments
[{'x': 0, 'y': False},
 {'x': 1, 'y': False},
 {'x': 4, 'y': False},
 {'x': 5, 'y': False},
 {'x': 2, 'y': False},
 {'x': 3, 'y': False},
 {'x': 6, 'y': False},
 {'x': 7, 'y': False},
 {'x': 0, 'y': True},
 {'x': 1, 'y': True}]

assignments = list(ctx.pick_iter(u, care_vars=['y']))
>>> assignments
[{'y': False}, {'x': 0, 'y': True}, {'x': 1, 'y': True}]
```

The first call to `pick_iter` did a full enumeration of satisfying assignments
over the records `[x: 0..7, y: BOOLEAN]` ([TLA+ records](
    https://lamport.azurewebsites.net/tla/summary.pdf))
whereas the second call exhaustively enumerated only over the type hints
of the variable `y`.

Under the hood, the picking methods call [`BDD.pick_iter`](
    https://github.com/tulip-control/dd/blob/954c7045ae4a62a50ebc2d5ee063e703cc5307a5/dd/_abc.py#L143),
and the function `omega.symbolic.enumeration._bitfields_to_int_iter`.


## Annotating graphs with formulas


In addition to writing formulas directly, sometimes it is convenient to
create a graph (an enumerated data structure with nodes and edges),
and label nodes and edges with formulas or assignments to variables.


These are enumerated graphs with node and edge labels.
A label can be a formula (as string). A formula describes a set, thus this
representation is called “semi-symbolic”.
For convenience, there are two flavors:

- `automata.Automaton`: describes a language of (in)finite trees (sequences).
  This represents an [alternating automaton](
    https://doi.org/10.1007/3-540-60915-6_6)
  with the desired acceptance condition (Buchi, Rabin, Streett, Muller, parity,
  etc.), variables as alphabet, and formulas as guards labeling edges.
  A set of `universal_nodes` marks those nodes where path quantification is
  universal.

- `automata.TransitionSystem`: describes a transition relation of a discrete
  system. Nodes can be labeled with state predicates (formulas over unprimed
  variables), and edges with [actions](
    https://doi.org/10.1145/177492.177726)
  (formulas over primed variables). Some variables can be universally
  quantified (inputs), the rest existentially (outputs). A transition system
  can be viewed as an automaton with trivial acceptance condition
  (e.g., Buchi with all nodes accepting). It can also be viewed as
  a [Kripke structure](
    https://en.wikipedia.org/wiki/Kripke_structure_%28model_checking%29),
  or -when an environment is present- as a [contracted](
    https://en.wikipedia.org/wiki/Edge_contraction) description of a bipartite
  [game graph](https://doi.org/10.1016/0168-0072(93)90036-D).

Let's create a small transition system:

```python
import omega.automata as _automata

g = _automata.TransitionSystem()
g.owner = 'env'
g.vars = dict(x='bool', y=(0, 5))
g.env_vars.add('x')

g.add_nodes_from(range(5))
g.add_edge(0, 1, formula=r"x /\ (y' = 4)")
g.add_edge(0, 0, formula=" ~ x")
g.add_edge(1, 2, formula="(y' = 3)")
g.add_edge(2, 3, formula="(y' = y - 1)")
g.add_edge(3, 4, formula="y' < y")
g.add_edge(4, 0, formula="y' = 5")
g.initial_nodes.add(0)
```

Primed identifiers refer to values of variables at the target node of an edge,
whereas unprimed ones to values at the source node. Most attributes are of
`networkx.MultiDiGraph`, with additional ones in the same spirit.
Partial assignments leave the unassigned variables free
([open world semantics](https://en.wikipedia.org/wiki/Open-world_assumption)).


### Converting annotated graphs to symbolic automata


A `TransitionSystem` can be converted to a `symbolic.Automaton` by invoking
the function `symbolic.logicizer.graph_to_logic`. The result is a description
of the same labeled graph, but entirely with formulas. An integer variable
(named as desired) is added to represent the nodes that were enumerated in
the `TransitionSystem`.

Optional:

- initial nodes can be ignored in the initial condition
- self-loops added,
- assumptions for receptivity generated.

Using the transition system `g` defined earlier:

```python
import omega.symbolic.logicizer as _lgc

aut = _lgc.graph_to_logic(g, 'nd', ignore_initial=False)
```



## Synthesizing implementations


Having written a specification as described above, we can use a synthesis
algorithm to create an implementation. If the specification is:

```tla
AssumeGuarantee(
        EnvInit, EnvNext, EnvLive
        SysInit, SysNext, SysLive) ==
    /\ SysInit
    /\ EnvInit => /\ [](Earlier(EnvNext) => SysNext)
                  /\ (EnvLive /\ []EnvNext) => SysLive

Spec == AssumeGuarantee(EnvInit, EnvNext, EnvLive,
                        SysInit, SysNext, SysLive)
```

then an implementation has the form of a state machine:

```tla
Component == Init /\ [] ImplNext
```

where the initial condition `Init` and action `ImplNext` are synthesized
to ensure that this state machine implements the specification:

```tla
THEOREM Component => Spec
```

As noted above, the complexity of synthesis depends on what kind of liveness
formulas are in `EnvLive` and `SysLive`. [GR(1) synthesis](
    https://doi.org/10.1016/j.jcss.2011.08.007)
handles conjunctions of recurrence formulas in these operators.
As an example:

```python
import omega.games.gr1 as _gr1
import omega.symbolic.temporal as trl


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

aut.plus_one = True  # strictly causal stepwise implication
aut.moore = True  # implementation reads current state; not foo'
aut.qinit = r'\E \A'  # disjoint-state throughout

fixpoint_iterates = _gr1.solve_streett_game(aut)
_gr1.make_streett_transducer(*fixpoint_iterates, aut)
```

The above example shows how to:

- instantiate an `Automaton`

- declare some variables with integer type hints
  (by calling the method `Automaton.declare_variables`)

- specify which variables represent each component
  (via the attribute `Automaton.varlist`)

- specify the initial condition, action, and liveness for each
  component (via the attributes `init, action, win` of `Automaton`),
  see also the operator `AssumeGuarantee` above.

- specify that we are using `AssumeGuarantee`
  (via the attribute `Automaton.plus_one`)

- define that the implementation's action can depend on the current state,
  but not on the next values of any environment variables, here `foo'`
  (via the attribute `Automaton.moore`)

- define that this is a disjoint-state specification, so the implementation
  picks the initial value of (visible) component variables (here `bar`)
  (via the attribute `Automaton.qinit`)

- perform the fixpoint computation of the winning collection of states
  (by calling the function `solve_streett_game`)

- construct a symbolic implementation from the fixpoint iterates
  (by calling the function `make_streett_transducer`).


### Determinism ?


Synthesis is the search problem that corresponds to the decision problem
called *realizability*. The latter is defined in the module
`spec/Realizability.tla`. From that definition, the answer should allow
unique changes of the component's state, i.e., at each state, the action
`ImplNext` should allow the component to change in only one way.

This isn't the case for the action that `gr1.make_streett_transducer` creates.
This action is less restrictive (in general), though it still ensures the
refinement `Component => Spec`. A deterministic state machine (functional)
can be created from the synthesized action by one of the techniques described
below:

- symbolic function synthesis (`omega.symbolic.functions`), or
- state machine enumeration (`omega.games.enumeration`).


### Symbolic function synthesis


A BDD implicitly represents a constraint between variables. Suppose that
the BDD `u` depends on the variables `x` and `y`. In order to compute the
value of `y` given the value of `x`, we have to "solve an equation".
Moreover, for any given value of `x`, multiple values of `y` may satisfy `u`.

Finding those values requires extra machinery, for example the availability
of a BDD package. At deployment, we usually need only one value of `y`,
and want to simplify dependencies. We can achieve this by "solving" ahead
of time, to obtain an explicit answer of how to compute `y` from `x`.

This approach is called functional synthesis, because we are constructing
a function that maps input assignments to output assignments.
Functional synthesis can be viewed as a discrete realization of the
[implicit function theorem](
    https://en.wikipedia.org/wiki/Implicit_function_theorem).

The example below shows how to use the module `omega.symbolic.functions`
to synthesize a function that maps an assignment to `x` to an assignment
to `y'`. This function is represented as a collection of BDDs, one BDD
for each bit of `y'`, namely the bits `y_0'`, `y_1'`, and `y_2'`.


```python
import omega.symbolic.functions as fcn
import omega.symbolic.temporal as trl

aut = trl.Automaton()
aut.declare_variables(x=(1, 6), y=(1, 6))
u = aut.to_bdd("y' = x")
out_bits = aut.vars["y'"]['bitnames']
outputs = fcn.make_functions(u, out_bits, aut.bdd)
print(outputs)
```


### Enumerating a state machine


An action can allow multiple steps from a specific state. This is the case
for actions that result from GR(1) synthesis, as mentioned earlier.
Such a "permissive" action can be compactly represented using a BDD.
Looking at the BDD communicates little about what the action means.

One possibility for inspecting what an action means is to enumerate the
steps that it allows, and construct with them a graph. This is what the
module `omega.games.enumeration` does, though at each state it enumerates
only one step for each environment input allowed by the assumption
(specifically by the action of the antecedent in a stepwise implication).

The example below shows how to define symbolic actions (as BDDs), and then
enumerate this representation, creating a `networkx.DiGraph`.


```python
import omega.symbolic.temporal as trl
import omega.games.enumeration as enum
import omega.symbolic.enumeration as sym_enum


# declarations
aut = trl.Automaton()
aut.declare_variables(x=(1, 6), y=(1, 6))
aut.varlist['env'] = ['x']
aut.varlist['sys'] = ['y']
aut.prime_varlists()
aut.moore = True
# specification using stepwise implication
aut.init['env'] = r'x = 1 /\ y = 2'
aut.init['sys'] = aut.true
aut.action['sys'] = r" x < 5 /\ y' = IF x = 4 THEN 1 ELSE x "
aut.action['env'] = r" x \in 1..4 /\ x' \in 1..4 "
# enumerate and plot
g = enum.action_to_steps(aut, 'env', 'sys', qinit=r'\A \A')
sym_enum._dump_graph_as_figure(g, 'foo.pdf')
```


The example below shows how to synthesize a symbolic implementation (with
an action that may allow multiple steps from each state), and then enumerate
this implementation.


```python
import omega.games.gr1 as _gr1
import omega.games.enumeration as enum
import omega.symbolic.temporal as trl
import omega.symbolic.enumeration as sym_enum


aut = trl.Automaton()
aut.declare_variables(x=(1, 3), y=(-3, 3))
aut.varlist.update(env=['x'], sys=['y'])
aut.init['env'] = r'x = 1  /\  y = 2'
aut.init['sys'] = 'TRUE'
aut.action['env'] = r'''
    /\ x \in 1..2
    /\ x' \in 1..2
    '''
aut.action['sys'] = r'''
    /\ y \in -3..3
    /\ y' = x - 3
    '''
aut.win['<>[]'] = aut.bdds_from('x = 2')
aut.win['[]<>'] = aut.bdds_from('y # -1')
aut.qinit = r'\A \A'  # should work from all states that
                     # satisfy `aut.init['env']`
aut.moore = True
aut.plus_one = True
#
# synthesize
z, yij, xijk = _gr1.solve_streett_game(aut)
_gr1.make_streett_transducer(z, yij, xijk, aut)
#
# enumerate
g = enum.action_to_steps(aut, 'env', 'impl', qinit=aut.qinit)
# plot
sym_enum._dump_graph_as_figure(g, 'foo.pdf')
```


The enumeration algorithm also attempts to reduce the total number of nodes
in the resulting graph. To do so, it prefers steps that lead from the current
node to a node that has already been enumerated, when such a step exists.


## Assembling implementations for simulation


Writing simulation code is straightforward. However, unstructured simulation
code quickly becomes unreadable. To simplify the code that users write for
simulation, `omega` includes utilities for instantiating state machines.
These utilities are available in the module `omega.steps`.

What usually makes simulation code confusing is tracking of state. There is
a tendency to treat classes as material objects, and sprinkle state among
classes that represent components of a system. This approach leads to
spaghetti code and confusion.

Separating state tracking from reasoning about changes of state yields
code structure that is easier to understand, and tidier to use.
This approach is taken in `omega.steps`, which includes classes for:

- wrapping synthesized components (both symbolic and enumerated ones)
  (classes `AutomatonStepper`, `EnumStrategyStepper`).
  All components are Moore, in that their state changes are independent
  of the next state of other components.

- assembling these components into a system (the class `Assembly`)

- storing state history "in the background", and using it at the end
  (e.g., for plotting state changes) (the class `History`).

Moreover, you can write your own components as classes that implement the
same (simple) interface. These can then be assembled together with
synthesized components. Doing so is useful for quickly mocking parts of the
system, for debugging, and for filling in simple components, with the
`Scheduler` class being such an example.

The following example demonstrates how to use these facilities:

```python
import omega.steps as simu
import foobar


# synthesize
foo_spec = foorbar.specify_component_foo()
bar_spec = foorbar.specify_component_bar()
foorbar.synthesize_some_controller(foo_spec, sys='foo', env='bar')
foorbar.synthesize_some_controller(bar_spec, sys='bar', env='foo')
# assemble
foo = simu.AutomatonStepper(foo_spec)
bar = simu.AutomatonStepper(bar_spec)
sch = simu.Scheduler(2)
asm = simu.Assembly()
asm.machines = dict(scheduler=sch, foo=foo, bar=bar)
# run, printing the state as it changes
n_steps = 15
asm.init()
for _ in range(n_steps):
    print(asm.state)
    asm.step()
print(asm.state)
# plot
# ...
```

The interface of a component class is elementary:

- a method `init` that returns the initial values of variables that
  represent the component. This method takes no arguments.

- a method `step` that returns the next values of variables that represent
  the component, and takes as argument the current state.

The class `Assembly` takes care of tracking state changes, including
hidden state. By convention, a component variable is hidden if its name
starts with an underscore (`_`). The assembly applies name-mangling to
these variables, by prepending the component's name to avoid conflicts in
the namespace shared by all components (the "global" namespace).
Other variable names remain unchanged, and are thus visible to any components
where the names of those variables are declared.


## Writing your own symbolic algorithms


You can use the class `omega.symbolic.temporal.Automaton` to write symbolic
algorithms. Useful utilities for this purpose are available in the modules
`omega.symbolic.fixpoint` and `omega.symbolic.prime`.

For example, a standard practice for catching errors in a BDD-based
algorithm is to check that intermediate results depend on the expected
variables. The simplest case is making sure that a BDD represents
a state predicate, meaning that the BDD doesn't depend on any primed
variables:

```python
import omega.symbolic.prime as prm
import omega.symbolic.temporal as trl


aut = trl.Automaton()
aut.declare_variables(x=(1, 5), y=(-2, 17))
# a state predicate depends only on unprimed identifiers
u = aut.to_bdd(r'x \in 1..3  /\  y = -2')
assert prm.is_state_predicate(u), aut.support(u)
# an action may depend on primed identifiers
u = aut.to_bdd(r"x' \in 2..4")
assert not prm.is_state_predicate(u)
```

Another example is inspecting the support of a predicate:


```python
aut.declare_constants(c=(1, 5))
u = aut.to_bdd(r"c = 3 /\ x \in 1..3 /\ x' \in 2..4 /\ y = 0")
print(u.support)  # bits
print(aut.support(u))  # integer-valued variables
print(prm.rigid_support(u, aut))  # identifiers of constants
print(prm.flexible_support(u, aut))  # identifiers of unprimed variables
print(prm.unprimed_support(u, aut))  # all unprimed identifiers
print(prm.primed_support(u, aut))  # all primed identifiers
```


## Lower-level and internal details


### Table of variables


This is a `dict` that defines variables and their type hint.
There are three flavors of tables, at different levels of abstraction:

- simple (human friendly)
- detailed (ready for bitblasting)
- bitblasted (a refinement, used for most internal operations)

The simple format is used in the attributes
`omega.automata.Automaton.vars` and `omega.automata.TransitionSystem.vars`.
The detailed format is used in the attribute
`omega.symbolic.temporal.Automaton.vars`.


#### Simple format


The simple format is a `dict` that maps each variable name (`str`) to
either `'bool'` or a `tuple` of `(min, max)`. For example,
`dict(x='bool', y=(0, 3))`.


#### Detailed and bitblasted formats


The detailed format is a `dict` that maps each variable name (as `str`) to
a `dict` with `key: value` pairs:

- `'type': 'bool' or 'modwrap' or 'saturating'`
- `'dom': tuple(min, max)` (only for integer variables)
- `'owner': 'env' or 'sys'`

and, optionally:

- `"init": initial value`


A comparison of detailed and bitblasted tables:

| `symbolic.Automaton.vars` | detailed | bitblasted |
| --- | --- | --- |
| `'type'` | `bool` or `int` | same
| `'dom'` | same | same
| `'owner'` | same | same
| `'init'` | same | same
| `'bitnames'` | - | `list` of bit names as `str`
| `'signed'` | - | `bool`
| `'width'` | - | `= len(bitnames)`


### Bitblasting


The function `logic.bitvector.bitblast` translates first-order
logic formulas to propositional logic. The table of variables is refined
from detailed to bitblasted by `logic.bitvector.bitblast_table`.
The bitblaster can also compute safety constraints, using the function
`omega.logic.bitvector.type_invariants`:

- formulas that constrain integers
  (derived from `'type'` and `'dom'`)

- initial conditions (derived from `'init'`)

For example:

```python
import omega.logic.bitvector as bv


t = dict(
    x=dict(type='bool'),
    y=dict(type='int', dom=(0, 4)))
bt = bv.bitblast_table(t)
f = r"x' /\ (y <= 5)"
s = bv.bitblast(f, bt)
```

gives:

```python
>>> import pprint
>>> pprint.pprint(bt)
{'x': {'type': 'bool'},
 'y': {'bitnames': ['y_0', 'y_1', 'y_2'],
       'dom': (0, 4),
       'signed': False,
       'type': 'int',
       'width': 3}}

>>> pprint.pprint(s)
(" & x' $ 11 ^ ^ 1 ! y_0 1 | & 1 ! y_0 & ^ 1 ! y_0 1 ^ ^ 0 ! y_1 ? 1 | & 0 ! "
 'y_1 & ^ 0 ! y_1 ? 1 ^ ^ 1 ! y_2 ? 3 | & 1 ! y_2 & ^ 1 ! y_2 ? 3 ^ ^ 0 ! 0 ? '
 '5 | & 0 ! 0 & ^ 0 ! 0 ? 5 ^ ^ 0 ! 0 ? 7 | & 0 ! 0 & ^ 0 ! 0 ? 7 ! ^ ! ^ 0 0 '
 '? 9 ')
```

The bitblaster recognizes the action operator `'` (prime symbol),
so actions are handled as first-order expressions with primed identifiers
(of flexible variables) becoming rigid variables. In other words, each
flexible variable gives rise to two rigid variables:

1. one for the unprimed value (for example `x`), and
2. another for the primed value (for example `x'`).

Besides integer and Boolean variables defined in the bitblasted symbol table,
the `bitvector.bitblast` recognizes also bits of bitfields associated with
integers in the symbol table. This allows mixing first-order formulas with
propositional formulas that have been bitblasted earlier and translated to
infix syntax.

The workflow for compiling a symbol table is shown below.

![bitblasting workflow](
  https://rawgithub.com/johnyf/binaries/main/omega/bitblasting.svg)

The functions that prime and order variables are described in the
[BDD section](#bddizing).
The resulting bitvector formulas are in [SlugsIn](
  https://github.com/VerifiableRobotics/slugs/blob/master/doc/input_formats.md#slugsin)
syntax, which uses prefix notation. Parsing and syntax are discussed in the
[parsing section](#parsing).


### BDDizing


Formulas are strings, and BDDs data structures that allow for efficient
reasoning during synthesis and model checking. BDDs can be regarded as
acyclic graphs. The module `omega.symbolic.bdd` is responsible for
converting bitblasted formulas to BDDs.

A bitblasted formula is expressed in terms of Boolean-valued variables
("bits"). Those variables represent the integer-valued or Boolean-valued
variables that are declared at the first-order level, i.e., those
variables declared in the classes `omega.symbolic.temporal.Automaton` and
`omega.symbolic.fol.Context`.

The mapping between bits and the integer-valued variables that they represent
is handled within `omega.symbolic.fol.Context`. By the time a formula has
been bitblasted, this refinement mapping has been taken into account.
Primes within formulas are also handled during bitblasting.

The appropriate bits (and primed bits, for variables) are declared in the
BDD manager (`dd.autoref.BDD` or `dd.cudd.BDD`) at the time that you call
any of the methods:

- `Automaton.declare_variables`
- `Automaton.declare_constants`
- `Context.declare`

If you want to reorder the bits declared in the BDD manager to a different
order (e.g., because you have information about a good variable order),
then call the function `reorder` of the appropriate module (`dd.autoref` or
`dd.cudd`).


### Parsing


There are several parsers and abstract syntax trees (AST) in the `omega`
package. An effort has been made to reuse the same parsers as much as
possible, and change only the backend. The main mechanism for matching one
frontend with multiple backends is by replacing the AST nodes used.
By subclassing a prototype AST, and overriding the flattening methods, any
desired backend can be created for each parser. This is further supported by
[`astutils`](https://pypi.org/project/astutils/).

Linear temporal logic (LTL) and a fragment of the raw temporal logic of
actions (TLA+) are supported. The past fragment of LTL is translated to
the future fragment using [temporal testers](
    https://doi.org/10.1007/BFb0055036)
(see `omega.logic.past.translate`).

If a formula is a conjunction of an initial predicate, safety formulas of
the form `[](...)` and recurrence formulas `[]<>(...)`, then
`omega.gr1.split_gr1` can be used to split the temporal formula into
an initial condition, an action, a conjunction of recurrence formulas, and
a disjunction of persistence formulas.
These are stored in an `omega.symbolic.temporal.Automaton` when calling the
function `omega.gr1.closed_system_to_automaton`.

The resulting automaton stores transition-level formulas (in TLA+ these are
formulas that include primes (`'`)). These formulas can be bitblasted using
the module `omega.logic.bitvector`. Bitblasting generates formulas in
propositional logic, expressed using SlugsIn syntax. The bitblasted formulas
can be:

- parsed with the class `omega.symbolic.bdd.Parser` and:
	- converted to `BDD`s using the class `omega.symbolic.bdd.BDDNodes`
	- pretty-printed in infix syntax for debugging purposes,
- fed to a synthesizer that admits input in this syntax.

![LTL -> BDD](
    https://rawgithub.com/johnyf/binaries/main/omega/ltl_to_bdd.svg)

![details of parsing during bitblasting](
    https://rawgithub.com/johnyf/binaries/main/omega/fol_to_bdd_details.svg)



## Temporal logic syntax


Integer division has C99 semantics ([6.5.5, p.82](
  http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf)).

The parser BNF is given below. The parser admits modules or expressions
as input, to make it easier to work at both levels of granularity.

```tla
-------- MODULE omega_parser_grammar -------
(* Grammar of expressions and definitions parsed by
the function `omega.logic.lexyacc.Parser.parse()`.
*)
EXTENDS
    BNFGrammars


maybe(x) ==
    | Nil
    | x


is_lexer_grammar(L) ==
    /\ L.LETTER =
        | OneOf("abcdefghijklmnopqrstuvwxyz")
        | OneOf("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
    /\ L.UNDERSCORE = tok("_")
    /\ L.NUMERAL = OneOf("0123456789")
    /\ L.NAME =
        LET
            start ==
                | L.LETTER
                | L.UNDERSCORE
            symbol ==
                | start
                | L.NUMERAL
            tail == symbol^*
        IN
            start & tail
    /\ L.NUMBER = L.NUMERAL^+
        (* integer *)


(* first-order expressions *)
is_parser_grammar(L, G) ==
    /\ \A symbol \in DOMAIN L:
        G[symbol] = L[symbol]
    /\ G.module = G.unit^+
    /\ G.unit =
        | G.variable_declaration
        | G.constant_declaration
        | G.operator_def
    /\ G.variable_declaration =
        | tok("VARIABLE") & G.names
        | tok("VARIABLES") & G.names
    /\ G.constant_declaration =
        | tok("CONSTANT") & G.names
        | tok("CONSTANTS") & G.names
    /\ G.expr =
        | G.expr & tok("*") & G.expr
        | G.expr & tok("/") & G.expr
            (* quotient of C99 integer division *)
        | G.expr & tok("%") & G.expr
            (* remainder of C99 integer division *)
        | G.expr & tok("+") & G.expr
        | G.expr & tok("-") & G.expr
        (* predicates of arithmetic *)
        | G.expr & tok("=") & G.expr
        | G.expr & tok("#") & G.expr
            (* different *)
        | G.expr & tok("!=") & G.expr
            (* different *)
        | G.expr & tok("/=") & G.expr
            (* different *)
        | G.expr & tok("<=") & G.expr
        | G.expr & tok("=<") & G.expr
            (* same meaning as `<=` *)
        | G.expr & tok(">=") & G.expr
        (* quantifiers *)
        | tok("\\A") & G.qvars & tok(":") & G.expr
            (* "forall" *)
        | tok("\\E") & G.qvars & tok(":") & G.expr
            (* "exists" *)
        (* substitution *)
        | tok("LET") & G.defs & tok("IN") & G.expr
        (* a little set theory *)
        | LET
            expr == G.expr
            in == tok("\\in")
            DOUBLE_COLON == tok("..")
            num == G.number
            range == num & DOUBLE_COLON & num
          IN
            expr & in & range
            (* in range of integers *)
        (* propositional *)
        (* TLA+ syntax *)
        | tok("~") & G.expr
        | G.expr & tok("/\\") & G.expr
        | G.expr & tok("\\/") & G.expr
        | G.expr & tok("=>") & G.expr
        | G.expr & tok("<=>") & G.expr
        (* Promela syntax *)
        | tok("!") & G.expr
        | G.expr & tok("&") & G.expr
        | G.expr & tok("&&") & G.expr
        | G.expr & tok("|") & G.expr
        | G.expr & tok("||") & G.expr
        | G.expr & tok("->") & G.expr
        | G.expr & tok("<->") & G.expr
        (* other *)
        | G.expr & tok("^") & G.expr  (* xor *)
        | tok("IF") & G.expr &
            tok("THEN") & G.expr &
            tok("ELSE") & G.expr
            (* TLA+ ternary conditional *)
        | tok("ite") & tok("(") &
                G.expr & tok(",") &
                G.expr & tok(",") &
                G.expr &
            tok(")")
            (* ternary conditional *)
        (* temporal modal *)
        | tok("X") & G.expr
            (* "next" *)
        | G.expr & tok("'")
            (* "next" *)
        | tok("[]") & G.expr
            (* "always" *)
        | tok("<>") & G.expr
            (* "eventually" *)
        | tok("-X") & G.expr
            (* weak "previous" *)
        | tok("--X") & G.expr
            (* strong "previous" *)
        | tok("-[]") & G.expr
            (* "historically" (dual of `[]`) *)
        | tok("-<>") & G.expr
            (* "once" (dual of `<>`) *)
        | G.expr & tok("U") & G.expr
            (* strong "until" *)
        | G.expr & tok("W") & G.expr
            (* weak "until" *)
        | G.expr & tok("R") & G.expr
            (* "release" *)
        | G.expr & tok("S") & G.expr
            (* "since" *)
        | G.expr & tok("T") & G.expr
            (* "trigger" *)
        (* constants / misc *)
        | tok("(") & G.expr & tok(")")
        | tok("TRUE")
        | tok("FALSE")
        | G.number
        | G.variable
        | G.string
    /\ G.defs =
        G.operator_def & maybe(G.defs)
    /\ G.operator_def =
        L.NAME & tok("==") & G.expr
            (* operator definition *)
    /\ G.qvars =
        L.NAME & maybe(tok("'")) &
            maybe(tok(",") & G.qvars)
            (* list of quantified variables *)
    /\ G.names =
        L.NAME &
            maybe(tok(",") & G.names)
            (* list of variable or constant names *)
    /\ G.variable =
        L.NAME
    /\ G.string =
        tok("\"") & L.NAME & tok("\"")
    /\ G.number =
        maybe(tok("-")) & L.NUMBER

============================================
```

The token precedence (lowest to highest) and associativity
(r = right, l = left, n = none) is:

- `:` (l)
- `<=>`, `<->` (l)
- `=>`, `->` (l)
- `^` (l)
- `\/`, `|` (l)
- `/\`, `&` (l)
- `[]`, `<>`, `-[]`, `-<>` (l)
- `U`, `W`, `R`, `S`, `T` (l)
- `=`, `#`, `/=`, `!=` (l)
- `<=`, `=<`, `>=`, `>` (l)
- `+`, `-` (l)
- `*`, `/`, `%` (l)
- `~`, `!` (r)
- `X`, `-X`, `--X` (r)
- `'`, `.` (l)

Comments start at `(*` and close at `*)`, which can appear on different lines.
One-line comments start at `\*` and extend to the end of the line.


## The deprecated class `omega.symbolic.symbolic.Automaton`


The class `omega.symbolic.symbolic.Automaton` has been deprecated in favor
of the class `omega.symbolic.temporal.Automaton`. The deprecated class
provided a less direct route from formulas to BDDs, because the user had
to first populate an `Automaton` instance, and then call the `build` method
to generate primed variables, bitblast formulas and the symbol table,
and populate auxiliary attributes. Building returned a second `Automaton`
instance, which was less practical than working with a single instance.


## Some design notes


An assignment to variables is represented as a `dict`.

At the interface with humans, a formula is represented as a string. Deeper,
formulas are converted to [binary decision diagrams (BDDs)](
    https://github.com/tulip-control/dd)
for certain operations.

There are two approaches to ensuring a data structure is well-formed: during
creation, and at check points. The latter is simple, flat, and easy to maintain.
Most classes have a method `assert_consistent` that performs these checks.
This collects all checks at one place, to override and modify when subclassing.

Synthesis specifications include assumptions about the world outside
the component, called "environment". The strings `"env"` and `"sys"` are
used to distinguish assumptions from guarantees, in the context of a single
component. When an `Automaton` represents multiple components, the names
of those components are used instead of `"env"` and `"sys"`.

The classes `omega.symbolic.temporal.Automaton` and
`omega.symbolic.symbolic.Automaton` are inspired by the design of the class
[`tulip.spec.form.GRSpec`](
    https://github.com/tulip-control/tulip-control/blob/1c1ef990cfb042ec4984c9048dcd5c3644d70949/tulip/spec/form.py#L260).


## Copying


This document is copyright 2015-2020 by California Institute of Technology.
All rights reserved. Licensed under 3-clause BSD.
