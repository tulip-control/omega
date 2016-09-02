# `omega` documentation


## Design principles

At the interface with humans, a formula is represented as a string. Deeper, they are converted to [binary decision diagrams (BDDs)](https://github.com/johnyf/dd) for certain operations. An assignment to variables is represented by as a `dict`. In most places where formulae are used in data structures, an assignment can also be used, provided that the data structure is fed to a suitable algorithm. Partial assignments leave the unassigned variables free ([open world semantics](https://en.wikipedia.org/wiki/Open-world_assumption)).

In open systems, two players are involved: an environment, represented by [universally quantified](https://en.wikipedia.org/wiki/Universal_quantification) variables, and a system, represented by existentially quantified variables. These are identified by the strings `"env"` and `"sys"`, though other names work too, if you write a suitable algorithm.

There are two approaches to ensuring a data structure is well-formed: during creation, and at check points. The former leads to complex, nested, ugly, and fragile code. The latter is simple, flat, and easy to maintain. Most classes have a method `assert_consistent` that performs these checks. This collects all checks at one place, to override and modify when subclassing.

Another common method is `to_pydot`.


## Semi-symbolic automata

These are enumerated graphs with node and edge labels.
A label can be a formula (as string). A formula describes a set, thus this representation is called “semi-symbolic”.
For convenience, there are two flavors:

- `automata.Automaton`: describes a language of (in)finite trees (sequences). This represents an [alternating automaton](http://doi.org/10.1007/3-540-60915-6_6) with the desired acceptance condition (Buchi, Rabin, Streett, Muller, parity, etc.), variables as alphabet, and formulae as guards labeling edges. A set of `universal_nodes` marks those nodes where path quantification is universal.

- `automata.TransitionSystem`: describes a transition relation of a discrete system. Nodes can be labeled with state predicates (formulae over unprimed variables), and edges with [actions](http://dx.doi.org/10.1145/177492.177726) (formulae over primed variables). Some variables can be universally quantified (inputs), the rest existentially (outputs). A transition system can be viewed as an automaton with trivial acceptance condition (e.g., Buchi with all nodes accepting). It can also be viewed as a [Kripke structure](https://en.wikipedia.org/wiki/Kripke_structure_%28model_checking%29), or -when an environment is present- as a [contracted](https://en.wikipedia.org/wiki/Edge_contraction) description of a bipartite [game graph](http://dx.doi.org/10.1016/0168-0072(93)90036-D).

Lets create a small transition system:

```python
from omega import automata

g = automata.TransitionSystem()
g.owner = 'env'
g.vars = dict(x='bool', y=(0, 5))
g.env_vars.add('x')

g.add_nodes_from(xrange(5))
g.add_edge(0, 1, formula="x /\ (y' = 4)")
g.add_edge(0, 0, formula=" ~ x")
g.add_edge(1, 2, formula="(y' = 3)")
g.add_edge(2, 3, formula="(y' = y - 1")
g.add_edge(3, 4, formula="y' < y")
g.add_edge(4, 0, formula="y' = 5")
g.initial_nodes.add(0)
```

Primed identifiers refer to values of variables at the target node of an edge, whereas unprimed ones to the source node. Most attributes are of `networkx.MultiDiGraph`, with additional ones in the same spirit.

These constructs are intended for development and educational activities, or as intermediate data structures in a larger framework. For scalable human input, use [`openpromela`](https://github.com/johnyf/openpromela) or some equivalent.


## Symbolic automata

These automata are described by formulae that are represented as strings or BDDs. The user-defined attributes are:

- initial condition,
- action (= transition relation)
- winning condition.

These are inspired by [TLA](https://en.wikipedia.org/wiki/Temporal_logic_of_actions), [fair discrete systems](http://doi.org/10.1007/BFb0055036), [game structures](http://dx.doi.org/10.1016/j.jcss.2011.08.007), [automaton formulae](http://dx.doi.org/10.1007/978-3-662-10778-2), and the design of [`tulip.spec.form.GRSpec`](https://github.com/tulip-control/tulip-control/blob/1c1ef990cfb042ec4984c9048dcd5c3644d70949/tulip/spec/form.py#L260).
In addition, variables are defined in the attributed `vars`. The variables in a symbolic automaton are defined *differently* than in semi-symbolic automata, as discussed in [symbol tables section](#table-of-variables).

[First-order](https://en.wikipedia.org/wiki/First-order_logic) variables are supported (read: integers), as well as propositional variables (Booleans). The attributes of a symbolic automaton can be represented at several different levels of abstraction:

- first-order logic (unquantified)
- propositional logic
- BDD levels
- MDD levels

The following sections overview these layers, and conversions between them. Before that, lets create a small example.

```python
from omega.symbolic.symbolic import Automaton

a = Automaton()
a.vars = dict(x=dict(type='bool', owner='env'),
              y=dict(type='int', dom=(0, 5), owner='sys'))
a.init['env'].append(' ~ x')
a.init['sys'].append('y >= 2')
a.action['env'].append("ite(x, ~ x', x')")
a.action['sys'].append('y < 5')
a.action['sys'].extend(["y' > 0", "x' => (y = y - 1)"])
a.win['sys'].append('y = 3')
```

These are stored as given:

```python
>>> print(a)

Symbolic automaton:
========================================

variables:
{'x': {'owner': 'env', 'type': 'bool'},
 'y': {'dom': (0, 5), 'owner': 'sys', 'type': 'int'}}

ENV INIT
!x

ENV ACTION
ite(x, !x', x')

SYS INIT
y >= 2

SYS ACTION
y < 5
y' > 0
x' => (y = y - 1)

SYS WIN
y = 3
```

Humans are not intended to define variables in this way, because it is cumbersome. Instead, [convert](#Converting-labeled-graphs-to-symbolic-automata) a semi-symbolic automaton, or use `bitvector.make_table`.

By indexing formulae by player, an `Automaton` can serve also as a multi-player game structure.


### Build

A symbolic automaton provides a “context” for symbolic computation, in the sense of a [symbol table](https://en.wikipedia.org/wiki/Symbol_table), together with a translator from first-order formulae (user friendly) to BDDs. This establishes a more direct route between a human and the symbolic representation.

Use the method `Automaton.build` to generated primed variables, a variable order, initialize `Automaton.bdd`, bitblast the formulae attributes, and populate the convenience attributes (detailed in `symbolic.Automaton.__doc__`).
Using the earlier example:

```python
>>> aut = a.build()
>>> print(aut)

Symbolic automaton:
========================================

variables:
{'x': {'owner': 'env', 'type': 'bool'},
 'y': {'bitnames': ['y_0', 'y_1', 'y_2'],
       'dom': (0, 5),
       'owner': 'sys',
       'signed': False,
       'type': 'int',
       'width': 3}}

ENV INIT
-2

ENV ACTION
-6

SYS INIT
12

SYS ACTION
-36

SYS WIN
-37
```

These integers are (negated) BDD nodes in `Automaton.bdd`.
Notice that the same data structure is re-used with different formulae representation (strings vs BDDs).

One of the most useful methods is `add_expr`. It takes a first-order formula and returns a BDD node:

```python
>>> u = aut.add_expr("x' /\ (y = 5)")
-42
```

Each of the below attributes is a `set` with elements of the type shown in the table. Similar attributes with other combinations are available for convenience. For example, `uevars` contains both universally and existentially quantified variables. More details can be found in `symbolic.Automaton.__doc__`.

| attribute | uvars | evars | upvars | epvars |
| ---       | ---   | ---   | ---    | ---    |
| priming   | unprimed | unprimed | primed | primed |
| quantification | universal | existential | universal | existential |
| FOL       | str   | str   | str    | str    |
| bits      | str   | str   | str    | str    |
| B/MDD levels | int  | int   | int    | int    |

These attributes are populated automatically, by compiling the symbolic automaton. After calling `Automaton.build`, the attributes will contain BDD levels as integers. This representation is the most convenient for implementing symbolic algorithms with little overhead. It is occassionally useful to convert to the other representations (FOL, bit names), which is why they are noted in the table.


### Converting labeled graphs to symbolic automata

A `TransitionSystem` can be converted to a `symbolic.Automaton` by invoking the function `symbolic.logicizer.graph_to_logic`. The result is a description of the same labeled graph, but entirely with formulae. An integer variable (named as desired) is added to represent the nodes that were enumerated in the `TransitionSystem`.

Optional:

- initial nodes can be ignored in the initial condition
- self-loops added,
- assumptions for receptivity generated.

Using the transition system `g` defined earlier:

```python
from omega.symbolic import logicizer

aut = logicizer.graph_to_logic(g, 'nd', ignore_initial=False)
```


## Table of variables

This is a `dict` that defines variables, their type, initial value, owner (`"env"` or `"sys"`) and initial value (optional). There are three flavors of tables, at different levels of abstraction:

- simple (human friendly)
- detailed (ready for bitblasting)
- bitblasted (a refinement, used for most internal operations)

The simple format is used in `automata.Automaton.vars`, `automata.TransitionSystem.vars`. The detailed is used in `symbolic.Automaton.vars` for initializing it, and the bitblasted results by a call to `Automaton.build`.


### Simple format

The simple format is a `dict` that maps each variable name (as `str`) to either `'bool'` or a `tuple` of `(min, max)`. For example, `dict(x='bool', y=(0, 3))`.


### Detailed and bitblasted formats

The detailed format is a `dict` that maps each variable name (as `str`) to a `dict` with `key: value` pairs:

- `'type': 'bool' or 'modwrap' or 'saturating'`
- `'dom': tuple(min, max)` (only for integer variables)
- `'owner': 'env' or 'sys'`

and optionally:

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


## Bitblasting

The function `logic.bitvector.bitblast` translates (unquantified) first-order logic (FOL) formulae to bitvector logic. The table of variables is refined from detailed to bitblasted by `logic.bitvector.bitblast_table`. The bitblaster returns also some safety constraints:

- formulae that constrain saturating integers (derived from `'type'` and `'dom'`)
- initial conditions (derived from `'init'`)

For example:

```python
from omega.logic import bitvector as bv

t = dict(
    x=dict(type='bool', owner='env', init='True'),
    y=dict(type='saturating', dom=(0, 4), owner='sys', init=2)
bt, init, safe = bv.bitblast_table(t)
f = "x' /\ (y <= 5)"
s = bv.bitblast(s, bt)
```

gives:

```python
>>> print(bt)
{'x': {'owner': 'env', 'type': 'bool'},
 'y': {'bitnames': ['y_0', 'y_1', 'y_2'],
       'dom': (0, 4),
       'owner': 'sys',
       'signed': False,
       'type': 'int',
       'width': 3}}

>>> print(init)
{'sys': ['y = 2'], 'env': ['x = True']}

>>> print(safe)
{'sys': ['(0 <= y) /\ (y <= 4)'], 'env': []}

>>> print(s)
& x' $ 11 ^ ^ 1 ! y_0 1 | & 1 ! y_0 & ^ 1 ! y_0 1 ^ ^ 0 ! y_1 ? 1 | & 0 ! y_1 & ^ 0 ! y_1 ? 1 ^ ^ 1 ! y_2 ? 3 | & 1 ! y_2 & ^ 1 ! y_2 ? 3 ^ ^ 0 ! 0 ? 5 | & 0 ! 0 & ^ 0 ! 0 ? 5 ^ ^ 0 ! 0 ? 7 | & 0 ! 0 & ^ 0 ! 0 ? 7 ! ^ ! ^ 0 0 ? 9
```

Note that the only temporal operator recognized by the bitblaster is “next”. In propositional logic, “next” is represented by variable priming. Thus, it becomes part of a variable's name, which yields the “primed copies” of variables.

Besides integer and Boolean variables defined in the bitblasted symbol table, the `bitvector.bitblast` recognizes also bits of bitfields associated with integers in the symbol table. This allows mixing first-order formulae with propositional formulae that either:

- are obtained by calling `BDD.to_expr`, to represent the result of some BDD operation (e.g., quantification can conveniently be performed with BDDs)
- have been bitblasted earlier and flattened to infix syntax.

The workflow for compiling a symbol table is shown below.

![bitblasting workflow](https://rawgithub.com/johnyf/binaries/master/omega/bitblasting.svg)

The functions that prime and order variables are described in the [BDD section](#BDDizing).
The resulting bitvector formulae are in [SlugsIn](https://github.com/LTLMoP/slugs/blob/master/doc/input_formats.md#slugsin) syntax, which uses prefix notation. Parsing and syntax is discussed in the [parsing section](#Parsing).


## BDDizing

The typical operations involved in creating a BDD for a dynamical system are:

- list bits
- map each integer to a bitfield
- prime
- order

In order to interleave primed with unprimed variables in the ordering of BDD levels, priming and ordering are typically performed together. In `symbolic.symbolic`, there are three functions for this purpose:

- `_prime_and_order_table`: given a bitblasted table of unprimed FOL variables, return a table that contains ordered primed and unprimed FOL variables. Primed integers are associated with lists of primed BDD bits. The order is defined by a key called `"level"` in each variable's `dict`. The resulting table is used, for example, by `dd.mdd.bdd_to_mdd`.

- `_pick_var_order`: given an iterable of bits, return a list in [natural order](https://github.com/SethMMorton/natsort).

- `_partition_vars`: given `list` of ordered bits, return `dict` of BDD levels, and auto-generated attributes of `Automaton` (`uevars`, `prime`, `unprime`, etc.).

A BDD can later be converted to an MDD, which is similar, but defined over integer instead of Boolean variables.

Aspects involved in BDD initialization:

- time (variable priming)
- variable quantification (owner)
- abstraction layer (bit/int/level (B/MDD))

Instead of creating a new `BDD`, the method `Automaton.build` can also take an existing one. This is useful for using a BDD loaded from a CUDD `dddmp` file.


## Parsing

There are several parsers and abstract syntax trees (AST) in the `omega` package. An effort has been made to reuse the same parser frontends as much as possible, and change only the backend. The main mechanism for matching one frontend with multiple backends is by replacing the AST nodes used. By subclassing a prototype AST, and overriding the flattening methods, any desired backend can be created for each parser. This is further supported by [`astutils`](https://pypi.python.org/pypi/astutils).

Both future and past quantifier-free first-order linear temporal logic (QfFOLTL) is supported. The past fragment is translated to the future fragment using [temporal testers](http://doi.org/10.1007/BFb0055036) in `logic.past.translate`.

If the result belongs syntactically to the [GR(1) fragment](http://dx.doi.org/10.1007/11609773_24), then `gr1.ltl_to_automaton` can be used to split the temporal formula into an initial condition, an action, and a weak fairness formulae. These are stored in a `symbolic.Automaton`.

The only temporal operator in the resulting formulae is “next”. Using the `bitvector` module, these can be bitblasted, producing propositional logic (PL) formulae in SlugsIn syntax. These can be:

- parsed with the `symbolic.bdd.Parser` and:
	- converted to `BDD`s with `bdd.BDDNodes`
	- pretty-printed in infix for debugging purposes,
- fed to a synthesizer that admits input in this syntax, for example [`slugs`](https://github.com/LTLMoP/slugs).

![LTL -> BDD](https://rawgithub.com/johnyf/binaries/master/omega/ltl_to_bdd.svg)

![details of parsing during bitblasting](https://rawgithub.com/johnyf/binaries/master/omega/fol_to_bdd_details.svg)

## Temporal logic syntax

Integer division has C99 semantics ([6.5.5, p.82](http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf)).

```
       # first-order
expr ::= expr '*' expr
       | expr '/' expr  # quotient of C99 integer division
       | expr '%' expr  # remainder of C99 integer division
       | expr '+' expr
       | expr '-' expr

       | expr '=' expr
       | expr '!=' expr
       | expr '<=' expr
       | expr '>=' expr

       # quantifiers
       | '\A' list `:` expr  # forall
       | '\E' list `:` expr  # exists

       # propositional

       # TLA+ syntax
       | '~' expr
       | expr '/\' expr
       | expr '\/' expr
       | expr '=>' expr
       | expr '<=>' expr

       # Promela syntax
       | '!' expr
       | expr '&' expr | expr '&&' expr
       | expr '|' expr | expr '||' expr
       | expr '->' expr
       | expr '<->' expr

       # other
       | expr '^' expr  # xor
       | 'ite' '(' expr ',' expr ',' expr ')'  # ternary conditional

       # temporal modal
       | 'X' expr  # next
       | expr "'"  # next
       | '[]' expr  # always
       | '<>' expr  # eventually
       | '-X' expr  # weak previous
       | '--X' expr  # strong previous
       | expr '.' [NUMBER]  # previous [multiple]
       | '-[]' expr  # historically (dual of [])
       | '-<>' expr  # once (dual of <>)
       | expr 'U' expr  # strong until
       | expr 'W' expr  # weak until
       | expr 'R' expr  # release
       | expr 'S' expr  # since
       | expr 'T' expr  # trigger

       # constants / misc
       | '(' expr ')'
       | 'True'
       | 'False'
       | [-] NUMBER
       | variable
       | string

list ::= NAME ["'"] [',' list]  # list of variables
variable ::= NAME
string ::= '"' NAME '"'

NAME ::= [A-Za-z_][A-za-z0-9_:]*
NUMBER ::= \d+  # integer
```

The token precedence (lowest to highest) and associativity (r = right, l = left, n = none) is:

- `:` (l)
- `<=>`, `<->` (l)
- `=>`, `->` (l)
- `^` (l)
- `\/`, `|` (l)
- `/\`, `&` (l)
- `[]`, `<>`, `-[]`, `-<>` (l)
- `U`, `W`, `R`, `S`, `T` (l)
- `=`, `!=` (l)
- `<=`, `>=`, `>` (l)
- `+`, `-` (l)
- `*`, `/`, `%` (l)
- `~`, `!` (r)
- `X`, `-X`, `--X` (r)
- `'`, `.` (l)
