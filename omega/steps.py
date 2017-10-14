"""A module for constructing behaviors of assembled state machines."""
# Copyright 2017 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
from omega.games import enumeration as enum
from omega.logic import syntax as stx
from omega.symbolic import prime as prm


class History(object):
    """Record current and past values of variables.

    To initialize:

    ```python
    h = History(initial_state)
    ```

    or:

    ```python
    h.state = initial_state
    ```
    """

    def __init__(self):
        self.vars = dict()  # type hints
        self.state = dict()  # identifiers -> values
        # finite behavior
        self.past = list()  # list of earlier states

    def update(self, state):
        """Set `self.state` to `state`, update `self.past`.

        If you want to change the current state without
        appending the old state to `self.past`, then
        modify the attribute `self.state`.
        """
        self.past.append(self.state)
        self.state = state


class Assembly(History):
    """Register and step state machines.

    The assembly that results from these components should
    be a complete-system (aka closed-system, cf. Lamport).
    """

    def __init__(self):
        self.machines = dict()
        super(Assembly, self).__init__()
        self.state = None  # to call `init` first

    def init(self):
        """Return an initial state."""
        self.state = dict()
        for name, stm in self.machines.items():
            partial_state = self._init(stm, name)
            self._update_state(self.state, partial_state)

    def _init(self, machine, name):
        """Return partial state from `machine`.

        @param name: used to mangle hidden var names
        """
        partial = machine.init()
        return self._to_global_state(partial, name)

    def step(self):
        """Take a step and return the next state."""
        assert self.state is not None, 'first call method `init`'
        next_state = dict()
        for name, stm in self.machines.items():
            partial_state = self._step(stm, self.state, name)
            self._update_state(next_state, partial_state)
        # record history
        self.update(next_state)

    def _step(self, machine, state, name):
        """Return partial state update from `machine`.

        @param name: used to unmangle and mangle hidden
            var names
        """
        local = self._to_local_state(state, name, machine)
        partial = machine.step(local)
        return self._to_global_state(partial, name)

    def _to_local_state(self, global_state, name, machine):
        unmangled = omit_prefix(global_state, name)
        # ignore variables undeclared in `machine`
        local = {k: v for k, v in unmangled.items()
                 if k in machine.vars}
        return local

    def _to_global_state(self, local_state, name):
        vis = visible_vars(local_state)
        hid = hidden_vars(local_state)
        glob_hid = add_prefix(hid, name)
        _assert_disjoint(vis, glob_hid)
        vis.update(glob_hid)
        return vis

    def _update_state(self, state, partial):
        _assert_disjoint(partial, state)
        state.update(partial)


class AutomatonStepper(object):
    """Initialize and step a symbolic `Automaton`."""

    def __init__(self, aut):
        self.vars = aut.vars
        self.aut = aut
        self._init = aut.init['impl']
        self._action = aut.action['impl']

    def init(self):
        """Return initial values of variables for this component."""
        r = self.aut.pick(self._init)
        return {k: v for k, v in r.items() if k in self.aut.varlist['impl']}

    def step(self, state):
        """Return next values of variables or `None`.

        @param state: `dict` that maps identifiers to values.

            If any unprimed identifiers in `support(action)` are
            missing from `state`, raise `ValueError`.

            If `action` is not enabled at `state`,
            then raise `ValueError`.

            For an `action` that depends on primed variables
            (Mealy machine), the `state` should include those.
        """
        action = self._action
        self._assert_support_assigned(action, state)
        u = self.aut.let(state, action)
        vrs = self.aut.support(u).union(self.aut.varlist["impl'"])
        primed_state = self.aut.pick(u, vrs)
        self._assert_unblocked(primed_state)
        return _unprime_state(primed_state)

    def _assert_support_assigned(self, action, state):
        unprimed = prm.unprimed_support(action, self.aut)
        missing = unprimed.difference(state)
        assert not missing, (missing, state)

    def _assert_unblocked(self, state):
        if state is None:
            raise ValueError((
                'action is not enabled '
                'at state: {state}').format(
                    state=state))


class EnumStrategyStepper(object):
    """Initialize and step an enumerated strategy."""

    def __init__(self, graph):
        assert graph.initial_nodes
        # self.vars = graph.vars
        self.graph = graph

    def init(self):
        """Return initial values for variables this component controls."""
        return self._pick_sys(self.graph.initial_nodes)

    def step(self, state):
        """Return next values for variables this component controls."""
        u = next(u for u in self.graph if self.graph.nodes[u] == state)
        return self._pick_sys(self.graph.successors(u))

    def _pick_sys(self, nodes):
        u = next(iter(nodes))
        d = self.graph.nodes[u]
        # TODO: consider defining `varlist` instead of
        # `inputs` and `outputs`
        return slice_dict(d, self.graph.outputs)


class Component(object):
    """Behave as a Moore state machine.

    When given "inputs", it updates its state
    by joining the given inputs to the "outputs" that
    it computes from the old state.

    Calling `step` you get the outputs from the current
    state, without changing the state. When using several
    `Component` instances, you should get their outputs
    by calling `step`, then feed them back as inputs by
    calling `update`.
    """

    def __init__(self, machine):
        self.machine = machine
        self.state = None  # `dict()` later

    def init(self):
        """Return initial values for variables that the component controls.

        Use this to get inputs to other machines that result
        after the first step of a behavior.
        """
        return self.machine.init()

    def step(self):
        """Return next values for variables component controls.

        Use this to get inputs to feed to other machines,
        from the second step onwards.
        """
        assert self.state is not None, 'first call method `update`'
        return self.machine.step(self.state)

    def update(self, inputs):
        """Update `self.state` based on `inputs` and current state.

        First call `init` from other machines,
        then feed the results to `update` here.
        Then repeatedly call `step` and `update`.
        """
        _inputs = set(self.machine.graph.inputs)
        assert set(inputs) == _inputs, (inputs, _inputs)
        # uninitialized yet ?
        if self.state is None:
            outputs = self.init()
        else:
            outputs = self.step()
        state = dict(inputs)
        state.update(outputs)
        self.state = state


class Scheduler(object):
    """A non-interleaving binary clock.

    Each step increments the variable "turn".
    For example:

    ```python
    sch = Scheduler(3)
    state_1 = dict(turn=1)

    state_2 = sch.step(state_1)
    >>> state_2
    {'turn': 2}

    state_3 = sch.step(state_2)
    >>> state_3
    {'turn': 0}
    ```
    """

    def __init__(self, n):
        dom = (0, n - 1)
        turn_type = dict(type='int', dom=dom)
        self.vars = dict(turn=turn_type)
        self._n = n

    def init(self):
        """Return initial values for the component's variable."""
        return dict(turn=0)

    def step(self, state):
        """Return assignment to variable "turn"."""
        next_turn = (state['turn'] + 1) % self._n
        return dict(turn=next_turn)


def visible_vars(vrs):
    """Slice dictionary `vrs`, omitting keys matching `_*`.

    @type vrs: `dict`
    @rtype: `dict`
    """
    return {k: v for k, v in vrs.items()
            if not k.startswith('_')}


def hidden_vars(vrs):
    """Slice dictionary `vrs`, keeping keys matching `_*`."""
    return {k: v for k, v in vrs.items()
            if k.startswith('_')}


def add_prefix(vrs, prefix):
    """Prepend `prefix` to hidden variables in `vrs`.

    @type vrs: `dict`
    @type prefix: `str`
    """
    d = dict()
    for k, v in vrs.items():
        if k.startswith('_'):
            name = prefix + k
            assert name not in d, (name, d)
        else:
            name = k
        d[name] = v
    return d


def omit_prefix(vrs, prefix):
    """Omit `prefix` from hidden variables in `vrs`.

    @type vrs: `dict`
    @type prefix: `str`
    """
    d = dict()
    for k, v in vrs.items():
        t = _omit_prefix(k, prefix)
        assert t not in d, (t, d)
        d[t] = v
    return d


def _omit_prefix(s, prefix):
    if s.startswith(prefix):
        return s.replace(prefix, '', 1)
    return s


def _unprime_state(primed_state):
    """Return same state but with identifiers unprimed."""
    return {stx.unprime(k): v for k, v in primed_state.items()}


def slice_dict(d, keys):
    """Return restriction of `d` to `keys`.

    @type d: `dict`
    @type keys: `set`
    """
    return {k: v for k, v in d.items()
            if k in keys}


def _assert_disjoint(a, b):
    """Raise `AssertionError` if common `dict` keys."""
    overlap = a.keys() & b.keys()
    assert not overlap, (overlap, a, b)


def enumerate_impl(spec):
    """Return enumerated controller."""
    # modifies env, sys (which serve as a reusable interface)
    spec.init['sys'] = spec.init['impl']
    spec.action['sys'] = spec.action['impl']
    graph = enum.action_to_steps(spec, qinit=spec.qinit)
    graph.inputs = spec.varlist['env']
    graph.outputs = spec.varlist['sys']
    # pprint.pprint(graph.nodes(data=True))
    return graph
