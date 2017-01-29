"""Syntactic manipulation of trees."""
# Copyright 2014 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import copy
import os
import networkx as nx


class Tree(nx.MultiDiGraph):
    """Abstract syntax tree as a graph data structure.

    Use this as a scaffold for syntactic manipulation.
    It makes traversals and graph rewriting easier,
    so it is preferred to working directly with the
    recursive AST classes.

    The attribute `self.root` is the tree's root node.
    """

    def __init__(self):
        self.root = None
        super(Tree, self).__init__()

    def __repr__(self):
        return repr(self.root)

    def __str__(self):
        # need to override networkx.DiGraph.__str__
        return ('Abstract syntax tree as graph with edges:\n' +
                str([(str(u), str(v))
                    for u, v, k in self.edges_iter(keys=True)]))

    @property
    def variables(self):
        """Return the set of variables in tree."""
        return {u for u in self if u.type == 'var'}

    @classmethod
    def from_recursive_ast(cls, u):
        tree = cls()
        tree.root = u
        tree._recurse(u)
        return tree

    def _recurse(self, u):
        if hasattr(u, 'value'):
            # necessary this terminal is the root
            self.add_node(u)
        elif hasattr(u, 'operator'):
            for i, v in enumerate(u.operands):
                self.add_edge(u, v, key=i)
                self._recurse(v)
        else:
            raise Exception('unknown node type: {u}'.format(u=u))
        return u

    def to_recursive_ast(self, u=None):
        if u is None:
            u = self.root
        w = copy.copy(u)
        if not self.succ.get(u):
            assert hasattr(u, 'value')
        else:
            w.operands = [self.to_recursive_ast(v)
                          for _, v, _ in sorted(
                              self.edges_iter(u, keys=True),
                              key=lambda x: x[2])]
            assert len(u.operands) == len(w.operands)
        return w

    def add_subtree(self, leaf, tree):
        """Add the `tree` at the node `leaf`.

        AST nodes are not copied.
        """
        assert not self.succ.get(leaf)
        for u, v, k in tree.edges_iter(keys=True):
            self.add_edge(u, v, key=k)
        # replace old leaf with subtree root
        ine = self.in_edges(leaf, keys=True)
        if ine:
            assert len(ine) == 1
            ((parent, _, k), ) = ine
            self.add_edge(parent, tree.root, key=k)
        else:
            self.root = tree.root
        self.remove_node(leaf)

    def to_pydot(self, detailed=False):
        """Create GraphViz dot string from given AST."""
        g = ast_to_labeled_graph(self, detailed)
        return nx.drawing.nx_pydot.to_pydot(g)

    def write(self, filename, detailed=False):
        """Layout AST and save result in PDF file."""
        fname, fext = os.path.splitext(filename)
        fext = fext[1:]  # drop .
        p = self.to_pydot(detailed)
        p.set_ordering('out')
        p.write(filename, format=fext)


def ast_to_labeled_graph(tree, detailed):
    """Convert AST to `nextworkx.DiGraph` for graphics."""
    g = nx.DiGraph()
    for u in tree:
        if hasattr(u, 'operator'):
            label = u.operator
        elif hasattr(u, 'value'):
            label = u.value
        else:
            raise TypeError(
                'AST node must be an operator or terminal, '
                'got instead: {u}'.format(u=u) +
                ', of type: {t}'.format(t=type(u)))
        # show both repr and AST node class in each vertex
        if detailed:
            label += '\n' + str(type(u).__name__)
        g.add_node(id(u), label=label)
    for u, v, k in tree.edges_iter(keys=True):
        g.add_edge(id(u), id(v), label=k)
    return g
