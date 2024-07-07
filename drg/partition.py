from sage.graphs.graph import Graph
from sage.rings.integer import Integer


class Bubble:
    """
    An object representing a set of vertices in a partition of the graph.
    """

    def __init__(self, v, i, j=None):
        """
        Object constructor.

        Takes a number denoting the size of the set,
        and one or two numbers denoting the distance(s)
        from the initial set(s).
        """
        self.v = v
        self.i = i
        self.j = j

    def __repr__(self):
        """
        Object representation.
        """
        if self.j is None:
            return 'Set of %d elements at distance %d' % (self.v, self.i)
        else:
            return 'Set of %d elements at distances (%d, %d)' % \
                (self.v, self.i, self.j)

    def __str__(self):
        """
        String representation of the set.
        """
        if self.v == 1:
            return ''
        else:
            return '%d' % self.v

    def is_adjacent(self, other):
        """
        Tell whether two sets are adjacent in the diagram.
        """
        return abs(self.i - other.i) <= 1 and \
            (self.j is other.j or abs(self.j - other.j) <= 1)


class PartitionGraph(Graph):
    """
    A diagram representing a partition of a distance-regular graph.
    """

    def __init__(self, p, h=0):
        """
        Object constructor.

        Takes a graph parameters object
        and an integer denoting the distance between the initial vertices.
        """
        assert h >= 0 and h <= p._.d, "distance not in feasible range"
        d = dict(sum([[((i, j), x) for j, x in enumerate(r) if x != 0]
                      for i, r in enumerate(p._.p[h])], []))
        if h == 0:
            def pos(t):
                return t[:1]
        else:
            def pos(t):
                return t
        b = {k: Bubble(v, *pos(k)) for k, v in d.items()}
        V = b.values()
        Graph.__init__(self,
                       [V, lambda u, v: p.has_edges(h, u.i, u.j, v.i, v.j)],
                       loops=False, name=p._format_parameterArray())
        self._pos = {v: (v.i, Integer(0)) if v.j is None
                     else (v.j+v.i, v.j-v.i)
                     for v in V}
        self._distance = h

    def _repr_(self):
        """
        String representation.
        """
        out = "distance partition of %s" % self.name()
        if self._distance > 0:
            out = "%d-%s" % (self._distance, out)
        else:
            out = out.capitalize()
        return out

    def graphplot(self, **options):
        """
        Return a GraphPlot object.
        """
        if 'vertex_size' not in options:
            options['vertex_size'] = Integer(500)
        return Graph.graphplot(self, **options)
