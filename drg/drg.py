from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.rings.integer import Integer
from .util import checkNonneg
from .util import checkPos
from .util import integralize

class DRGParameters:
    """
    A class for parameters of a distance-regular graph
    and checking their feasibility.
    """

    def __init__(self, b, c):
        """
        Object constructor.

        Takes two iterables of the same length ``d'' as input,
        representing the intersection array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}''.
        The basic checks on integrality and nonnegativity
        of the intersection array are performed.
        """
        self.d = Integer(len(b))
        self.c = tuple([Integer(0)] + map(integralize, c))
        self.b = tuple(map(integralize, b) + [Integer(0)])
        self.a = tuple(b[0]-x-y for x, y in zip(self.b, self.c))
        assert self.d == len(c), "Parameter length mismatch"
        assert self.c[1] == 1, "Invalid c[1] value"
        assert all(checkNonneg(self.b[i] - self.b[i+1])
                   for i in range(self.d)), "b sequence not non-ascending"
        assert all(checkNonneg(self.c[i+1] - self.c[i])
                   for i in range(self.d)), "c sequence not non-descending"
        assert all(checkNonneg(x) for x in self.a), \
            "a values negative"
        k = [1]
        for i in range(self.d):
            k.append(integralize(k[-1]*self.b[i]/self.c[i+1]))
        self.k = tuple(k)
        self.n = sum(self.k)

    def __len__(self, expand = False, simplify = False):
        """
        Return the number of vertices.
        """
        if expand:
            self.n = _expand(self.n)
        if simplify:
            self.n = _simplify(self.n)
        return self.n

    def __repr__(self):
        """
        String representation.
        """
        return "Parameters of a distance-regular graph " \
               "with intersection array {%s; %s}" % \
               tuple(', '.join(str(x) for x in l)
                     for l in self.intersectionArray())

    def aTable(self, expand = False, simplify = False):
        """
        Return the table of intersection numbers ``a[1], a[2], ..., a[d]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.a = tuple(map(_expand, self.a))
        if simplify:
            self.a = tuple(map(_simplify, self.a))
        return self.a[1:]

    def bTable(self, expand = False, simplify = False):
        """
        Return the table of intersection numbers ``b[0], b[1], ..., b[d-1]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.b = tuple(map(_expand, self.b))
        if simplify:
            self.b = tuple(map(_simplify, self.b))
        return self.b[:-1]

    def cTable(self, expand = False, simplify = False):
        """
        Return the table of intersection numbers ``c[1], c[2], ..., c[d]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.c = tuple(map(_expand, self.c))
        if simplify:
            self.c = tuple(map(_simplify, self.c))
        return self.c[1:]

    def diameter(self):
        """
        Return the diameter of the graph.
        """
        return self.d

    def intersectionArray(self, expand = False, simplify = False):
        """
        Return the intersection array of the graph as a tuple of two tuples.
        """
        return (self.bTable(expand = expand, simplify = simplify),
                self.cTable(expand = expand, simplify = simplify))

    def kTable(self, expand = False, simplify = False):
        """
        Return the table of intersection numbers ``k[0], k[1], ..., k[d]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.k = tuple(map(_expand, self.k))
        if simplify:
            self.k = tuple(map(_simplify, self.k))
        return self.k

    order = __len__
