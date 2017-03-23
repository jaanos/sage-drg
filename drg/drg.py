from sage.rings.integer import Integer
from .util import checkNonneg, checkPos, integralize

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
        self.c = tuple([Integer(0)] + [integralize(x) for x in c])
        self.b = tuple([integralize(x) for x in b] + [Integer(0)])
        self.a = tuple(b[0]-x-y for x, y in zip(self.b, self.c))
        assert self.d == len(c), "Parameter length mismatch"
        assert self.c[1] == 1, "Invalid c[1] value"
        assert all(checkNonneg(self.b[i] - self.b[i+1])
                   for i in range(self.d)), "b sequence not non-ascending"
        assert all(checkNonneg(self.c[i+1] - self.c[i])
                   for i in range(self.d)), "c sequence not non-descending"
        assert all(checkNonneg(x) for x in self.a), \
            "a values negative"

    def __repr__(self):
        return "Parameters of a distance-regular graph " \
               "with intersection array {%s; %s}" % \
               tuple(', '.join(str(x) for x in l)
                     for l in self.intersectionArray())

    def aTable(self):
        """
        Return the table of intersection numbers ``a[1], a[2], ..., a[d]'',
        where ``d'' is the diameter of the graph.
        """
        return self.a[1:]

    def bTable(self):
        """
        Return the table of intersection numbers ``b[0], b[1], ..., b[d-1]'',
        where ``d'' is the diameter of the graph.
        """
        return self.b[:-1]

    def cTable(self):
        """
        Return the table of intersection numbers ``c[1], c[2], ..., c[d]'',
        where ``d'' is the diameter of the graph.
        """
        return self.c[1:]

    def diameter(self):
        """
        Return the diameter of the graph.
        """
        return self.d

    def intersectionArray(self):
        """
        Return the intersection array of the graph as a tuple of two tuples.
        """
        return (self.bTable(), self.cTable())
