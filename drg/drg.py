from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.rings.integer import Integer
from .array3d import Array3D
from .util import checkNonneg
from .util import checkPos
from .util import factor as _factor
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
        try:
            self.c = tuple([Integer(0)] + map(integralize, c))
        except TypeError:
            raise ValueError("c sequence not integral")
        try:
            self.b = tuple(map(integralize, b) + [Integer(0)])
        except TypeError:
            raise ValueError("b sequence not integral")
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
        try:
            for i in range(self.d):
                k.append(integralize(k[-1]*self.b[i]/self.c[i+1]))
        except TypeError:
            raise ValueError("Subconstituents not integral")
        self.k = tuple(k)
        self.n = sum(self.k)
        self.p = Array3D(self.d + 1)
        for i in range(self.d + 1):
            self.p[0, i, i] = k[i]
            self.p[i, 0, i] = Integer(1)
            self.p[i, i, 0] = Integer(1)
        for i in range(self.d):
            self.p[i+1, 1, i+1] = self.a[i+1]
            self.p[i, 1, i+1] = self.b[i]
            self.p[i+1, 1, i] = self.c[i+1]
        for i in range(2, self.d + 1):
            for j in range(1, self.d + 1):
                for h in range(1, self.d):
                    try:
                        self.p[h, i, j] = integralize(_simplify(_expand(
                            ( self.c[h] * self.p[h-1, i-1, j]
                            + self.b[h] * self.p[h+1, i-1, j]
                            - self.b[i-2] * self.p[h, i-2, j]
                            + (self.a[h] - self.a[i-1]) * self.p[h, i-1, j]
                            ) / self.c[i]
                        )))
                    except TypeError:
                        raise ValueError("intersection number p[%d, %d, %d] "
                                         "is nonintegral" % (h, i, j))
                    assert checkNonneg(self.p[h, i, j]), \
                        "intersection number p[%d, %d, %d] is negative" % \
                        (h, i, j)
                try:
                    self.p[self.d, i, j] = integralize(_simplify(_expand(
                        ( self.c[self.d] * self.p[self.d-1, i-1, j]
                        - self.b[i-2] * self.p[self.d, i-2, j]
                        + (self.a[self.d] - self.a[i-1]) * self.p[self.d, i-1, j]
                        ) / self.c[i]
                    )))
                except TypeError:
                    raise ValueError("intersection number p[%d, %d, %d] "
                                     "is nonintegral" % (self.d, i, j))
                assert checkNonneg(self.p[self.d, i, j]), \
                    "intersection number p[%d, %d, %d] is negative" % \
                    (self.d, i, j)

    def __len__(self, expand = False, factor = False, simplify = False):
        """
        Return the number of vertices.
        """
        if expand:
            self.n = _expand(self.n)
        if factor:
            self.n = _factor(self.n)
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

    def aTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``a[1], a[2], ..., a[d]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.a = tuple(map(_expand, self.a))
        if factor:
            self.a = tuple(map(_factor, self.a))
        if simplify:
            self.a = tuple(map(_simplify, self.a))
        return self.a[1:]

    def bTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``b[0], b[1], ..., b[d-1]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.b = tuple(map(_expand, self.b))
        if factor:
            self.b = tuple(map(_factor, self.b))
        if simplify:
            self.b = tuple(map(_simplify, self.b))
        return self.b[:-1]

    def cTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``c[1], c[2], ..., c[d]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.c = tuple(map(_expand, self.c))
        if factor:
            self.c = tuple(map(_factor, self.c))
        if simplify:
            self.c = tuple(map(_simplify, self.c))
        return self.c[1:]

    def diameter(self):
        """
        Return the diameter of the graph.
        """
        return self.d

    def intersectionArray(self, expand = False, factor = False,
                          simplify = False):
        """
        Return the intersection array of the graph as a tuple of two tuples.
        """
        return (self.bTable(expand = expand, factor = factor,
                            simplify = simplify),
                self.cTable(expand = expand, factor = factor,
                            simplify = simplify))

    def kTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``k[0], k[1], ..., k[d]'',
        where ``d'' is the diameter of the graph.
        """
        if expand:
            self.k = tuple(map(_expand, self.k))
        if factor:
            self.k = tuple(map(_factor, self.k))
        if simplify:
            self.k = tuple(map(_simplify, self.k))
        return self.k

    def pTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of all intersection numbers.
        """
        if expand:
            self.p.map(_expand)
        if factor:
            self.p.map(_factor)
        if simplify:
            self.p.map(_simplify)
        return self.p

    order = __len__
