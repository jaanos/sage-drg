from warnings import warn
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.matrix.constructor import Matrix
from sage.rings.integer import Integer
from sage.symbolic.ring import SR
from .array3d import Array3D
from .coefflist import CoefficientList
from .util import checkNonneg
from .util import checkPos
from .util import factor as _factor
from .util import integralize
from .util import matrixMap
from .util import variables

class DRGParameters:
    """
    A class for parameters of a distance-regular graph
    and checking their feasibility.
    """

    def __init__(self, b, c):
        """
        Object constructor.

        Takes two iterables of the same length ``d`` as input,
        representing the intersection array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}``.
        The basic checks on integrality and nonnegativity
        of the intersection array are performed.
        """
        self.d = Integer(len(b))
        assert self.d == len(c), "Parameter length mismatch"
        try:
            self.c = tuple([Integer(0)] + map(integralize, c))
        except TypeError:
            raise ValueError("c sequence not integral")
        try:
            self.b = tuple(map(integralize, b) + [Integer(0)])
        except TypeError:
            raise ValueError("b sequence not integral")
        self.vars = tuple(set(sum(map(variables, b + c), ())))
        self.a = tuple(b[0]-x-y for x, y in zip(self.b, self.c))
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
        Return the table of intersection numbers ``a[1], a[2], ..., a[d]``,
        where ``d`` is the diameter of the graph.
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
        Return the table of intersection numbers ``b[0], b[1], ..., b[d-1]``,
        where ``d`` is the diameter of the graph.
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
        Return the table of intersection numbers ``c[1], c[2], ..., c[d]``,
        where ``d`` is the diameter of the graph.
        """
        if expand:
            self.c = tuple(map(_expand, self.c))
        if factor:
            self.c = tuple(map(_factor, self.c))
        if simplify:
            self.c = tuple(map(_simplify, self.c))
        return self.c[1:]

    def cosineSequences(self, index = None, ev = None, expand = False,
                        factor = False, simplify = False):
        """
        Compute and return the cosine sequences for each eigenvalue.
        """
        if "theta" not in self.__dict__:
            self.eigenvalues(expand = expand, factor = factor,
                             simplify = simplify)
        if "omega" not in self.__dict__:
            self.omega = Matrix(SR, self.d + 1)
            self.omega[:, 0] = 1
            for i in range(self.d + 1):
                self.omega[i, 1] = self.theta[i]/self.b[0]
                for j in range(2, self.d + 1):
                    self.omega[i, j] = _simplify(_factor((
                        (self.theta[i] - self.a[j-1]) * self.omega[i, j-1]
                        - self.c[j-1] * self.omega[i, j-2]) / self.b[j-1]))
        if expand:
            matrixMap(_expand, self.omega)
        if factor:
            matrixMap(_factor, self.omega)
        if simplify:
            matrixMap(_simplify, self.omega)
        if ev is not None:
            try:
                index = self.theta.index(ev)
            except ValueError as ex:
                if index is None:
                    raise ex
        if index is not None:
            return self.omega[index]
        return self.omega

    def diameter(self):
        """
        Return the diameter of the graph.
        """
        return self.d

    def eigenvalues(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the eigenvalues of the graph.
        """
        if "theta" not in self.__dict__:
            B = Matrix(SR, [M[1] for M in self.p])
            self.theta = B.eigenvalues()
            try:
                self.theta.sort(key = lambda x: CoefficientList(x, self.vars),
                                reverse = True)
            except:
                warn(Warning("Sorting of eigenvalues failed - "
                             "you may want to sort theta manually"))
            else:
                if len(self.vars) > 1:
                    warn(Warning("More than one variable is used - "
                                 "please check that the ordering is correct"))
            self.theta = tuple(self.theta)
        if expand:
            self.theta = tuple(map(_expand, self.theta))
        if factor:
            self.theta = tuple(map(_factor, self.theta))
        if simplify:
            self.theta = tuple(map(_simplify, self.theta))
        return self.theta

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
        Return the table of intersection numbers ``k[0], k[1], ..., k[d]``,
        where ``d`` is the diameter of the graph.
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

    def reorderEigenvalues(self, *order):
        """
        Specify a new order for the eigenvalues and return it.
        """
        if "theta" not in self.__dict__:
            self.eigenvalues()
        if len(order) == 1 and isinstance(order[0], (tuple, list)):
            order = order[0]
        assert len(order) == self.d, "wrong number of indices"
        order = [0] + list(order)
        assert set(order) == set(range(self.d + 1)), \
            "repeating or nonexisting indices"
        self.theta = tuple(self.theta[i] for i in order)
        if "omega" in self.__dict__:
            self.omega = Matrix(SR, [self.omega[i] for i in order])
        return self.theta

    def valency(self):
        """
        Return the valency of the graph.
        """
        return self.b[0]

    def variables(self):
        """
        Return the variables in the graph parameters.
        """
        return self.vars

    order = __len__
