from warnings import warn
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import identity_matrix
from sage.rings.integer import Integer
from sage.symbolic.ring import SR
from .array3d import Array3D
from .coefflist import CoefficientList
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
from .util import matrixMap
from .util import rewriteExp
from .util import rewriteMatrix
from .util import rewriteTuple
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
        assert self.d == len(c), "parameter length mismatch"
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
            raise ValueError("subconstituents not integral")
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
        self.n = rewriteExp(self.n, expand = expand, factor = factor,
                            simplify = simplify)
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
        self.a = rewriteTuple(self.a, expand = expand, factor = factor,
                              simplify = simplify)
        return self.a[1:]

    def bTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``b[0], b[1], ..., b[d-1]``,
        where ``d`` is the diameter of the graph.
        """
        self.b = rewriteTuple(self.b, expand = expand, factor = factor,
                              simplify = simplify)
        return self.b[:-1]

    def cTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``c[1], c[2], ..., c[d]``,
        where ``d`` is the diameter of the graph.
        """
        self.c = rewriteTuple(self.c, expand = expand, factor = factor,
                              simplify = simplify)
        return self.c[1:]

    def check_absoluteBound(self):
        """
        Check whether the absolute bound is not exceeded.
        """
        if "q" not in self.__dict__:
            self.kreinParameters()
        for i in range(self.d + 1):
            if sum(self.m[h] for h in range(self.d + 1)
                   if self.q[h, i, i] != 0) > self.m[i]*(self.m[i] + 1)/2:
                raise ValueError("absolute bound exceeded "
                                 "for (%d, %d)" % (i, i))
            for j in range(i+1, self.d + 1):
                if sum(self.m[h] for h in range(self.d + 1)
                       if self.q[h, i, j] != 0) > self.m[i]*self.m[j]:
                    raise ValueError("absolute bound exceeded "
                                     "for (%d, %d)" % (i, j))

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
        rewriteMatrix(self.omega, expand = expand, factor = factor,
                      simplify = simplify)
        if ev is not None:
            try:
                index = self.theta.index(ev)
            except ValueError as ex:
                if index is None:
                    raise ex
        if index is not None:
            return self.omega[index]
        return Matrix(SR, self.omega)

    def diameter(self):
        """
        Return the diameter of the graph.
        """
        return self.d

    def dualEigenmatrix(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the dual eigenmatrix of the graph.
        """
        if "m" not in self.__dict__:
            self.multiplicities(expand = expand, factor = factor,
                                simplify = simplify)
        if "Q" not in self.__dict__:
            self.Q = Matrix(SR, [[self.omega[j, i] * self.m[j]
                                  for j in range(self.d + 1)]
                                 for i in range(self.d + 1)])
            if "P" in self.__dict__ and _simplify(_expand(self.P * self.Q)) \
                        != self.order(expand = True, simplify = True) \
                            * identity_matrix(SR, self.d + 1):
                    warn(Warning("the eigenmatrices do not multiply "
                                 "into a multiple of the identity matrix"))
        rewriteMatrix(self.Q, expand = expand, factor = factor,
                      simplify = simplify)
        return Matrix(SR, self.Q)

    def eigenmatrix(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the eigenmatrix of the graph.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        if "P" not in self.__dict__:
            self.P = Matrix(SR, [[self.omega[i, j] * self.k[j]
                                  for j in range(self.d + 1)]
                                 for i in range(self.d + 1)])
            if "Q" in self.__dict__ and _simplify(_expand(self.P * self.Q)) \
                        != self.order(expand = True, simplify = True) \
                            * identity_matrix(SR, self.d + 1):
                    warn(Warning("the eigenmatrices do not multiply "
                                 "into a multiple of the identity matrix"))
        rewriteMatrix(self.P, expand = expand, factor = factor,
                      simplify = simplify)
        return Matrix(SR, self.P)

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
        self.theta = rewriteTuple(self.theta, expand = expand, factor = factor,
                                  simplify = simplify)
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

    def is_formallySelfDual(self):
        """
        Check whether the graph is formally self-dual.
        """
        if "fsd" not in self.__dict__:
            self.fsd = (self.eigenmatrix(simplify = 2)
                        - self.dualEigenmatrix(simplify = 2)).is_zero()
        return self.fsd

    def kTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``k[0], k[1], ..., k[d]``,
        where ``d`` is the diameter of the graph.
        """
        self.k = rewriteTuple(self.k, expand = expand, factor = factor,
                              simplify = simplify)
        return self.k

    def kreinParameters(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the Krein parameters.
        """
        if "m" not in self.__dict__:
            self.multiplicities(expand = expand, factor = factor,
                                simplify = simplify)
        if "q" not in self.__dict__:
            q = Array3D(self.d + 1)
            for h in range(self.d + 1):
                for i in range(self.d + 1):
                    for j in range(self.d + 1):
                        q[h, i, j] = full_simplify(
                                            sum(self.k[t] * self.omega[h, t]
                                                          * self.omega[i, t]
                                                          * self.omega[j, t]
                                                for t in range(self.d + 1))
                                            * self.m[i] * self.m[j] / self.n)
                        if not checkNonneg(q[h, i, j]):
                            raise ValueError("Krein parameter q[%d, %d, %d] "
                                             "negative" % (h, i, j))
            self.q = q
        self.q.rewrite(expand = expand, factor = factor, simplify = simplify)
        return self.q

    def multiplicities(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the multiplicities of the eigenvalues.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        if "m" not in self.__dict__:
            try:
                self.m = tuple(integralize(_simplify(_factor(
                                            self.n / sum(k * om**2 for k, om
                                                         in zip(self.k, omg)))))
                               for omg in self.omega)
            except TypeError:
                raise ValueError("multiplicities not integral")
        if expand:
            self.m = tuple(map(_expand, self.m))
        if factor:
            self.m = tuple(map(_factor, self.m))
        if simplify:
            self.m = tuple(map(_simplify, self.m))
        return self.m

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
        if "m" in self.__dict__:
            self.m = tuple(self.m[i] for i in order)
        if "P" in self.__dict__:
            self.P = Matrix(SR, [self.P[i] for i in order])
        if "Q" in self.__dict__:
            self.Q = Matrix(SR, [[r[j] for j in order] for r in self.Q])
        if "q" in self.__dict__:
            self.q.reorder(order)
        if "fsd" in self.__dict__:
            del self.fsd
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
