# -*- coding: utf-8 -*-
from warnings import warn
from sage.all import pi
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.functions.other import ceil
from sage.functions.other import floor
from sage.functions.trig import cos
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import identity_matrix
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.integer import Integer
from sage.rings.number_field.number_field import NumberField
from sage.symbolic.relation import solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .coefflist import CoefficientList
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
from .util import is_constant
from .util import is_squareSum
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
        assert all(checkPos(x) for x in self.c[1:]), "c sequence not positive"
        assert all(checkPos(x) for x in self.b[:-1]), \
            "b sequence not positive"
        self.vars = tuple(set(sum(map(variables, tuple(b) + tuple(c)), ())))
        self.a = tuple(full_simplify(b[0]-x-y)
                       for x, y in zip(self.b, self.c))
        assert self.c[1] == 1, "Invalid c[1] value"
        assert all(checkNonneg(self.b[i] - self.b[i+1])
                   for i in range(self.d)), "b sequence not non-ascending"
        assert all(checkNonneg(self.c[i+1] - self.c[i])
                   for i in range(self.d)), "c sequence not non-descending"
        assert all(checkNonneg(x) for x in self.a), \
            "a values negative"
        m = floor(self.d / 2)
        self.antipodal = all(full_simplify(self.b[i] - self.c[self.d - i])
                             == 0 for i in range(self.d) if i != m)
        if self.antipodal:
            try:
                self.r = integralize(1 + self.b[m] / self.c[self.d - m])
            except TypeError:
                raise ValueError("covering index not integral")
        self.bipartite = all(a == 0 for a in self.a)
        if self.bipartite:
            try:
                for i in range(m):
                    integralize(self.b[2*i]*self.b[2*i+1]/self.c[2])
                    integralize(self.c[2*i+1]*self.c[2*i+2]/self.c[2])
            except TypeError:
                raise ValueError("intersection array of halved graph "
                                 "not integral")
        k = [1]
        try:
            for i in range(self.d):
                k.append(integralize(k[-1]*self.b[i]/self.c[i+1]))
                if self.a[i+1] >= k[-1]:
                    raise ValueError("valency of subconstituent %d too large"
                                     % (i+1))
                if isinstance(self.a[i+1], Integer) and \
                        isinstance(k[-1], Integer) and \
                        self.a[i+1] % 2 == 1 and k[-1] % 2 == 1:
                    raise ValueError("handshake lemma not satisfied "
                                     "for subconstituent %d" % (i+1))
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
                        + (self.a[self.d] - self.a[i-1])
                            * self.p[self.d, i-1, j]
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

    def antipodalQuotient(self):
        """
        Return the parameters of the antipodal quotient.
        """
        if "quotient" not in self.__dict__:
            assert self.antipodal, "graph not antipodal"
            if self.d == 2:
                self.quotient = DRGParameters([self.b[0]/(self.b[1]+1)],
                                              [Integer(1)])
            else:
                m = floor(self.d / 2)
                b = self.b[:m]
                c = list(self.c[1:m+1])
                if self.d % 2 == 0:
                    c[-1] *= self.r
                self.quotient = DRGParameters(b, c)
        return self.quotient

    def bTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``b[0], b[1], ..., b[d-1]``,
        where ``d`` is the diameter of the graph.
        """
        self.b = rewriteTuple(self.b, expand = expand, factor = factor,
                              simplify = simplify)
        return self.b[:-1]

    def bipartiteHalf(self):
        """
        Return the parameters of the bipartite half.
        """
        if "half" not in self.__dict__:
            assert self.bipartite, "graph not bipartite"
            m = floor(self.d / 2)
            b = [self.b[2*i]*self.b[2*i+1]/self.c[2] for i in range(m)]
            c = [self.c[2*i+1]*self.c[2*i+2]/self.c[2] for i in range(m)]
            self.half = DRGParameters(b, c)
        return self.half

    def cTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``c[1], c[2], ..., c[d]``,
        where ``d`` is the diameter of the graph.
        """
        self.c = rewriteTuple(self.c, expand = expand, factor = factor,
                              simplify = simplify)
        return self.c[1:]

    def check_2design(self):
        """
        For an graph with intersection array
        {r*mu+1, (r-1)*mu, 1; 1, mu, r*mu+1},
        check whether a corresponding 2-design exists.
        """
        if self.d == 3 and self.antipodal and isinstance(self.r, Integer) \
                and isinstance(self.b[0], Integer) \
                and self.b[0] - 1 == self.b[1] + self.c[2]:
            if self.r % 2 == 0:
                ok = is_squareSum(self.b[0])
            elif self.b[0] % 2 == 0:
                ok = Integers(self.r)(self.b[0]).is_square() and \
                    Integers(self.b[0])(self.r if self.r % 4 == 1
                                        else -self.r).is_square()
            if not ok:
                raise ValueError("no corresponding 2-design: "
                                 "nonexistence by BCN, Prop. 1.10.5.")

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

    def check_combinatorial(self):
        """
        Check for various combinatorial conditions.
        """
        if checkPos(self.b[0] - 2):
            if self.b[1] == 1 and (self.d != 2 or self.c[2] != self.b[0]):
                raise ValueError("b1 = 1 and not a cycle "
                                 "or cocktail party graph")
            for i in range(2, self.d):
                if checkPos(self.b[i] - 1):
                    continue
                if self.d >= 3*i or \
                        any(self.c[j] > 1 or self.a[j] >= self.c[i+j]
                            for j in range(1, self.d - i + 1)) or \
                        (self.d >= 2*i and self.c[2*i] == 1) or \
                        any(a[j] > 0 for j in range(1, self.d - 2*i + 1)) or \
                        (i < self.d and (self.c[2] - 1)*self.a[i+1]
                                        + self.a[1] > self.a[i]):
                    raise ValueError("Godsil's diameter bound not reached: "
                                     "nonexistence by BCN, Lem. 5.3.1.")
        if self.d >= 3 and self.c[2] > 1 and 3*self.c[2] > 2*self.c[3] and \
                (self.d != 3 or self.b[2] + self.c[2] > self.c[3]):
            raise ValueError("intersection number c[3] too small: "
                             "nonexistence by BCN, Thm. 5.4.1.")
        if self.a[1] > 0 and \
                any(self.a[1] + 1 > 2*self.a[i] or
                    ((i < self.d-1 or self.a[self.d] > 0 or
                     (self.d > 2 and self.b[self.d-1] > 1)) and
                     self.a[1] + 1 > self.a[i] + self.a[i+1]) or
                    self.a[1] + 2 > self.b[i] + self.c[i+1]
                    for i in range(1, self.d)):
            raise ValueError("counting argument: "
                             "nonexistence by BCN, Prop. 5.5.1.")
        if self.d >= 2:
            if self.a[1] == 0 and any(2*self.a[i] > self.k[i]
                                      for i in range(2, self.d+1)):
                raise ValueError(u"Turán's theorem: "
                                  "nonexistence by BCN, Prop. 5.6.4.")
            if not self.antipodal:
                ka = self.k[self.d] * self.a[self.d]
                kka = self.k[self.d] * (self.k[self.d] - self.a[self.d] - 1)
                try:
                    if (self.k[1] > ka and self.k[1] > kka) or \
                            (self.k[2] > kka and (self.k[1] > ka or
                                self.k[1] > self.a[self.d] *
                                    (self.a[1] + 2 - self.a[self.d])) and
                                (self.b[self.d-1] > 1 or
                                 not (self.a[1] + 1 == self.a[self.d]) or
                                 integralize(self.k[1]/self.a[self.d])
                                    > self.k[self.d])):
                        raise TypeError
                except TypeError:
                    raise ValueError("last subconstituent too small: "
                                     "nonexistence by BCN, Prop. 5.6.1.")
                if self.d >= 3 and \
                        self.k[1] == self.k[self.d] * (self.k[self.d] - 1) \
                        and self.k[self.d] > self.a[self.d] + 1:
                    raise ValueError("last subconstituent too small: "
                                     "nonexistence by BCN, Prop. 5.6.3.")
            if isinstance(self.n, Integer) and isinstance(self.k[1], Integer) \
                    and ((self.n % 2 == 1 and self.k[1] % 2 == 1) or
                         (isinstance(self.a[1], Integer) and self.n % 3 != 0
                          and self.a[1] % 3 != 0 and self.k[1] % 3 != 0)):
                raise ValueError("handshake lemma not satisfied")
            c2one = self.c[2] == 1
            case3 = self.b[self.d-1] == 1 and self.a[self.d] == self.a[1] + 1
            case4 = False
            if self.p[2, self.d, self.d] == 0:
                try:
                    ad1 = self.a[self.d] + 1
                    bad1 = self.b[self.d-1] - ad1
                    integralize(self.k[self.d] / ad1)
                    if self.a[self.d] > self.a[1] + 1 or bad1 > 0 or \
                            self.b[self.d-1] > self.c[2] or \
                            (bad1 == 0 and self.a[self.d] > 0) \
                            or (self.b[self.d-1] > 1 and ad1 > self.a[1]):
                        raise TypeError
                    case4 = self.b[self.d-1] <= 1 and self.a[self.d] > 0
                except TypeError:
                    raise ValueError("p[2,d,d] = 0: "
                                     "nonexistence by BCN, Prop. 5.7.1.")
            if c2one or case3 or case4 or self.a[1] == 1 or \
                    (self.c[2] == 2 and
                        self.a[1]*(self.a[1]+3)/2 > self.k[1]) or \
                    any(self.b[i] > 1 and self.c[i] == self.b[1]
                        for i in range(2, self.d+1)):
                if case3:
                    try:
                        integralize(self.k[self.d] / (self.a[1]+2))
                    except TypeError:
                        raise ValueError("last subconstituent "
                                         "a union of cliques, "
                                         "a[1]+2 does not divide k[d]: "
                                         "nonexistence by BCN, "
                                         "Prop. 4.3.2(iii).")
                try:
                    kl = integralize(self.k[1] / (self.a[1]+1))
                    vkll = integralize(self.n*kl / (self.a[1]+2))
                except TypeError:
                    raise ValueError("handshake lemma not satisfied "
                                     "for maximal cliques")
                if self.a[1] * self.c[2] > self.a[2] or \
                        (c2one and 1 + self.b[1]*(self.b[1]+1) *
                                        (self.a[1]+2)/(1 + self.a[1]) > vkll):
                    raise ValueError("graph with maximal cliques: "
                                     "nonexistence by BCN, Prop. 4.3.3.")

    def check_conference(self):
        """
        Check whether a conference graph can exist.
        """
        if self.d == 2 and all(isinstance(x, Integer)
                               for x in self.b + self.c) and \
                self.b[1] == self.c[2] and self.b[0] == 2*self.b[1] and \
                (self.n % 4 != 1 or not is_squareSum(self.n)):
            raise ValueError("conference graph must have order "
                             "a sum of two squares with residue 1 (mod 4)")

    def check_feasible(self, recurse = True):
        """
        Check whether the intersection array is feasible.
        """
        if self.d == 1 or self.k[1] == 2:
            return
        self.check_combinatorial()
        self.check_conference()
        self.check_geodeticEmbedding()
        self.check_2design()
        self.check_genPoly()
        self.check_terwilliger()
        self.check_secondEigenvalue()
        self.check_localEigenvalues()
        self.check_absoluteBound()
        if recurse:
            if self.bipartite:
                try:
                    self.bipartiteHalf().check_feasible()
                except (ValueError, AssertionError) as ex:
                    raise ex.__class__("bipartite half:", *ex.args)
            if self.antipodal:
                if self.bipartite:
                    recurse = False
                try:
                    self.antipodalQuotient().check_feasible(recurse)
                except (ValueError, AssertionError) as ex:
                    raise ex.__class__("antipodal quotient:", *ex.args)

    def check_genPoly(self):
        """
        For a graph with parameters of a generalized polygon,
        check whether its parameters satisfy the restrictions.
        """
        g, s, t = self.genPoly_parameters()
        if g:
            try:
                st = integralize(s*t)
                st2 = 2*st
            except TypeError:
                st = st2 = Integer(1)
            if g not in [2, 4, 6, 8, 12] or (s > 1 and t > 1 and \
                    (g == 12 or
                     (g == 8 and (not st2.is_square() or
                                  s > t**2 or t > s**2)) or
                     (g == 6 and (not st.is_square()
                                  or s > t**3 or t > s**3)))):
                raise ValueError("no corresponding generalized polygon: "
                                 "nonexistence by BCN, Thm. 6.5.1.")
            if g == 6 and 1 in [s, t]:
                m = next(x for x in [s, t] if x != 1)
                if isinstance(m, Integer) and (m == 10 or m % 8 == 6):
                    raise ValueError("PG(2, q) does not exist "
                                     "for q = 10 or q = 8n+6")

    def check_geodeticEmbedding(self):
        """
        For a graph with intersection array {2b, b, 1; 1, 1, 2b},
        check whether there exists an embedding
        into a geodetic graph of diameter 2.
        """
        if self.d == 3 and self.b[0] == self.c[3] and self.b[2] == 1 \
                and self.c[2] == 1 and self.b[0] == 2*self.b[1] \
                and self.b[0] > 4:
            raise ValueError("no embedding into a geodetic graph "
                             "of diameter 2: nonexistence by BCN, "
                             "Prop. 1.17.3.")

    def check_localEigenvalues(self):
        """
        For a graph of diameter at least 3,
        check whether the eigenvalues of the local graph
        are in the allowed range.
        """
        if "m" not in self.__dict__:
            self.multiplicities()
        if self.d >= 3 and not self.match(((5, 2, 1), (1, 2, 5))) and \
                all(is_constant(th) for th in self.theta if th != self.k[1]):
            th1, i = max((th, h) for h, th in enumerate(self.theta)
                         if th != self.k[1])
            thd, j = min((th, h) for h, th in enumerate(self.theta)
                         if th != self.k[1])
            if (self.b[1]/(th1+1) < 1 and self.c[2] != 1) or \
                    (self.b[1]/(thd+1) > -2 and self.a[1] != 0):
                raise ValueError("local eigenvalues not in allowed range: "
                                 "nonexistence by BCN, Thm. 4.4.3.")
            s = {h for h, m in enumerate(self.m)
                 if self.theta[h] != self.k[1] and m < self.k[1]}
            if not s.issubset({i, j}):
                raise ValueError("m[i] < k for i != 2, d: "
                                 "nonexistence by BCN, Thm. 4.4.4.")
            r = []
            for h in s:
                t = self.b[1] / (self.theta[h] + 1)
                try:
                    integralize(t)
                except TypeError:
                    r.append(t)
            if len(r) == 0:
                return
            p = next(iter(r)).minpoly()
            k = NumberField(p, names = ('a', ))
            a, = k.gen()
            if len(r) == 1 or p.degree() != 2 or \
                    len({t.minpoly() for t in r}) == 2 or not a.is_integral():
                raise ValueError("m[i] < k, b[1]/(theta[1]+1) and "
                                 "b[1]/(theta[d]+1) not integers "
                                 "or algebraic conjugates: "
                                 "nonexistence by BCN, Thm. 4.4.4.")

    def check_secondEigenvalue(self):
        """
        For a graph with the second eigenvalue equal to b[1]-1,
        check whether it belongs to the characterization.
        """
        if "theta" not in self.__dict__:
            self.eigenvalues()
        if (self.b[1] - 1) in self.theta:
            if (self.d != 2 or all(th != -2 for th in self.theta)
                    or self.n > 28) and self.c[2] != 1 and \
                    not (self.is_hamming() or
                         self.is_locallyPetersen() or
                         self.is_johnson() or
                         self.is_halfCube() or
                         self.match(((27, 10, 1), (1, 10, 27)))):
                raise ValueError("theta[1] = b[1]-1, not in characterization:"
                                 " nonexistence by BCN, Thm. 4.4.11.")

    def check_terwilliger(self):
        """
        Check whether the graph is a Terwilliger graph
        and whether existence conditions are satisfied in this case,
        or if the Terwilliger diameter bound is satisfied otherwise.
        """
        small = (self.d == 2 and 50 * self.c[2] > self.n) or \
                (self.d >= 3 and 50 * (self.c[2] - 1) > self.b[0])
        if self.d >= 2 and isinstance(self.b[0], Integer) and \
                isinstance(self.a[1], Integer) and \
                isinstance(self.c[2], Integer):
            if self.b[0] == 10 and self.a[1] == 3 and \
                    (self.c[2] == 2 or self.b[2] > self.c[2]):
                s = 4
            else:
                s = ceil(self.b[0] / (self.a[1] + 1))
            v = 2*(s*(self.a[1] + 1) - self.b[0]) / (s*(s-1)) + 1 - self.c[2]
            if v > 0:
                raise ValueError("coclique bound exceeded: "
                                 "nonexistence by KP10, Thm. 3.")
            elif v == 0:
                if small and not self.is_locallyPetersen() and \
                        not self.match(((2, 1), (1, 1)), ((5, 4), (1, 1)),
                                       ((5, 2, 1), (1, 2, 5))):
                    raise ValueError("too small for a Terwilliger graph: "
                                     "nonexistence by BCN, Cor. 1.16.6.")
                return
        if self.c[2] <= 2 and (small
                or self.b[1]*(self.c[1]-1) > self.a[1]*(self.a[1]-1)
                or (self.d >= 3 and self.c[3] > 1
                                and 2*self.c[2] > self.c[3])) and \
                any(self.c[i] + self.a[1]+ self.b[i+1] + 2
                    > self.b[i] + self.c[i+1]
                    for i in range(self.d)):
            raise ValueError("Terwilliger's diameter bound not reached: "
                             "nonexistence by BCN, Thm. 5.2.1.")

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

    def dualEigenmatrix(self, expand = False, factor = False,
                        simplify = False):
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
            if self.k[1] == 2:
                self.theta = tuple(2*cos(2*i*pi/self.n)
                                   for i in range(self.d + 1))
            else:
                B = Matrix(SR, [M[1] for M in self.p])
                self.theta = B.eigenvalues()
                try:
                    self.theta.sort(
                        key = lambda x: CoefficientList(x, self.vars),
                        reverse = True)
                except:
                    warn(Warning("Sorting of eigenvalues failed - "
                                 "you may want to sort theta manually"))
                else:
                    if len(self.vars) > 1:
                        warn(Warning("More than one variable is used - "
                                     "please check that the ordering "
                                     "of the eigenvalues is correct"))
                self.theta = tuple(self.theta)
        self.theta = rewriteTuple(self.theta, expand = expand,
                                  factor = factor, simplify = simplify)
        return self.theta

    def genPoly_parameters(self, expand = False, factor = False,
                           simplify = False):
        """
        Determine the parameters of the generalized polygon
        whose collinearity graph has matching parameters.
        """
        try:
            t = rewriteExp(self.c[self.d] - 1, expand = expand,
                           factor = factor, simplify = simplify)
            s = rewriteExp(integralize(self.b[0] / self.c[self.d]),
                           expand = expand, factor = factor,
                           simplify = simplify)
            st = s * t
            if any(c != 1 or b != st
                   for b, c in zip(self.b[1:-1], self.c[1:-1])):
                raise TypeError
            return (2*self.d, s, t)
        except TypeError:
            return (False, None, None)

    def intersectionArray(self, expand = False, factor = False,
                          simplify = False):
        """
        Return the intersection array of the graph as a tuple of two tuples.
        """
        return (self.bTable(expand = expand, factor = factor,
                            simplify = simplify),
                self.cTable(expand = expand, factor = factor,
                            simplify = simplify))

    def is_antipodal(self):
        """
        Check whether the graph is antipodal,
        and return the covering index if it is.
        """
        return self.r if self.antipodal else False

    def is_bipartite(self):
        """
        Check whether the graph is bipartite.
        """
        return self.bipartite

    def is_formallySelfDual(self):
        """
        Check whether the graph is formally self-dual.
        """
        if "fsd" not in self.__dict__:
            self.fsd = (self.eigenmatrix(simplify = 2)
                        - self.dualEigenmatrix(simplify = 2)).is_zero()
        return self.fsd

    def is_halfCube(self):
        """
        Check whether the graph can be a halved cube.
        """
        b1 = [SR(x) == (self.d-i) * (2*(self.d-i) - 1)
              for i, x in enumerate(self.b[:-1])]
        b2 = [SR(x) == (self.d-i) * (2*(self.d-i) + 1)
              for i, x in enumerate(self.b[:-1])]
        c = [SR(x) == (i+1) * (2*i + 1) for i, x in enumerate(self.c[1:])]
        return len(solve(b1 + c, self.vars)) > 0 or \
               len(solve(b2 + c, self.vars)) > 0

    def is_hamming(self):
        """
        Check whether the graph can be a Hamming (or Doob) graph.
        """
        z = SR.symbol()
        return len(solve([SR(x) == (self.d-i) * z
                          for i, x in enumerate(self.b[:-1])] +
                          [SR(x) == i+1 for i, x in enumerate(self.c[1:])],
                         self.vars + (z, ))) > 0

    def is_johnson(self):
        """
        Check whether the graph can be a Johnson graph.
        """
        z = SR.symbol()
        return len(solve([SR(x) == (self.d-i) * (self.d - z - i)
                          for i, x in enumerate(self.b[:-1])] +
                          [SR(x) == (i+1)**2 for i, x
                           in enumerate(self.c[1:])], self.vars + (z, ))) > 0

    def is_locallyPetersen(self):
        """
        Check whether the graph can be locally Petersen.
        """
        return self.match(((10, 6), (1, 6)), ((10, 6, 4), (1, 2, 5)),
                          ((10, 6, 4, 1), (1, 2, 6, 10)))

    def kTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``k[0], k[1], ..., k[d]``,
        where ``d`` is the diameter of the graph.
        """
        self.k = rewriteTuple(self.k, expand = expand, factor = factor,
                              simplify = simplify)
        return self.k

    def kreinParameters(self, expand = False, factor = False,
                        simplify = False):
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

    def match(self, *ial):
        """
        Check whether the graph matches any of the given intersection arrays.
        """
        for b, c in ial:
            assert len(b) == len(c), "parameter length mismatch"
            if self.d != len(b):
                continue
            if len(solve([SR(l) == r for l, r
                         in zip(self.b[:-1] + self.c[1:],
                                tuple(b) + tuple(c))], self.vars)) > 0:
                return True
        return False

    def multiplicities(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the multiplicities of the eigenvalues.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        if "m" not in self.__dict__:
            if self.k[1] == 2:
                self.m = tuple(Integer(1 if th in [2, -2] else 2)
                               for th in self.theta)
            else:
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
