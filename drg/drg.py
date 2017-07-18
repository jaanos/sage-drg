# -*- coding: utf-8 -*-
from warnings import warn
from sage.all import pi
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.combinat.q_analogues import q_int
from sage.functions.log import log
from sage.functions.other import ceil
from sage.functions.other import floor
from sage.functions.other import sqrt
from sage.functions.trig import cos
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import identity_matrix
from sage.misc.misc import subsets
from sage.misc.misc import uniq
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.integer import Integer
from sage.rings.number_field.number_field import NumberField
from sage.symbolic.expression import Expression
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .coefflist import CoefficientList
from .nonex import checkConditions
from .nonex import classicalFamilies
from .nonex import families
from .nonex import sporadic
from .partition import PartitionGraph
from .util import checkNonneg
from .util import checkPos
from .util import checkPowerOf
from .util import checkPrimePower
from .util import _factor
from .util import full_simplify
from .util import hard_ceiling
from .util import hard_floor
from .util import integralize
from .util import is_constant
from .util import is_squareSum
from .util import matrixMap
from .util import rewriteExp
from .util import rewriteMatrix
from .util import rewriteTuple
from .util import subs
from .util import variables

class InfeasibleError(Exception):
    """
    Infeasibility of a parameter set.
    """

    def __init__(self, reason = None, refs = None, part = None):
        """
        Exception constructor.
        """
        part = () if part is None else (part, )
        if isinstance(reason, InfeasibleError):
            self.reason = reason.reason
            self.refs = reason.refs
            self.part = reason.part + part
        elif isinstance(reason, Exception):
            self.reason = ", ".join(str(x) for x in reason.args)
            self.refs = []
            self.part = part
        else:
            self.reason = reason
            if refs is None:
                refs = []
            elif not isinstance(refs, list):
                refs = [refs]
            self.refs = [ref if isinstance(ref, tuple) else (ref, None)
                         for ref in refs]
            self.part = part
        msg = []
        if len(self.part) > 0:
            msg.append(" of ".join(self.part))
        if self.reason is not None:
            msg.append(self.reason)
        if len(self.refs) > 0:
            msg.append("nonexistence by %s" %
                       "; ".join(self.formatRef(ref) for ref in self.refs))
        msg = ": ".join(msg)
        if isinstance(msg, unicode):
            msg = msg.encode("utf-8")
        self.args = (msg, )

    @staticmethod
    def formatRef(ref):
        """
        Format reason for nonexistence.
        """
        pap, thm = ref
        if thm is None:
            return pap
        else:
            return "%s, %s" % (pap, thm)

class DRGParameters:
    """
    A class for parameters of a distance-regular graph
    and checking their feasibility.
    """

    def __init__(self, b, c, alpha = None, beta = None, complement = None):
        """
        Object constructor.

        Takes two iterables of the same length ``d`` as input,
        representing the intersection array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}``.
        The basic checks on integrality and nonnegativity
        of the intersection array are performed.

        If three parameters are given,
        they are understood as the valency and numbers of common neighbours
        of two adjacent and two nonadjacent vertices, respectively,
        in a strongly regular graph.
        If four parameters are given,
        they are understood as the classical parameters.
        """
        if alpha is not None:
            if beta is not None:
                self.d = Integer(b)
                q = c
                b = [(q_int(self.d, q) - q_int(i, q)) *
                     (beta - alpha * q_int(i, q)) for i in range(self.d)]
                c = [q_int(i, q) * (1 + alpha * q_int(i-1, q))
                     for i in range(1, self.d + 1)]
            elif b - c == 1:
                self.d = Integer(1)
                b, c = (b, ), (1, )
            else:
                self.d = Integer(2)
                b, c = (b, b-c-1), (1, alpha)
        else:
            self.d = Integer(len(b))
        assert self.d == len(c), "parameter length mismatch"
        try:
            self.c = tuple([Integer(0)] + map(integralize, c))
        except TypeError:
            raise InfeasibleError("c sequence not integral")
        try:
            self.b = tuple(map(integralize, b) + [Integer(0)])
        except TypeError:
            raise InfeasibleError("b sequence not integral")
        assert all(checkPos(x) for x in self.c[1:]), \
            "c sequence not positive"
        assert all(checkPos(x) for x in self.b[:-1]), \
            "b sequence not positive"
        self.vars = tuple(set(sum(map(variables, tuple(b) + tuple(c)), ())))
        self.vars_ordered = len(self.vars) <= 1
        self.prefix = "v%x" % (hash(self) % Integer(2)**32)
        self.subgraphs = {}
        self.distance_graphs = {}
        self.triple = {}
        self.a = tuple(full_simplify(b[0]-x-y)
                       for x, y in zip(self.b, self.c))
        assert self.c[1] == 1, "Invalid c[1] value"
        assert all(checkNonneg(self.b[i] - self.b[i+1])
                   for i in range(self.d)), "b sequence not non-ascending"
        assert all(checkNonneg(self.c[i+1] - self.c[i])
                   for i in range(self.d)), "c sequence not non-descending"
        assert all(checkNonneg(x) for x in self.a), \
            "a values negative"
        if any(any(self.b[j] < self.c[i]
                   for j in range(self.d-i+1)) for i in range(self.d+1)):
            raise InfeasibleError("b[j] < c[i] with i+j <= d",
                                  ("BCN", "Proposition 4.1.6.(ii)"))
        m = floor(self.d / 2)
        self.antipodal = all(full_simplify(self.b[i] - self.c[self.d - i])
                             == 0 for i in range(self.d) if i != m)
        self.bipartite = all(a == 0 for a in self.a)
        k = [Integer(1)]
        try:
            for i in range(self.d):
                k.append(integralize(k[-1]*self.b[i]/self.c[i+1]))
                if self.a[i+1] >= k[-1]:
                    raise InfeasibleError("valency of subconstituent %d "
                                          "too large" % (i+1))
                if isinstance(self.a[i+1], Integer) and \
                        isinstance(k[-1], Integer) and \
                        self.a[i+1] % 2 == 1 and k[-1] % 2 == 1:
                    raise InfeasibleError("handshake lemma not satisfied "
                                          "for subconstituent %d" % (i+1))
        except TypeError:
            raise InfeasibleError("subconstituents not integral")
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
                        raise InfeasibleError("intersection number "
                                              "p[%d, %d, %d] is nonintegral"
                                               % (h, i, j))
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
                    raise InfeasibleError("intersection number p[%d, %d, %d]"
                                          " is nonintegral" % (self.d, i, j))
                assert checkNonneg(self.p[self.d, i, j]), \
                    "intersection number p[%d, %d, %d] is negative" % \
                    (self.d, i, j)
        if self.antipodal:
            try:
                self.r = integralize(1 + self.b[m] / self.c[self.d - m])
            except TypeError:
                raise InfeasibleError("covering index not integral")
            if self.d == 2:
                b = [self.b[0]/(self.b[1]+1)]
                c = [Integer(1)]
            elif self.d >= 3:
                m = floor(self.d / 2)
                b = self.b[:m]
                c = list(self.c[1:m+1])
                if self.d % 2 == 0:
                    c[-1] *= self.r
            if self.d >= 2:
                self.quotient = self.add_subgraph((tuple(b), tuple(c)),
                                                  "antipodal quotient")
        if self.bipartite and self.d >= 2:
            m = floor(self.d / 2)
            b = tuple(self.b[2*i]*self.b[2*i+1]/self.c[2] for i in range(m))
            c = tuple(self.c[2*i+1]*self.c[2*i+2]/self.c[2]
                      for i in range(m))
            self.half = self.add_subgraph((b, c), "bipartite half")
        if self.d == 2 and checkPos(self.b[0] - self.c[2]) \
                and complement is not False:
            if complement is None:
                complement = DRGParameters((self.k[2], self.p[2, 2, 1]),
                                           (Integer(1), self.p[1, 2, 2]),
                                           complement = self)
            self.complement = self.add_subgraph(complement, "complement")

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash(self.intersectionArray())

    def __eq__(self, other):
        """
        Compare self to other.
        """
        ia = self.intersectionArray()
        if isinstance(other, DRGParameters):
            return ia == other.intersectionArray()
        else:
            return ia == other

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
               "with intersection array %s" % \
               self.format_intersectionArray()

    def aTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``a[1], a[2], ..., a[d]``,
        where ``d`` is the diameter of the graph.
        """
        self.a = rewriteTuple(self.a, expand = expand, factor = factor,
                              simplify = simplify)
        return self.a[1:]

    def add_subgraph(self, ia, part):
        """
        Add a derived graph into the list.
        """
        if ia in self.distance_graphs:
            return next(g for g in self.distance_graphs if g == ia)
        elif ia in self.subgraphs:
            return next(g for g in self.subgraphs if g == ia)
        elif not isinstance(ia, DRGParameters):
            try:
                ia = DRGParameters(*ia)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = part)
        if ia.n == self.n:
            self.distance_graphs[ia] = part
        else:
            self.subgraphs[ia] = part
        return ia

    def antipodalQuotient(self):
        """
        Return the parameters of the antipodal quotient.
        """
        assert self.antipodal, "graph not antipodal"
        assert self.d >= 2, "quotient of complete graph has diameter 0"
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
        assert self.bipartite, "graph not bipartite"
        assert self.d >= 2, "bipartite half of complete graph has diameter 0"
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
                raise InfeasibleError("no corresponding 2-design",
                                      ("BCN", "Prop. 1.10.5."))

    def check_2graph(self):
        """
        For a strongly regular or Taylor graph,
        check whether a regular 2-graph can be derived.
        """
        if self.d == 2 and self.n == 2*(2*self.b[0] - self.a[1] - self.c[2]):
            mu = self.b[0] - self.c[2]
            if checkPos(mu):
                self.add_subgraph(((2*mu, self.b[1]), (Integer(1), mu)),
                                  "2-graph derivation")
        elif self.d == 3 and self.antipodal and \
                self.r == 2 and self.a[1] > 0:
            try:
                mu = integralize(self.a[1] / 2)
                n = integralize(self.n / 4)
            except TypeError:
                raise InfeasibleError("Taylor graph with a[1] > 0 odd "
                                      "or cover of K_n with n odd",
                                      ("BCN", "Thm. 1.5.3."))
            self.local_graph = self.add_subgraph(((self.a[1], n - mu - 1),
                                                  (Integer(1), mu)),
                                                 "local graph")

    def check_absoluteBound(self):
        """
        Check whether the absolute bound is not exceeded.
        """
        if "q" not in self.__dict__:
            self.kreinParameters()
        for i in range(self.d + 1):
            if sum(self.m[h] for h in range(self.d + 1)
                   if self.q[h, i, i] != 0) > self.m[i]*(self.m[i] + 1)/2:
                raise InfeasibleError("absolute bound exceeded "
                                      "for (%d, %d)" % (i, i))
            for j in range(i+1, self.d + 1):
                if sum(self.m[h] for h in range(self.d + 1)
                       if self.q[h, i, j] != 0) > self.m[i]*self.m[j]:
                    raise InfeasibleError("absolute bound exceeded "
                                          "for (%d, %d)" % (i, j))

    def check_antipodal(self):
        """
        For an antipodal cover of even diameter at least 4,
        check whether its quotient satisfies necessary conditions
        for the existence of a cover.
        """
        if self.antipodal and self.d >= 4 and self.d % 2 == 0:
            q = self.antipodalQuotient()
            try:
                integralize(sum(q.p[q.d, i, q.d-i] for i in range(1, q.d))
                            / self.r)
                if self.d == 4 and self.c[2] == 1:
                    kl = q.b[0] / (q.a[1] + 1)
                    if self.r > kl:
                        raise TypeError
                    integralize(q.n*kl / (q.a[1]+2))
            except TypeError:
                raise InfeasibleError("quotient cannot have covers "
                                      "of even diameter",
                                      ("BCN", "Prop. 4.2.7."))

    def check_classical(self):
        """
        Check whether the graph has classical parameters for which
        nonexistence has been shown as a part of an infinite family.
        """
        if self.d >= 3:
            s = SR.symbol("__s")
            sols = sorted([s.subs(ss) for ss in
                           _solve((s+1)*(self.a[1]+1)
                                  - s*(s+1)*(self.c[2]-1)/2
                                  == self.b[0], s)])
            x, y = hard_ceiling(sols[0], 0), hard_floor(sols[-1], self.b[0])
            try:
                q = integralize(sqrt(self.c[2]) - 1)
                r = hard_floor(((self.a[1] + 1)
                                - (self.b[0] - self.b[2]) / (q+2))
                               / (q+1) + 1)
                if q == 0:
                    t = r
                else:
                    t = hard_floor(((self.a[1] + 1)/(self.c[2] - 1) + 1) / 2)
                if q >= 2 and x >= 2 and x <= y and x <= r and x <= t \
                        and not self.is_grassmann():
                    raise InfeasibleError("not a Grassmann graph",
                                          ("Metsch95", "Thm. 2.3."))
            except TypeError:
                pass
        clas = self.is_classical()
        if not clas:
            return
        for cl, (cond, ref) in classicalFamilies.items():
            if isinstance(cl[0], Expression):
                diam = cl[0] == self.d
                cl = tuple(subs(exp, diam) for exp in cl)
            else:
                diam = None
            vars = tuple(set(sum(map(variables, cl), ())))
            for c in clas:
                sols = _solve([SR(l) == r for l, r in zip(c, cl)], vars)
                if all(isinstance(e, Expression) for e in sols):
                    continue
                if diam is not None:
                    sols = [s + [diam] for s in sols]
                if any(checkConditions(cond, sol) for sol in sols):
                    raise InfeasibleError(refs = ref)
        if self.d >= 3 and self.a[1] == 0 and self.a[2] > 0 and \
                self.c[2] > 2:
            raise InfeasibleError("classical with a[1] = 0, "
                                  "a[2] > 0 and c[2] > 2",
                                  ("PanWeng09", "Thm. 2.1."))
        if self.d >= 4 and self.a[1] > 0 and self.c[2] > 1 and \
                any(b < 0 for d, b, alpha, beta in clas) and \
                not self.is_dualPolar2Aodd() and not self.is_hermitean() \
                and not self.is_weng_feasible():
            raise InfeasibleError("classical with b < 0",
                                  ("Weng99", "Thm. 10.3."))
        if self.d < 3:
            return
        for d, b, alpha, beta in clas:
            try:
                b = integralize(b)
            except TypeError:
                continue
            if x <= y and is_constant(alpha) and is_constant(beta) and \
                    alpha >= 1 and alpha == b - 1:
                t = hard_floor((1 + self.a[1] + b**2 * (b**2 + b + 1))
                               / (b**3 + b**2 + 2*b - 1))
                if x <= t and (d != 3 or b != 2 or
                               (x <= 7 and y >= 7 and t >= 7)) and \
                        not self.is_bilinearForms():
                    raise InfeasibleError("not a bilinear forms graph",
                                          ("Metsch99", "Prop. 2.2."))

    def check_combinatorial(self):
        """
        Check for various combinatorial conditions.
        """
        self.maxCliques = False
        if checkPos(self.b[0] - 2):
            if self.b[1] == 1 and (self.d != 2 or self.c[2] != self.b[0]):
                raise InfeasibleError("b1 = 1 and not a cycle "
                                      "or cocktail party graph")
            for i in range(2, self.d):
                if checkPos(self.b[i] - 1):
                    continue
                if self.d >= 3*i or \
                        any(self.c[j] > 1 or self.a[j] >= self.c[i+j]
                            for j in range(1, self.d - i + 1)) or \
                        (self.d >= 2*i and self.c[2*i] == 1) or \
                        any(self.a[j] > 0 for j
                            in range(1, self.d - 2*i + 1)) or \
                        (i < self.d and (self.c[2] - 1)*self.a[i+1]
                                        + self.a[1] > self.a[i]):
                    raise InfeasibleError("Godsil's diameter bound "
                                          "not reached",
                                          ("BCN", "Lem. 5.3.1."))
        if self.d >= 3 and self.c[2] > 1 and 3*self.c[2] > 2*self.c[3] and \
                (self.d != 3 or self.b[2] + self.c[2] > self.c[3]):
            raise InfeasibleError("intersection number c[3] too small",
                                  ("BCN", "Thm. 5.4.1."))
        for i in range(2, self.d):
            if self.b[i] != self.b[1]:
                break
            if self.c[i] != 1:
                raise InfeasibleError("impossible arrangement of lines",
                                      ("BCN", "Thm. 5.4.4."))
        if self.a[1] > 0 and \
                any(self.a[1] + 1 > 2*self.a[i] or
                    ((i < self.d-1 or self.a[self.d] > 0 or
                     (self.d > 2 and self.b[self.d-1] > 1)) and
                     self.a[1] + 1 > self.a[i] + self.a[i+1]) or
                    self.a[1] + 2 > self.b[i] + self.c[i+1]
                    for i in range(1, self.d)):
            raise InfeasibleError("counting argument",
                                  ("BCN", "Prop. 5.5.1."))
        if self.d >= 4 and set(self.a[1:4]) == {0} and \
                self.c[2:5] == (1, 2, 3):
            try:
                integralize(self.b[1] * self.b[2] * self.b[3] / 4)
                integralize(self.n * self.k[4] / 36)
            except TypeError:
                raise InfeasibleError("handshake lemma not satisfied "
                                      "for Pappus subgraphs", "Koolen92")
        if self.d >= 2:
            if self.a[1] == 0 and any(2*self.a[i] > self.k[i]
                                      for i in range(2, self.d+1)):
                raise InfeasibleError(u"Turán's theorem",
                                      ("BCN", "Prop. 5.6.4."))
            for h in range(1, self.d + 1):
                for i in range(self.d + 1):
                    for j in range(abs(h-i), min(self.d, h+i) + 1):
                        if self.p[h, i, j] > 0:
                            ppm = self.p[h, i+1, j-1] \
                                if i < self.d and j > 0 else 0
                            ppz = self.p[h, i+1, j] if i < self.d else 0
                            ppp = self.p[h, i+1, j+1] \
                                if i < self.d and j < self.d else 0
                            pzm = self.p[h, i, j-1] if j > 0 else 0
                            pzp = self.p[h, i, j+1] if j < self.d else 0
                            pmm = self.p[h, i-1, j-1] \
                                if i > 0 and j > 0 else 0
                            pmz = self.p[h, i-1, j] if i > 0 else 0
                            pmp = self.p[h, i-1, j+1] \
                                if i > 0 and j < self.d else 0
                            if ppm + ppz + ppp < self.b[i] or \
                                    pzm + self.p[h, i, j] + pzp \
                                        < self.a[i] + 1 or \
                                    pmm + pmz + pmp < self.c[i]:
                                raise InfeasibleError("counting argument",
                                                      "Lambeck93")
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
                    raise InfeasibleError("last subconstituent too small",
                                          ("BCN", "Prop. 5.6.1."))
                if self.d >= 3 and \
                        self.k[1] == self.k[self.d] * (self.k[self.d] - 1) \
                        and self.k[self.d] > self.a[self.d] + 1:
                    raise InfeasibleError("last subconstituent too small",
                                          ("BCN", "Prop. 5.6.3."))
            if isinstance(self.n, Integer) and isinstance(self.k[1], Integer) \
                    and ((self.n % 2 == 1 and self.k[1] % 2 == 1) or
                         (isinstance(self.a[1], Integer) and self.n % 3 != 0
                          and self.a[1] % 3 != 0 and self.k[1] % 3 != 0)):
                raise InfeasibleError("handshake lemma not satisfied")
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
                    raise InfeasibleError("p[2,d,d] = 0",
                                          ("BCN", "Prop. 5.7.1."))
            if c2one or case3 or case4 or self.a[1] == 1 or \
                    (self.c[2] == 2 and
                        self.a[1]*(self.a[1]+3)/2 > self.k[1]) or \
                    any(self.b[i] > 1 and self.c[i] == self.b[1]
                        for i in range(2, self.d+1)):
                if case3:
                    try:
                        integralize(self.k[self.d] / (self.a[1]+2))
                    except TypeError:
                        raise InfeasibleError("last subconstituent a union "
                                              "of cliques, a[1]+2 does not "
                                              "divide k[d]",
                                              ("BCN", "Prop. 4.3.2.(iii)"))
                try:
                    kl = integralize(self.k[1] / (self.a[1]+1))
                    vkll = integralize(self.n*kl / (self.a[1]+2))
                except TypeError:
                    raise InfeasibleError("handshake lemma not satisfied "
                                          "for maximal cliques")
                if self.a[1] * self.c[2] > self.a[2] or \
                        (c2one and 1 + self.b[1]*(self.b[1]+1) *
                                        (self.a[1]+2)/(1 + self.a[1]) > vkll):
                    raise InfeasibleError("graph with maximal cliques",
                                          ("BCN", "Prop. 4.3.3."))
                self.maxCliques = True

    def check_conference(self):
        """
        Check whether a conference graph can exist.
        """
        if self.d == 2 and all(isinstance(x, Integer)
                               for x in self.b + self.c) and \
                self.b[1] == self.c[2] and self.b[0] == 2*self.b[1] and \
                (self.n % 4 != 1 or not is_squareSum(self.n)):
            raise InfeasibleError("conference graph must have order a sum "
                                  "of two squares with residue 1 (mod 4)")

    def check_family(self):
        """
        Check whether the graph has an intersection array for which
        nonexistence has been shown as a part of an infinite family.
        """
        for (b, c), (cond, ref) in families.items():
            if len(b) != self.d:
                continue
            vars = tuple(set(sum(map(variables, b + c), ())))
            sols = _solve([SR(l) == r for l, r
                           in zip(self.b[:-1] + self.c[1:], b + c)], vars)
            if any(checkConditions(cond, sol) for sol in sols):
                raise InfeasibleError(refs = ref)

    def check_feasible(self, checked = None, skip = None):
        """
        Check whether the intersection array is feasible.
        """
        if self.d == 1 or self.k[1] == 2:
            return
        ia = self.intersectionArray()
        if checked is None:
            checked = set()
        if ia in checked:
            return
        checks = [
            ("sporadic", self.check_sporadic),
            ("family", self.check_family),
            ("2graph", self.check_2graph),
            ("classical", self.check_classical),
            ("combinatorial", self.check_combinatorial),
            ("conference", self.check_conference),
            ("geodeticEmbedding", self.check_geodeticEmbedding),
            ("2design", self.check_2design),
            ("hadamard", self.check_hadamard),
            ("antipodal", self.check_antipodal),
            ("genPoly", self.check_genPoly),
            ("terwilliger", self.check_terwilliger),
            ("secondEigenvalue", self.check_secondEigenvalue),
            ("localEigenvalues", self.check_localEigenvalues),
            ("absoluteBound", self.check_absoluteBound),
        ]
        if skip is None:
            skip = set()
        elif isinstance(skip, str):
            skip = {skip}
        else:
            skip = set(skip)
        for name, check in checks:
            if name not in skip:
                check()
        checked.add(ia)
        for ia, part in self.subgraphs.items():
            try:
                ia.check_feasible(checked)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = part)
        if "complement" in self.__dict__:
            try:
                self.complement.check_feasible(checked)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = "complement")
        for idx in subsets(range(1, self.d + 1)):
            if len(idx) > 0 and len(idx) < self.d and idx != [1]:
                part = "distance-%s graph" % (idx if len(idx) > 1
                                                  else idx[0])
                try:
                    dg = self.add_subgraph(self.mergeClasses(*idx), part)
                    dg.check_feasible(checked)
                except (InfeasibleError, AssertionError) as ex:
                    raise InfeasibleError(ex, part = part)
                except IndexError:
                    pass

    def check_genPoly(self):
        """
        For a graph with parameters of a generalized polygon,
        check whether its parameters satisfy the restrictions.
        """
        if "maxCliques" not in self.__dict__:
            self.check_combinatorial()
        if not self.maxCliques:
            return
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
                                  or s > t**3 or t > s**3)) or
                     (g == 4 and (s > t**2 or t > s**2)))):
                raise InfeasibleError("no corresponding generalized polygon",
                                      ("BCN", "Thm. 6.5.1."))
            if g == 4:
                try:
                    integralize(s*t*(s+1)*(t+1) / (s+t))
                except TypeError:
                    raise InfeasibleError("infeasible parameters "
                                          "for generalized quadrangle",
                                          ("PayneThas", "1.2.2."))
            elif g == 6 and 1 in [s, t]:
                m = next(x for x in [s, t] if x != 1)
                if isinstance(m, Integer) and m % 4 in [1, 2] and \
                        not is_squareSum(m):
                    raise InfeasibleError("Bruck-Ryser theorem",
                                          ("BCN", "Thm. 1.10.4."))
        if self.antipodal and self.d == 3 and \
                self.b[0] == (self.r - 1) * (self.c[2] + 1):
            s = self.r - 1
            t = self.c[2] + 1
            if s > t**2 or t > s**2:
                raise InfeasibleError("no corresponding "
                                      "generalized quadrangle",
                                      ("BCN", "Thm. 6.5.1."))
            if s > t * (t-1):
                raise InfeasibleError("no spread in corresponding "
                                      "generalized quadrangle",
                                      [("BCN", "Prop. 12.5.2."),
                                       ("PayneThas", "1.8.3.")])
            try:
                integralize(s*t*(s+1)*(t+1) / (s+t))
            except TypeError:
                raise InfeasibleError("infeasible parameters "
                                      "for generalized quadrangle",
                                      ("PayneThas", "1.2.2."))

    def check_geodeticEmbedding(self):
        """
        For a graph with intersection array {2b, b, 1; 1, 1, 2b},
        check whether there exists an embedding
        into a geodetic graph of diameter 2.
        """
        if self.d == 3 and self.b[0] == self.c[3] and self.b[2] == 1 \
                and self.c[2] == 1 and self.b[0] == 2*self.b[1] \
                and self.b[0] > 4:
            raise InfeasibleError("no embedding into a geodetic graph "
                                  "of diameter 2", ("BCN", "Prop. 1.17.3."))

    def check_hadamard(self):
        """
        For a graph with intersection array {2c, 2c-1, c, 1; 1, c, 2c-1, 2c},
        with c > 1, check whether c is even.
        """
        if self.d == 4 and self.b[0] > 2 and self.bipartite \
                and self.antipodal and self.r == 2:
            try:
                integralize(self.c[2]/2)
            except TypeError:
                raise InfeasibleError("Hadamard graph with odd c[2]",
                                      ("BCN", "Cor. 1.8.2."))

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
            bm = -1 - self.b[1]/(th1+1)
            bp = -1 - self.b[1]/(thd+1)
            if (bm > -2 and self.c[2] != 1) or (bp < 1 and self.a[1] != 0):
                raise InfeasibleError("local eigenvalues "
                                      "not in allowed range",
                                      ("BCN", "Thm. 4.4.3."))
            if not self.bipartite:
                mu = self.a[1] + bp*bm
                bd = self.k[1] * mu - (self.a[1] - bp) * (self.a[1] - bm)
                fb = self.k[1] * self.a[1] * self.b[1] + \
                    (th1 * (self.a[1] + 1) + self.k[1]) * \
                    (thd * (self.a[1] + 1) + self.k[1])
                if bd > 0:
                    raise InfeasibleError("bound on local eigenvalues "
                                          "exceeded", u"JurišićKoolen00")
                if fb < 0:
                    raise InfeasibleError("fundamental bound exceeded",
                                          "JKT00")
                elif bd == 0 or fb == 0:
                    try:
                        integralize(self.c[2]*mu/2)
                        if self.c[2] < mu + 1:
                            raise TypeError
                    except TypeError:
                        raise InfeasibleError("local graph strongly regular",
                                              u"JurišićKoolen00")
                    if self.d == 4 and self.antipodal:
                        try:
                            bm = integralize(bm)
                            bp = integralize(bp)
                            integralize((bp - bm) / self.r)
                            if bp < 1 or bm > -2:
                                raise TypeError
                        except TypeError:
                            raise InfeasibleError("locally strongly regular "
                                                  "antipodal graph with d=4",
                                                  u"JurišićKoolen00")
                    self.local_graph = self.add_subgraph(((self.a[1],
                                                           -(bp+1)*(bm+1)),
                                                          (Integer(1), mu)),
                                                         "local graph")
            def checkMul(h):
                if self.antipodal and self.omega[h, self.d] != 1 and \
                      self.m[h] < self.k[1] + self.r - 2:
                    return ("m[%d] < k+r-2" % h, "GodsilHensel92")
                elif self.a[self.d] == 0 and \
                        1 not in [self.omega[h, 2], self.omega[h, self.d]] \
                        and self.m[h] < self.k[1] + self.b[self.d-1] - 1:
                    return ("m[%d] < k+b[d-1]-1" % h, "GodsilKoolen95")
                elif self.m[h] < self.k[1]:
                    return ("m[%d] < k" % h, ("BCN", "Thm. 4.4.4."))
                else:
                    return None
            d = {h: checkMul(h) for h in range(1, self.d)}
            s = {h for h, v in d.items() if v is not None}
            if not s.issubset([i, j]):
                m, k = min((self.m[h], h) for h in s if h not in [i, j])
                reason, ref = d[k]
                raise InfeasibleError(reason, ref)
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
            a = NumberField(p, names = ('a', )).gen()
            if len(r) == 1 or p.degree() != 2 or \
                    len({t.minpoly() for t in r}) == 2 or \
                    not a.is_integral():
                m, k = min((self.m[h], h) for h in s)
                reason, ref = d[k]
                raise InfeasibleError(reason + ", b[1]/(theta[1]+1) and "
                                      "b[1]/(theta[d]+1) not integers "
                                      "or algebraic conjugates", ref)

    def check_secondEigenvalue(self):
        """
        For a graph with the second eigenvalue equal to b[1]-1,
        check whether it belongs to the characterization.
        """
        if "theta" not in self.__dict__:
            self.eigenvalues()
        if (self.b[1] - 1) in self.theta:
            if (self.d != 2 or all(th != -2 for th in self.theta)
                    or (self.b[1] != 1 and self.n > 28)) and \
                    self.c[2] != 1 and \
                    not (self.is_hamming() or
                         self.is_locallyPetersen() or
                         self.is_johnson() or
                         self.is_halfCube() or
                         self.match(((27, 10, 1), (1, 10, 27)))):
                raise InfeasibleError("theta[1] = b[1]-1, "
                                      "not in characterization",
                                      ("BCN", "Thm. 4.4.11."))

    def check_sporadic(self):
        """
        Check whether the graph has an intersection array
        for which nonexistence has been shown sporadically.
        """
        ia = self.intersectionArray()
        if ia in sporadic:
            raise InfeasibleError(refs = sporadic[ia])

    def check_terwilliger(self):
        """
        Check whether the graph is a Terwilliger graph
        and whether existence conditions are satisfied in this case,
        or if the Terwilliger diameter bound is satisfied otherwise.
        """
        if "theta" not in self.__dict__:
            self.eigenvalues()
        small = (self.d == 2 and 50 * self.c[2] > self.n) or \
                (self.d >= 3 and 50 * (self.c[2] - 1) > self.b[0])
        if self.d >= 2 and isinstance(self.b[0], Integer) and \
                isinstance(self.a[1], Integer) and \
                isinstance(self.c[2], Integer):
            if all(isinstance(th, Integer) for th in self.theta):
                th = min(self.theta)
            else:
                th = None
            if self.b[0] == 10 and self.a[1] == 3 and \
                    (self.c[2] == 2 or self.b[2] > self.c[2]):
                s = 4
            elif th is not None and self.a[1] != 2 and \
                    -1 - self.b[1]/(th+1) < self.a[1]:
                s = ceil(self.b[0] / self.a[1])
            else:
                s = ceil(self.b[0] / (self.a[1] + 1))
            v = 2*(s*(self.a[1] + 1) - self.b[0]) / (s*(s-1)) + 1 - self.c[2]
            if v > 0:
                raise InfeasibleError("coclique bound exceeded",
                                      ("KoolenPark10", "Thm. 3."))
            elif v == 0:
                if small and not self.is_locallyPetersen() and \
                        not self.match(((2, 1), (1, 1)), ((3, 2), (1, 1)),
                                       ((5, 2, 1), (1, 2, 5))):
                    raise InfeasibleError("too small for a "
                                          "Terwilliger graph",
                                          ("BCN", "Cor. 1.16.6."))
                return
        if self.c[2] >= 2 and (small
                or self.b[1]*(self.c[1]-1) > self.a[1]*(self.a[1]-1)
                or (self.d >= 3 and self.c[3] > 1
                                and 2*self.c[2] > self.c[3])) and \
                any(self.c[i] + self.a[1] + self.b[i+1] + 2
                    > self.b[i] + self.c[i+1]
                    for i in range(self.d)):
            raise InfeasibleError("Terwilliger's diameter bound not reached",
                                  ("BCN", "Thm. 5.2.1."))

    def complementaryGraph(self):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        assert self.d == 2 and checkPos(self.b[0] - self.c[2]), \
            "the complement is not distance-regular"
        return self.complement

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

    def distancePartition(self, h = 0):
        """
        Return the diagram of the distance partition
        corresponding to a vertex (if h = 0)
        or two vertices at distance h.
        """
        return PartitionGraph(self, h)

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
                    if not self.vars_ordered:
                        warn(Warning("More than one variable is used - "
                                     "please check that the ordering "
                                     "of the eigenvalues is correct"))
                self.theta = tuple(self.theta)
        self.theta = rewriteTuple(self.theta, expand = expand,
                                  factor = factor, simplify = simplify)
        return self.theta

    def format_intersectionArray(self):
        """
        Return a string representation of the intersection array.
        """
        return "{%s; %s}" % tuple(', '.join(str(x) for x in l)
                                  for l in self.intersectionArray())

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

    def has_edges(self, h, i1, j1, i2, j2):
        """
        Determine if there can be edges between sets of vertices
        at distances (i1, j1) and (i2, j2) from two vertices at distance h
        using the currently known triple intersection numbers.
        """
        if j1 is None:
            return abs(i1 - i2) <= 1
        assert all(x >= 0 and x <= self.d for x in [h, i1, j1, i2, j2]), \
            "distance not in feasible range"
        if abs(i1 - i2) > 1 or abs(j1 - j2) > 1:
            return False
        tperms = [[0, 1, 2], [0, 2, 1], [1, 0, 2],
                  [1, 2, 0], [2, 0, 1], [2, 1, 0]]
        dperms = [[0, 1, 2], [1, 0, 2], [0, 2, 1],
                  [2, 0, 1], [1, 2, 0], [2, 1, 0]]
        for t, d in (((h, i1, j1), (i2, j2, 1)), ((h, i2, j2), (i1, j1, 1))):
            for p, q in zip(tperms, dperms):
                tp = tuple(t[i] for i in p)
                if tp in self.triple and \
                        self.triple[tp][tuple(d[i] for i in q)] == 0:
                    return False
        return True

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

    def is_bilinearForms(self):
        """
        Check whether the graph can be a bilinear forms graph
        of diameter at least 2.
        """
        s = SR.symbol("__s")
        for q in sorted([s.subs(ss) for ss in
                         _solve(s*(s+1) == self.c[2], s)], reverse = True):
            if not checkPrimePower(q):
                continue
            beta = self.b[0] * (q-1) / (q**self.d - 1)
            try:
                integralize(log(integralize(beta + 1), q))
            except TypeError:
                continue
            if self.is_classicalWithParameters(q, q-1, beta):
                return True
        return False

    def is_bipartite(self):
        """
        Check whether the graph is bipartite.
        """
        return self.bipartite

    def is_classical(self):
        """
        Check whether the graph is classical,
        and return all sets of classical parameters if it is.
        """
        if "classical" not in self.__dict__:
            clas = []
            bs = set()
            if self.d == 2:
                e = self.c[2] - self.a[1] - 2
                d = sqrt(4*self.b[1] + e**2)
                bs.add((e+d)/2)
                bs.add((e-d)/2)
            elif all(self.a[i] == self.a[1] * self.c[i]
                     for i in range(2, self.d+1)):
                bs.add(self.c[2] - 1)
                bs.add(-self.a[1] - 1)
            elif self.d >= 3:
                d = self.a[1] * self.c[3] - self.a[3]
                if d != 0:
                    bs.add((self.a[2]*self.c[3] - self.c[2]*self.a[3]) / d)
            for b in bs:
                if b in [0, -1]:
                    continue
                alpha = self.c[2] / (b+1) - 1
                beta = self.k[1] / q_int(self.d, b)
                if all(self.b[i] == (q_int(self.d, b) - q_int(i, b))
                                  * (beta - alpha * q_int(i, b)) and
                       self.c[i+1] == q_int(i+1, b)
                                    * (1 + alpha * q_int(i, b))
                       for i in range(self.d)):
                    clas.append((self.d, b, alpha, beta))
            self.classical = False if len(clas) == 0 else clas
        return self.classical

    def is_classicalWithParameters(self, b, alpha, beta):
        """
        Check whether the graph can have the specified classical parameters.
        """
        p = DRGParameters(self.d, b, alpha, beta)
        return len(_solve([SR(l) == r for l, r in
                           zip(self.b + self.c, p.b + p.c)], self.vars)) > 0

    def is_dualPolar2Aodd(self):
        """
        Check whether the graph can be a dual polar graph ^2A_{2d-1}(-b)
        of diameter at least 2.
        """
        if self.d < 2:
            return False
        q = self.c[2] - 1
        if not checkPrimePower(q):
            return False
        beta = self.b[0] * (q-1) / (q**self.d - 1)
        return q == beta**2 and self.is_classicalWithParameters(q, 0, beta)

    def is_formallySelfDual(self):
        """
        Check whether the graph is formally self-dual.
        """
        if "fsd" not in self.__dict__:
            self.fsd = (self.eigenmatrix(simplify = 2)
                        - self.dualEigenmatrix(simplify = 2)).is_zero()
        return self.fsd

    def is_grassmann(self):
        """
        Check whether the graph can be a Grassmann graph
        of diameter at least 2.
        """
        if self.d < 2:
            return False
        s = sqrt(self.c[2])
        for q in sorted([-1+s, -1-s], reverse = True):
            if not checkPrimePower(q):
                continue
            beta = self.b[0] * (q-1) / (q**self.d - 1)
            try:
                integralize(log(integralize(q + beta*(q-1)), q))
            except TypeError:
                continue
            if self.is_classicalWithParameters(q, q, beta):
                return True
        return False

    def is_halfCube(self):
        """
        Check whether the graph can be a halved cube.
        """
        b1 = [SR(x) == (self.d-i) * (2*(self.d-i) - 1)
              for i, x in enumerate(self.b[:-1])]
        b2 = [SR(x) == (self.d-i) * (2*(self.d-i) + 1)
              for i, x in enumerate(self.b[:-1])]
        c = [SR(x) == (i+1) * (2*i + 1) for i, x in enumerate(self.c[1:])]
        return len(_solve(b1 + c, self.vars)) > 0 or \
               len(_solve(b2 + c, self.vars)) > 0

    def is_hamming(self):
        """
        Check whether the graph can be a Hamming (or Doob) graph.
        """
        z = SR.symbol()
        return len(_solve([SR(x) == (self.d-i) * z
                           for i, x in enumerate(self.b[:-1])] +
                           [SR(x) == i+1 for i, x in enumerate(self.c[1:])],
                          self.vars + (z, ))) > 0

    def is_hermitean(self):
        """
        Check whether the graph can be a Hermitean forms graph
        of diameter at least 2.
        """
        s = SR.symbol("__s")
        for q in sorted([s.subs(ss) for ss in
                         _solve(s*(s+1) == self.c[2], s)]):
            if not checkPrimePower(-q):
                continue
            beta = self.b[0] * (q-1) / (q**self.d - 1)
            if beta+1 == -q**self.d and \
                    self.is_classicalWithParameters(q, q-1, beta):
                return True
        return False

    def is_johnson(self):
        """
        Check whether the graph can be a Johnson graph.
        """
        z = SR.symbol()
        return len(_solve([SR(x) == (self.d-i) * (self.d - z - i)
                           for i, x in enumerate(self.b[:-1])] +
                           [SR(x) == (i+1)**2 for i, x
                            in enumerate(self.c[1:])],
                          self.vars + (z, ))) > 0

    def is_locallyPetersen(self):
        """
        Check whether the graph can be locally Petersen.
        """
        return self.match(((10, 6), (1, 6)), ((10, 6, 4), (1, 2, 5)),
                          ((10, 6, 4, 1), (1, 2, 6, 10)))

    def is_weng_feasible(self):
        """
        Check whether the graph can be a member
        of a feasible family of classical graphs
        appearing in a classification from Weng99.
        """
        if self.d < 2:
            return False
        s = sqrt(2 * self.c[2])
        for q in sorted([-1-s, -1+s]):
            if not checkPrimePower(-q):
                continue
            beta = self.b[0] * (q-1) / (q**self.d - 1)
            if beta == -(1 + q**self.d)/2 and \
                    self.is_classicalWithParameters(q, (q-1)/2, beta):
                return True
        return False

    def kTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of intersection numbers ``k[0], k[1], ..., k[d]``,
        where ``d`` is the diameter of the graph.
        """
        self.k = rewriteTuple(self.k, expand = expand, factor = factor,
                              simplify = simplify)
        return self.k

    def kreinParameters(self, compute = True, expand = False,
                        factor = False, simplify = False):
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
                        if compute:
                            q[h, i, j] = full_simplify(
                                            sum(self.k[t] * self.omega[h, t]
                                                          * self.omega[i, t]
                                                          * self.omega[j, t]
                                                for t in range(self.d + 1))
                                            * self.m[i] * self.m[j] / self.n)
                        if not checkNonneg(q[h, i, j]):
                            raise InfeasibleError("Krein parameter "
                                                  "q[%d, %d, %d] negative"
                                                  % (h, i, j))
            self.q = q
        self.q.rewrite(expand = expand, factor = factor, simplify = simplify)
        return self.q

    def localGraph(self):
        """
        Return parameters of the local graph
        if it is known to be distance-regular.
        """
        if "local_graph" not in self.__dict__:
            self.check_2graph()
        if "local_graph" not in self.__dict__:
            self.check_localEigenvalues()
        assert "local_graph" in self.__dict__, \
            "local graph is not known to be distance-regular"
        return self.local_graph

    def match(self, *ial):
        """
        Check whether the graph matches any of the given intersection arrays.
        """
        for b, c in ial:
            assert len(b) == len(c), "parameter length mismatch"
            if self.d != len(b):
                continue
            if len(_solve([SR(l) == r for l, r
                          in zip(self.b[:-1] + self.c[1:],
                                 tuple(b) + tuple(c))], self.vars)) > 0:
                return True
        return False

    def mergeClasses(self, *args):
        adj = set(args)
        assert all(i >= 1 and i <= self.d for i in adj), \
            "indices out of bounds"
        b = [sum(self.k[j] for j in adj)]
        c = [1]
        cur = adj
        idx = set(range(1, self.d+1)).difference(adj)
        while len(idx) > 0:
            nxt = {i for i in idx if any(any(checkPos(self.p[h, i, j])
                                             for j in adj) for h in cur)}
            if len(nxt) == 0:
                break
            bi = {sum(sum(self.p[h, i, j] for j in adj) for i in nxt)
                  for h in cur}
            ci = {sum(sum(self.p[h, i, j] for j in adj) for i in cur)
                  for h in nxt}
            if len(bi) > 1 or len(ci) > 1:
                raise IndexError("merging classes %s does not yield "
                                 "a P-polynomial scheme" % sorted(adj))
            b.append(next(iter(bi)))
            c.append(next(iter(ci)))
            cur = nxt
            idx.difference_update(nxt)
        return DRGParameters(b, c)

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
                    raise InfeasibleError("multiplicities not integral")
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

    def set_vars(self, vars):
        """
        Set the order of the variables for eigenvalue sorting.
        """
        if vars is False:
            self.vars_ordered = False
        else:
            self.vars = tuple(vars) + tuple(x for x in self.vars
                                            if x not in vars)
            self.vars_ordered = True

    def show_distancePartitions(self, **options):
        """
        Show all distance partitions.
        """
        for h in range(self.d + 1):
            self.distancePartition(h).show(**options)

    def subs(self, exp, complement = False):
        """
        Substitute the given subexpressions in the parameters.
        """
        p = DRGParameters(*[[subs(x, exp) for x in l]
                            for l in self.intersectionArray()],
                          complement = complement)
        if "theta" in self.__dict__:
            p.theta = tuple(subs(th, exp) for th in self.theta)
        if "omega" in self.__dict__:
            p.omega = self.omega.subs(exp)
        if "P" in self.__dict__:
            p.P = self.P.subs(exp)
        if "Q" in self.__dict__:
            p.Q = self.Q.subs(exp)
        if "q" in self.__dict__:
            p.q = self.q.subs(exp)
            p.kreinParameters(compute = False)
        if "local_graph" in self.__dict__:
            try:
                p.local_graph = p.add_subgraph(self.local_graph.subs(exp),
                                               "local graph")
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = "local graph")
        if "complement" in self.__dict__:
            try:
                p.complement = self.complement.subs(exp, complement = p)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = "complement")
        for k, v in self.triple.items():
            p.triple[k] = v.subs(exp)
        for ia, part in self.subgraphs.items():
            try:
                p.add_subgraph(ia.subs(exp), part)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = part)
        for ia, part in self.distance_graphs.items():
            try:
                p.add_subgraph(ia.subs(exp), part)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part = part)
        return p

    def tripleEquations(self, u, v, w, krein = None, params = None,
                        solve = True, save = None):
        """
        Solve equations for triples of vertices at distances u, v, w.

        If krein is a list of triples, the corresponding equations are used;
        otherwise, equations for zero Krein parameters are used.
        If params is a dictionary mapping strings to triples,
        the keys will be used as variables mapped to triple intersection
        numbers for corresponding triples.
        If solve is False, only a list of equations and a set of variables
        is returned, without solving the equations.
        """
        assert checkPos(self.p[u, v, w]), \
            "no triple of vertices at distances %d, %d, %d" % (u, v, w)
        if solve and krein is None and params is None \
                and (u, v, w) in self.triple:
            return self.triple[u, v, w]
        if "Q" not in self.__dict__:
            self.dualEigenmatrix()
        if "q" not in self.__dict__:
            self.kreinParameters()
        out = []
        r = range(self.d+1)
        s = [[[Integer(1) if (h, i, j) in [(v, w, 0), (u, 0, w), (0, u, v)]
               else SR.symbol("%s_%d_%d_%d_%d_%d_%d" %
                              (self.prefix, u, v, w, h, i, j))
               for j in r] for i in r] for h in r]
        for i in r:
            for j in r:
                if self.p[u, i, j] == sum(s[i][j][t] for t in r
                                        if isinstance(s[i][j][t], Integer)):
                    for t in r:
                        if not isinstance(s[i][j][t], Integer):
                            s[i][j][t] = Integer(0)
                if self.p[v, i, j] == sum(s[i][t][j] for t in r
                                        if isinstance(s[i][t][j], Integer)):
                    for t in r:
                        if not isinstance(s[i][t][j], Integer):
                            s[i][t][j] = Integer(0)
                if self.p[w, i, j] == sum(s[t][i][j] for t in r
                                        if isinstance(s[t][i][j], Integer)):
                    for t in r:
                        if not isinstance(s[t][i][j], Integer):
                            s[t][i][j] = Integer(0)
        vars = set(x for x in sum([sum(l, []) for l in s], [])
                   if not isinstance(x, Integer))
        c = [[[len([t for t in r if not isinstance(s[i][j][t], Integer)])
               for j in r] for i in r],
             [[len([t for t in r if not isinstance(s[i][t][j], Integer)])
               for j in r] for i in r],
             [[len([t for t in r if not isinstance(s[t][i][j], Integer)])
               for j in r] for i in r]]
        q = []
        for h, ch in enumerate(c):
            for i, ci in enumerate(ch):
                for j, n in enumerate(ci):
                    if n == 1:
                        q.append((h, i, j))
        while len(q) > 0:
            l, i, j = q.pop()
            h, i, j = [(i, j, None), (i, None, j), (None, i, j)][l]
            if j is None:
                j = next(t for t in r if not isinstance(s[h][i][t], Integer))
                s[h][i][j] = self.p[u, h, i] - sum(s[h][i][t] for t in r
                                                   if t != j)
                c[1][h][j] -= 1
                c[2][i][j] -= 1
                if c[1][h][j] == 1:
                    q.append((1, h, j))
                if c[2][i][j] == 1:
                    q.append((2, i, j))
            elif i is None:
                i = next(t for t in r if not isinstance(s[h][t][j], Integer))
                s[h][i][j] = self.p[v, h, j] - sum(s[h][t][j] for t in r
                                                   if t != i)
                c[0][h][i] -= 1
                c[2][i][j] -= 1
                if c[0][h][i] == 1:
                    q.append((0, h, i))
                if c[2][i][j] == 1:
                    q.append((2, i, j))
            elif h is None:
                h = next(t for t in r if not isinstance(s[t][i][j], Integer))
                s[h][i][j] = self.p[w, i, j] - sum(s[t][i][j] for t in r
                                                   if t != h)
                c[0][h][i] -= 1
                c[1][j][j] -= 1
                if c[0][h][i] == 1:
                    q.append((0, h, i))
                if c[1][h][j] == 1:
                    q.append((1, h, j))
        for i in r:
            for j in r:
                l = sum(s[i][j][t] for t in r)
                if isinstance(l, Integer):
                    assert self.p[u, i, j] == l, \
                        "value of p[%d, %d, %d] exceeded" % (u, i, j)
                else:
                    out.append(self.p[u, i, j] == l)
                l = sum(s[i][t][j] for t in r)
                if isinstance(l, Integer):
                    assert self.p[v, i, j] == l, \
                        "value of p[%d, %d, %d] exceeded" % (v, i, j)
                else:
                    out.append(self.p[v, i, j] == l)
                l = sum(s[t][i][j] for t in r)
                if isinstance(l, Integer):
                    assert self.p[w, i, j] == l, \
                        "value of p[%d, %d, %d] exceeded" % (w, i, j)
                else:
                    out.append(self.p[w, i, j] == l)
        if krein is None:
            if save is None:
                save = True
            krein = []
            for h in range(1, self.d+1):
                for i in range(1, self.d+1):
                    for j in range(1, self.d+1):
                        if self.q[h, i, j] == 0:
                            krein.append((h, i, j))
        if krein:
            for h, i, j in krein:
                l = sum(sum(sum(self.Q[th, h] * self.Q[ti, i] *
                                self.Q[tj, j] * s[th][ti][tj]
                                for tj in r) for ti in r) for th in r)
                if isinstance(l, Integer):
                    assert l == 0, \
                        "Krein equation for (%d, %d, %d) not satisfied" % \
                        (h, i, j)
                else:
                    out.append(l == 0)
        if params:
            for a, (h, i, j) in params.items():
                x = SR.symbol(a)
                out.append(s[h][i][j] == x)
        vars.intersection_update(sum([sum(l, []) for l in s], []))
        if not solve:
            return (out, vars)
        sol = _solve(out, vars)
        assert len(sol) > 0, "system of equations has no solution"
        S = Array3D(self.d + 1)
        for h in r:
            for i in r:
                for j in r:
                    if isinstance(s[h][i][j], Integer):
                        S[h, i, j] = s[h][i][j]
                    else:
                        S[h, i, j] = s[h][i][j].subs(sol[0])
        if save:
            self.triple[u, v, w] = S
        return S

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
    substitute = subs
