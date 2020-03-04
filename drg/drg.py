# -*- coding: utf-8 -*-
from sage.combinat.q_analogues import q_int
from sage.functions.log import log
from sage.functions.other import ceil
from sage.functions.other import sqrt
from sage.matrix.constructor import Matrix
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.integer import Integer
from sage.rings.number_field.number_field import NumberField
from sage.symbolic.expression import Expression
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .assoc_scheme import ASParameters
from .assoc_scheme import PolyASParameters
from .aux import InfeasibleError
from .nonex import checkConditions
from .nonex import classicalFamilies
from .nonex import families
from .nonex import sporadic
from .partition import PartitionGraph
from .util import checklist
from .util import checkNonneg
from .util import checkPos
from .util import checkPrimePower
from .util import full_simplify
from .util import hard_ceiling
from .util import hard_floor
from .util import integralize
from .util import is_constant
from .util import is_squareSum
from .util import pair_keep
from .util import pair_swap
from .util import rewriteExp
from .util import subs
from .util import symbol
from .util import variables

check_DRGParameters = []
check = checklist(check_DRGParameters, PolyASParameters._checklist)


class DRGParameters(PolyASParameters):
    """
    A class for parameters of a distance-regular graph
    and checking their feasibility.
    """

    ANTIPODAL = "antipodal quotient"
    ARRAY = "intersection array"
    BIPARTITE = "bipartite half"
    DUAL_INTEGRAL = False
    DUAL_MATRIX = "Q"
    DUAL_PARAMETER = "Krein parameter"
    DUAL_PARTS = "eigenspaces"
    DUAL_SIZES = "multiplicities"
    DUAL_SYMBOL = "q"
    MATRIX = "P"
    METRIC = True
    OBJECT = "distance-regular graph"
    OBJECT_LATEX = "distance-regular graph"
    PARAMETER = "intersection number"
    PART = "relation"
    PARTS = "relations"
    PART_SCHEME = "distance-%s graph"
    PTR = pair_keep
    QTR = pair_swap
    SIZE = "valency"
    SIZES = "valencies"
    SYMBOL = "p"

    _checklist = check_DRGParameters

    def __init__(self, b, c=None, alpha=None, beta=None,
                 complement=None, order=None):
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
        self._init_storage()
        if isinstance(b, ASParameters):
            o = b.is_pPolynomial()
            assert o, "scheme not P-polynomial"
            self._.d = b._.d
            if order is None:
                order = o[0]
            else:
                order = self._reorder(order)
            assert order in o, "scheme not P-polynomial for given order"
            PolyASParameters.__init__(self, b, order=order)
            self._check_intersectionArray()
            if isinstance(b, DRGParameters):
                return
        else:
            if alpha is not None:
                if beta is not None:
                    self._.d = Integer(b)
                    q = c
                    b = [(q_int(self._.d, q) - q_int(i, q)) *
                         (beta - alpha * q_int(i, q)) for i in range(self._.d)]
                    c = [q_int(i, q) * (1 + alpha * q_int(i-1, q))
                         for i in range(1, self._.d + 1)]
                elif b - c == 1:
                    self._.d = Integer(1)
                    b, c = (b, ), (1, )
                else:
                    self._.d = Integer(2)
                    b, c = (b, b-c-1), (1, alpha)
            else:
                self._.d = Integer(len(b))
            PolyASParameters.__init__(self, b, c)
            self._check_intersectionArray()
            self._.k = tuple(self._init_multiplicities())
            self._.p = Array3D(self._.d + 1)
            self._compute_parameters(self._.p, self._.k)
        self._compute_imprimitivity()
        if not isinstance(b, ASParameters):
            self.check_handshake()
        self._compute_complement(complement)

    def _check_intersectionArray(self):
        """
        Check the basic restrictions on the intersection array.
        """
        assert all(checkNonneg(self._.b[i] - self._.b[i+1])
                   for i in range(self._.d)), \
            "b sequence not non-ascending"
        assert all(checkNonneg(self._.c[i+1] - self._.c[i])
                   for i in range(self._.d)), \
            "c sequence not non-descending"
        if any(self._.b[j] < self._.c[i]
               for i in range(self._.d+1) for j in range(self._.d-i+1)):
            raise InfeasibleError("b[j] < c[i] with i+j <= d",
                                  ("BCN", "Proposition 4.1.6.(ii)"))

    def _check_parameter(self, h, i, j, v, integral=True,
                         name=None, sym=None):
        """
        Check for the feasibility
        of an intersection number or Krein parameter.

        The parameter is checked for nonnegativity,
        and, if requested, also for integrality.
        """
        return PolyASParameters._check_parameter(self, h, i, j, v,
                                                 integral=integral,
                                                 name=name, sym=sym)

    def _complement(self):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        return PolyASParameters._complement(self, self._.k, self._.p)

    def _compute_kreinParameters(self, expand=False, factor=False,
                                 simplify=False):
        """
        Compute the Krein parameters.
        """
        if not self._has("m"):
            self.multiplicities(expand=expand, factor=factor,
                                simplify=simplify)
        if not self._has("q"):
            q = Array3D(self._.d + 1)
            self._compute_dualParameters(q, self._.k, self._.m, self.PTR)
            self._.q = q

    def _compute_kTable(self, expand=False, factor=False, simplify=False):
        """
        Compute the valencies of the relations.

        Does nothing, as they are already computed
        for distance-regular graphs.
        """
        pass

    def _compute_multiplicities(self, expand=False, factor=False,
                                simplify=False):
        """
        Compute the multiplicities of the eigenspaces.
        """
        if not self._has("m"):
            self._.m = self._compute_sizes(self._.k, expand=expand,
                                           factor=factor, simplify=simplify)

    def _compute_pTable(self, expand=False, factor=False,
                        simplify=False):
        """
        Compute the intersection numbers.

        Does nothing, as they are already computed
        for distance-regular graphs.
        """
        pass

    def _copy_cosineSequences(self, p):
        """
        Obtain the cosine sequences from the eigenmatrix.
        """
        PolyASParameters._copy_cosineSequences(self, p.eigenmatrix())

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return DRGParameters

    def _init_array(self, b, c):
        """
        Initialize the intersection array while checking for integrality.
        """
        try:
            self._.c = (Integer(0), ) + tuple(map(integralize, c))
        except TypeError:
            raise InfeasibleError("c sequence not integral")
        try:
            self._.b = tuple(map(integralize, b)) + (Integer(0), )
        except TypeError:
            raise InfeasibleError("b sequence not integral")

    def _is_trivial(self):
        """
        Check whether the distance-regular graph is trivial
        for the purposes of feasibility checking.

        Returns ``True`` if the graph has diameter one or valency two.
        """
        return PolyASParameters._is_trivial(self) or self._.k[1] == 2

    @staticmethod
    def _subconstituent_name(h):
        """
        Return a properly formatted ordinal for the given subconstituent.
        """
        if h == 1:
            return "local graph"
        else:
            return PolyASParameters._subconstituent_name(h)

    def _subs(self, exp, p, seen):
        """
        Substitute the given subexpressions in the parameters.
        """
        p, new = PolyASParameters._subs(self, exp, p, seen)
        if new:
            if self._has("q") and not p._has("q"):
                p._.q = self._.q.subs(*exp)
                p._check_parameters(p._.q, integral=self.DUAL_INTEGRAL,
                                    name=self.DUAL_PARAMETER,
                                    sym=self.DUAL_SYMBOL)
        return p

    def complementaryGraph(self):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        assert self._.d == 2 and checkPos(self._.b[0] - self._.c[2]), \
            "the complement is not distance-regular"
        return self._.complement

    def distancePartition(self, h=0):
        """
        Return the diagram of the distance partition
        corresponding to a vertex (if h = 0)
        or two vertices at distance h.
        """
        return PartitionGraph(self, h)

    def eigenvalues(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the eigenvalues of the graph.
        """
        return self._compute_eigenvalues(self._.p, expand=expand,
                                         factor=factor, simplify=simplify)

    def genPoly_parameters(self, expand=False, factor=False, simplify=False):
        """
        Determine the parameters of the generalized polygon
        whose collinearity graph has matching parameters.
        """
        try:
            t = rewriteExp(self._.c[self._.d] - 1, expand=expand,
                           factor=factor, simplify=simplify)
            s = rewriteExp(integralize(self._.b[0] / self._.c[self._.d]),
                           expand=expand, factor=factor, simplify=simplify)
            st = s * t
            if any(c != 1 or b != st
                   for b, c in zip(self._.b[1:-1], self._.c[1:-1])):
                raise TypeError
            return (2*self._.d, s, t)
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
        assert all(x >= 0 and x <= self._.d for x in [h, i1, j1, i2, j2]), \
            "distance not in feasible range"
        if abs(i1 - i2) > 1 or abs(j1 - j2) > 1:
            return False
        for t, d in (((h, i1, j1), (i2, j2, 1)), ((h, i2, j2), (i1, j1, 1))):
            if any(x == 0 for x in self.triple_generator(t, d)):
                return False
        return True

    def is_bilinearForms(self):
        """
        Check whether the graph can be a bilinear forms graph
        of diameter at least 2.
        """
        s = symbol("__s")
        for q in sorted([s.subs(ss) for ss in
                         _solve(s*(s+1) == self._.c[2], s)], reverse=True):
            if not checkPrimePower(q):
                continue
            beta = self._.b[0] * (q-1) / (q**self._.d - 1)
            try:
                integralize(log(integralize(beta + 1), q))
            except TypeError:
                continue
            if self.is_classicalWithParameters(q, q-1, beta):
                return True
        return False

    def is_classical(self):
        """
        Check whether the graph is classical,
        and return all sets of classical parameters if it is.
        """
        if not self._has("classical"):
            clas = []
            bs = set()
            if self._.d == 2:
                e = self._.c[2] - self._.a[1] - 2
                d = sqrt(4*self._.b[1] + e**2)
                bs.add((e+d)/2)
                bs.add((e-d)/2)
            elif all(self._.a[i] == self._.a[1] * self._.c[i]
                     for i in range(2, self._.d+1)):
                bs.add(self._.c[2] - 1)
                bs.add(-self._.a[1] - 1)
            elif self._.d >= 3:
                d = self._.a[1] * self._.c[3] - self._.a[3]
                if d != 0:
                    bs.add((self._.a[2]*self._.c[3]
                            - self._.c[2]*self._.a[3]) / d)
            for b in bs:
                if b in [0, -1]:
                    continue
                alpha = self._.c[2] / (b+1) - 1
                beta = self._.k[1] / q_int(self._.d, b)
                if all(self._.b[i] ==
                       (q_int(self._.d, b) - q_int(i, b)) *
                       (beta - alpha * q_int(i, b)) and
                       self._.c[i+1] ==
                       q_int(i+1, b) * (1 + alpha * q_int(i, b))
                       for i in range(self._.d)):
                    clas.append((self._.d, b, alpha, beta))
            self._.classical = False if len(clas) == 0 else clas
        return self._.classical

    def is_classicalWithParameters(self, b, alpha, beta):
        """
        Check whether the graph can have the specified classical parameters.
        """
        p = DRGParameters(self._.d, b, alpha, beta)
        return len(_solve([SR(l) == r for l, r in
                           zip(self._.b + self._.c, p._.b + p._.c)],
                          self._.vars)) > 0

    def is_dualPolar2Aodd(self):
        """
        Check whether the graph can be a dual polar graph ^2A_{2d-1}(-b)
        of diameter at least 2.
        """
        if self._.d < 2:
            return False
        q = self._.c[2] - 1
        if not checkPrimePower(q):
            return False
        beta = self._.b[0] * (q-1) / (q**self._.d - 1)
        return q == beta**2 and self.is_classicalWithParameters(q, 0, beta)

    def is_grassmann(self):
        """
        Check whether the graph can be a Grassmann graph
        of diameter at least 2.
        """
        if self._.d < 2:
            return False
        s = sqrt(self._.c[2])
        for q in sorted([-1+s, -1-s], reverse=True):
            if not checkPrimePower(q):
                continue
            beta = self._.b[0] * (q-1) / (q**self._.d - 1)
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
        b1 = [SR(x) == (self._.d-i) * (2*(self._.d-i) - 1)
              for i, x in enumerate(self._.b[:-1])]
        b2 = [SR(x) == (self._.d-i) * (2*(self._.d-i) + 1)
              for i, x in enumerate(self._.b[:-1])]
        c = [SR(x) == (i+1) * (2*i + 1) for i, x in enumerate(self._.c[1:])]
        return len(_solve(b1 + c, self._.vars)) > 0 or \
            len(_solve(b2 + c, self._.vars)) > 0

    def is_hamming(self):
        """
        Check whether the graph can be a Hamming (or Doob) graph.
        """
        z = symbol()
        return len(_solve([SR(x) == (self._.d-i) * z
                           for i, x in enumerate(self._.b[:-1])] +
                          [SR(x) == i+1 for i, x in enumerate(self._.c[1:])],
                          self._.vars + (z, ))) > 0

    def is_hermitean(self):
        """
        Check whether the graph can be a Hermitean forms graph
        of diameter at least 2.
        """
        s = symbol("__s")
        for q in sorted([s.subs(ss) for ss in
                         _solve(s*(s+1) == self._.c[2], s)]):
            if not checkPrimePower(-q):
                continue
            beta = self._.b[0] * (q-1) / (q**self._.d - 1)
            if beta+1 == -q**self._.d and \
                    self.is_classicalWithParameters(q, q-1, beta):
                return True
        return False

    def is_johnson(self):
        """
        Check whether the graph can be a Johnson graph.
        """
        z = symbol()
        return len(_solve([SR(x) == (self._.d-i) * (self._.d - z - i)
                           for i, x in enumerate(self._.b[:-1])] +
                          [SR(x) == (i+1)**2 for i, x
                           in enumerate(self._.c[1:])],
                          self._.vars + (z, ))) > 0

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
        if self._.d < 2:
            return False
        s = sqrt(2 * self._.c[2])
        for q in sorted([-1-s, -1+s]):
            if not checkPrimePower(-q):
                continue
            beta = self._.b[0] * (q-1) / (q**self._.d - 1)
            if beta == -(1 + q**self._.d)/2 and \
                    self.is_classicalWithParameters(q, (q-1)/2, beta):
                return True
        return False

    def localGraph(self, compute=False):
        """
        Return parameters of the local graph
        if it is known to be distance-regular.

        If compute is set to True,
        then the relevant triple intersection numbers will be computed.
        """
        return self.subconstituent(1, compute=compute)

    def merge(self, *args, **kargs):
        """
        Return parameters of a graph obtained
        by merging specified relations.
        """
        return PolyASParameters.merge(self, self._.k, self._.p,
                                      *args, **kargs)

    def reorderEigenspaces(self, *order):
        """
        Specify a new order for the eigenspaces.
        """
        self.reorderEigenvalues(*order)

    def reorderEigenvalues(self, *order):
        """
        Specify a new order for the eigenvalues and return it.
        """
        order = PolyASParameters.reorderEigenvalues(self, *order)
        PolyASParameters.reorderEigenspaces(self, *order)
        return self._.theta

    def reorderParameters(self, *order):
        """
        Specify a new order for the parameters and return them.
        """
        order = self._reorder(order)
        assert order in self.is_pPolynomial(), \
            "scheme not P-polynomial for the given order"
        PolyASParameters.reorderRelations(self, *order)
        PolyASParameters.reorderParameters(self, self._.p, *order)
        return self.parameterArray()

    def reorderRelations(self, *order):
        """
        Specify a new order for the relations.
        """
        self.reorderParameters(*order)

    def show_distancePartitions(self, **options):
        """
        Show all distance partitions.
        """
        for h in range(self._.d + 1):
            self.distancePartition(h).show(**options)

    def subconstituent(self, h, compute=False):
        """
        Return parameters of the h-th subconstituent
        if it is known to form an association scheme.
        If the resulting scheme is P-polynomial,
        the parameters are returned as such.

        If compute is set to True,
        then the relevant triple intersection numbers will be computed.
        """
        if h == 1:
            if self._.subconstituents[h] is None:
                self.check_2graph()
            if self._.subconstituents[h] is None:
                self.check_localEigenvalues()
        if self._.subconstituents[h] is None:
            subc, rels = PolyASParameters.subconstituent(self, h,
                                                         compute=compute,
                                                         return_rels=True)
            if subc is not None and len(rels) > 1 and rels[1] == 1 \
                    and subc.is_pPolynomial() \
                    and tuple(range(subc._.d+1)) \
                    in subc._.pPolynomial_ordering:
                self._.subconstituents[h] = DRGParameters(
                    subc, order=tuple(range(subc._.d+1)))
        return self._.subconstituents[h]

    def subs(self, *exp, **kargs):
        """
        Substitute the given subexpressions in the parameters.
        """
        return self._subs(exp,
                          DRGParameters(*[[subs(x, *exp) for x in l] for l
                                          in self.intersectionArray()]),
                          kargs.get("seen", {}))

    def valency(self):
        """
        Return the valency of the graph.
        """
        return self._.b[0]

    @check(1)
    def check_2graph(self):
        """
        For a strongly regular or Taylor graph,
        check whether a regular 2-graph can be derived.
        """
        if self._.d == 2 and \
                self._.n == 2*(2*self._.b[0] - self._.a[1] - self._.c[2]):
            mu = self._.b[0] - self._.c[2]
            if checkPos(mu):
                self.add_subscheme(DRGParameters((2*mu, self._.b[1]),
                                                 (Integer(1), mu)),
                                   "2-graph derivation")
        elif self._.d == 3 and self._.antipodal and \
                self._.r == 2 and self._.a[1] > 0:
            try:
                mu = integralize(self._.a[1] / 2)
                n = integralize(self._.n / 4)
            except TypeError:
                raise InfeasibleError("Taylor graph with a[1] > 0 odd "
                                      "or cover of K_n with n odd",
                                      ("BCN", "Thm. 1.5.3."))
            self._.subconstituents[1] = \
                self.add_subscheme(DRGParameters((self._.a[1], n - mu - 1),
                                                 (Integer(1), mu)),
                                   "local graph")

    @check(1)
    def check_classical(self):
        """
        Check whether the graph has classical parameters for which
        nonexistence has been shown as a part of an infinite family.
        """
        if self._.d >= 3:
            s = symbol("__s")
            sols = sorted([s.subs(ss) for ss in
                           _solve((s+1)*(self._.a[1]+1)
                                  - s*(s+1)*(self._.c[2]-1)/2
                                  == self._.b[0], s)])
            x = hard_ceiling(sols[0], Integer(0))
            y = hard_floor(sols[-1], Integer(-1))
            try:
                q = integralize(sqrt(self._.c[2]) - 1)
                r = hard_floor(((self._.a[1] + 1)
                                - (self._.b[0] - self._.b[2]) / (q+2))
                               / (q+1) + 1)
                if q == 0:
                    t = r
                else:
                    t = hard_floor(
                        ((self._.a[1] + 1)/(self._.c[2] - 1) + 1) / 2)
                if q >= 2 and y >= 2 and x <= y and x <= r and x <= t \
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
                diam = cl[0] == self._.d
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
                    raise InfeasibleError(refs=ref)
        if self._.d >= 3 and self._.a[1] == 0 and self._.a[2] > 0 and \
                self._.c[2] > 2:
            raise InfeasibleError("classical with a[1] = 0, "
                                  "a[2] > 0 and c[2] > 2",
                                  ("PanWeng09", "Thm. 2.1."))
        if self._.d >= 4 and self._.a[1] > 0 and self._.c[2] > 1 and \
                any(b < 0 for d, b, alpha, beta in clas) and \
                not self.is_dualPolar2Aodd() and not self.is_hermitean() \
                and not self.is_weng_feasible():
            raise InfeasibleError("classical with b < 0",
                                  ("Weng99", "Thm. 10.3."))
        if self._.d < 3:
            return
        for d, b, alpha, beta in clas:
            try:
                b = integralize(b)
            except TypeError:
                continue
            if not (is_constant(alpha) and is_constant(beta)):
                continue
            if alpha == b and ((b == 6 and d >= 7) or
                               (b >= 10 and d >= 6 and
                                not checkPrimePower(b))) \
                    and beta + 1 == (b**(d+1) - 1) / (b - 1):
                raise InfeasibleError("not a Grassmann graph",
                                      ("GavrilyukKoolen18", "Thm. 1.2."))
            if x <= y and alpha >= 1 and alpha == b - 1 \
                    and y >= (b**d-1)/(b-1):
                t = hard_floor((1 + self._.a[1] + b**2 * (b**2 + b + 1))
                               / (b**3 + b**2 + 2*b - 1))
                if x <= t and (d != 3 or b != 2 or
                               (x <= 7 and y >= 7 and t >= 7)) and \
                        not self.is_bilinearForms():
                    raise InfeasibleError("not a bilinear forms graph",
                                          ("Metsch99", "Prop. 2.2."))

    @check(1)
    def check_combinatorial(self):
        """
        Check for various combinatorial conditions.
        """
        self._.maxCliques = False
        if checkPos(self._.b[0] - 2):
            if self._.b[1] == 1 and \
                    (self._.d != 2 or self._.c[2] != self._.b[0]):
                raise InfeasibleError("b1 = 1 and not a cycle "
                                      "or cocktail party graph")
            for i in range(2, self._.d):
                if checkPos(self._.b[i] - 1):
                    continue
                if self._.d >= 3*i or \
                        any(self._.c[j] > 1 or self._.a[j] >= self._.c[i+j]
                            for j in range(1, self._.d - i + 1)) or \
                        (self._.d >= 2*i and self._.c[2*i] == 1) or \
                        any(self._.a[j] > 0 for j
                            in range(1, self._.d - 2*i + 1)) or \
                        (i < self._.d and
                         (self._.c[2] - 1)*self._.a[i+1] + self._.a[1]
                         > self._.a[i]):
                    raise InfeasibleError("Godsil's diameter bound "
                                          "not reached",
                                          ("BCN", "Lem. 5.3.1."))
        if self._.d >= 3 and self._.c[2] > 1 and \
                3*self._.c[2] > 2*self._.c[3] and \
                (self._.d != 3 or self._.b[2] + self._.c[2] > self._.c[3]):
            raise InfeasibleError("intersection number c[3] too small",
                                  ("BCN", "Thm. 5.4.1."))
        for i in range(2, self._.d):
            if self._.b[i] != self._.b[1]:
                break
            if self._.c[i] != 1:
                raise InfeasibleError("impossible arrangement of lines",
                                      ("BCN", "Thm. 5.4.4."))
        if self._.a[1] > 0 and \
                any(self._.a[1] + 1 > 2*self._.a[i] or
                    ((i < self._.d-1 or self._.a[self._.d] > 0 or
                     (self._.d > 2 and self._.b[self._.d-1] > 1)) and
                     self._.a[1] + 1 > self._.a[i] + self._.a[i+1]) or
                    self._.a[1] + 2 > self._.b[i] + self._.c[i+1]
                    for i in range(1, self._.d)):
            raise InfeasibleError("counting argument",
                                  ("BCN", "Prop. 5.5.1."))
        if self._.d >= 4 and set(self._.a[1:4]) == {0} and \
                self._.c[2:5] == (1, 2, 3):
            try:
                integralize(self._.b[1] * self._.b[2] * self._.b[3] / 4)
                integralize(self._.n * self._.k[4] / 36)
            except TypeError:
                raise InfeasibleError("handshake lemma not satisfied "
                                      "for Pappus subgraphs", "Koolen92")
        if self._.d >= 2:
            if self._.a[1] == 0 and any(2*self._.a[i] > self._.k[i]
                                        for i in range(2, self._.d+1)):
                raise InfeasibleError(u"Turán's theorem",
                                      ("BCN", "Prop. 5.6.4."))
            for h in range(1, self._.d + 1):
                for i in range(self._.d + 1):
                    for j in range(abs(h-i), min(self._.d, h+i) + 1):
                        if self._.p[h, i, j] > 0:
                            ppm = self._.p[h, i+1, j-1] \
                                if i < self._.d and j > 0 else 0
                            ppz = self._.p[h, i+1, j] if i < self._.d else 0
                            ppp = self._.p[h, i+1, j+1] \
                                if i < self._.d and j < self._.d else 0
                            pzm = self._.p[h, i, j-1] if j > 0 else 0
                            pzp = self._.p[h, i, j+1] if j < self._.d else 0
                            pmm = self._.p[h, i-1, j-1] \
                                if i > 0 and j > 0 else 0
                            pmz = self._.p[h, i-1, j] if i > 0 else 0
                            pmp = self._.p[h, i-1, j+1] \
                                if i > 0 and j < self._.d else 0
                            if ppm + ppz + ppp < self._.b[i] or \
                                    pzm + self._.p[h, i, j] + pzp \
                                    < self._.a[i] + 1 or \
                                    pmm + pmz + pmp < self._.c[i]:
                                raise InfeasibleError("counting argument",
                                                      "Lambeck93")
            if not self._.antipodal:
                ka = self._.k[self._.d] * self._.a[self._.d]
                kka = self._.k[self._.d] * \
                    (self._.k[self._.d] - self._.a[self._.d] - 1)
                try:
                    if (self._.k[1] > ka and self._.k[1] > kka) or \
                        (self._.k[2] > kka and
                         (self._.k[1] > ka or
                          self._.k[1] > self._.a[self._.d] *
                          (self._.a[1] + 2 - self._.a[self._.d])) and
                         (self._.b[self._.d-1] > 1 or
                          not (self._.a[1] + 1 == self._.a[self._.d]) or
                          integralize(self._.k[1]/self._.a[self._.d])
                            > self._.k[self._.d])):
                        raise TypeError
                except TypeError:
                    raise InfeasibleError("valency of last relation too small",
                                          ("BCN", "Prop. 5.6.1."))
                if self._.d >= 3 and self._.k[1] == \
                        self._.k[self._.d] * (self._.k[self._.d] - 1) and \
                        self._.k[self._.d] > self._.a[self._.d] + 1:
                    raise InfeasibleError("valency of last relation too small",
                                          ("BCN", "Prop. 5.6.3."))
            c2one = self._.c[2] == 1
            case3 = self._.b[self._.d-1] == 1 and \
                self._.a[self._.d] == self._.a[1] + 1
            case4 = False
            if self._.p[2, self._.d, self._.d] == 0:
                try:
                    ad1 = self._.a[self._.d] + 1
                    bad1 = self._.b[self._.d-1] - ad1
                    integralize(self._.k[self._.d] / ad1)
                    if self._.a[self._.d] > self._.a[1] + 1 or bad1 > 0 or \
                            self._.b[self._.d-1] > self._.c[2] or \
                            (bad1 == 0 and self._.a[self._.d] > 0) \
                            or (self._.b[self._.d-1] > 1 and
                                ad1 > self._.a[1]):
                        raise TypeError
                    case4 = self._.b[self._.d-1] <= 1 and \
                        self._.a[self._.d] > 0
                except TypeError:
                    raise InfeasibleError("p[2,d,d] = 0",
                                          ("BCN", "Prop. 5.7.1."))
            if c2one or case3 or case4 or self._.a[1] == 1 or \
                    (self._.c[2] == 2 and
                        self._.a[1]*(self._.a[1]+3)/2 > self._.k[1]) or \
                    any(self._.b[i] > 1 and self._.c[i] == self._.b[1]
                        for i in range(2, self._.d+1)):
                if case3:
                    try:
                        integralize(self._.k[self._.d] / (self._.a[1]+2))
                    except TypeError:
                        raise InfeasibleError("last relation a union "
                                              "of cliques, a[1]+2 does not "
                                              "divide k[d]",
                                              ("BCN", "Prop. 4.3.2.(iii)"))
                try:
                    kl = integralize(self._.k[1] / (self._.a[1]+1))
                    vkll = integralize(self._.n*kl / (self._.a[1]+2))
                except TypeError:
                    raise InfeasibleError("handshake lemma not satisfied "
                                          "for maximal cliques")
                if self._.a[1] * self._.c[2] > self._.a[2] or \
                        (c2one and
                         1 + self._.b[1]*(self._.b[1]+1) *
                            (self._.a[1]+2)/(1 + self._.a[1]) > vkll):
                    raise InfeasibleError("graph with maximal cliques",
                                          ("BCN", "Prop. 4.3.3."))
                self._.maxCliques = True

    @check(1)
    def check_conference(self):
        """
        Check whether a conference graph can exist.
        """
        if self._.d == 2 and all(isinstance(x, Integer)
                                 for x in self._.b + self._.c) and \
                self._.b[1] == self._.c[2] and \
                self._.b[0] == 2*self._.b[1] and \
                (self._.n % 4 != 1 or not is_squareSum(self._.n)):
            raise InfeasibleError("conference graph must have order a sum "
                                  "of two squares with residue 1 (mod 4)")

    @check(1)
    def check_geodeticEmbedding(self):
        """
        For a graph with intersection array {2b, b, 1; 1, 1, 2b},
        check whether there exists an embedding
        into a geodetic graph of diameter 2.
        """
        if self._.d == 3 and self._.b[0] == self._.c[3] and \
                self._.b[2] == 1 and self._.c[2] == 1 and \
                self._.b[0] == 2*self._.b[1] and self._.b[0] > 4:
            raise InfeasibleError("no embedding into a geodetic graph "
                                  "of diameter 2", ("BCN", "Prop. 1.17.3."))

    @check(1)
    def check_2design(self):
        """
        For an graph with intersection array
        {r*mu+1, (r-1)*mu, 1; 1, mu, r*mu+1},
        check whether a corresponding 2-design exists.
        """
        if self._.d == 3 and self._.antipodal \
                and isinstance(self._.r, Integer) \
                and isinstance(self._.b[0], Integer) \
                and self._.b[0] - 1 == self._.b[1] + self._.c[2]:
            ok = True
            if self._.r % 2 == 0:
                ok = is_squareSum(self._.b[0])
            elif self._.b[0] % 2 == 0:
                ok = Integers(self._.r)(self._.b[0]).is_square() and \
                    Integers(self._.b[0])(self._.r if self._.r % 4 == 1
                                          else -self._.r).is_square()
            if not ok:
                raise InfeasibleError("no corresponding 2-design",
                                      ("BCN", "Prop. 1.10.5."))

    @check(1)
    def check_hadamard(self):
        """
        For a graph with intersection array {2c, 2c-1, c, 1; 1, c, 2c-1, 2c},
        with c > 1, check whether c is even.
        """
        if self._.d == 4 and self._.b[0] > 2 and self._.bipartite \
                and self._.antipodal and self._.r == 2:
            try:
                integralize(self._.c[2]/2)
            except TypeError:
                raise InfeasibleError("Hadamard graph with odd c[2]",
                                      ("BCN", "Cor. 1.8.2."))

    @check(1)
    def check_antipodal(self):
        """
        For an antipodal cover of even diameter at least 4,
        check whether its quotient satisfies necessary conditions
        for the existence of a cover.
        """
        if self._.antipodal and self._.d >= 4 and self._.d % 2 == 0:
            q = self.antipodalQuotient()
            try:
                integralize(sum(q._.p[q._.d, i, q._.d-i]
                                for i in range(1, q._.d))
                            / self._.r)
                if self._.d == 4 and self._.c[2] == 1:
                    kl = q._.b[0] / (q._.a[1] + 1)
                    if self._.r > kl:
                        raise TypeError
                    integralize(q._.n*kl / (q._.a[1]+2))
            except TypeError:
                raise InfeasibleError("quotient cannot have covers "
                                      "of even diameter",
                                      ("BCN", "Prop. 4.2.7."))

    @check(1)
    def check_genPoly(self):
        """
        For a graph with parameters of a generalized polygon,
        check whether its parameters satisfy the restrictions.
        """
        if not self._has("maxCliques"):
            self.check_combinatorial()
        if not self._.maxCliques:
            return
        g, s, t = self.genPoly_parameters()
        if g:
            try:
                st = integralize(s*t)
                st2 = 2*st
            except TypeError:
                st = st2 = Integer(1)
            if g not in [2, 4, 6, 8, 12] or \
                    (s > 1 and t > 1 and
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
        if self._.antipodal and self._.d == 3 and \
                self._.b[0] == (self._.r - 1) * (self._.c[2] + 1):
            s = self._.r - 1
            t = self._.c[2] + 1
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

    @check(1)
    def check_clawBound(self):
        """
        Check the claw bound for strongly regular graphs.
        """
        if not self._has("theta"):
            self.eigenvalues()
        if self._.d == 2:
            s, r = sorted(self._.theta[1:])
            if self._.c[2] not in [s*s, s*(s+1)] and \
                    2*(r+1) > s*(s+1)*(self._.c[2]+1):
                raise InfeasibleError("claw bound exceeded",
                                      "BrouwerVanLint84")

    @check(1)
    def check_terwilliger(self):
        """
        Check whether the graph is a Terwilliger graph
        and whether existence conditions are satisfied in this case,
        or if the Terwilliger diameter bound is satisfied otherwise.
        """
        if not self._has("theta"):
            self.eigenvalues()
        small = (self._.d == 2 and 50 * self._.c[2] > self._.n) or \
                (self._.d >= 3 and 50 * (self._.c[2] - 1) > self._.b[0])
        if self._.d >= 2 and isinstance(self._.b[0], Integer) and \
                isinstance(self._.a[1], Integer) and \
                isinstance(self._.c[2], Integer):
            if all(isinstance(th, Integer) for th in self._.theta):
                th = min(self._.theta)
            else:
                th = None
            if self._.b[0] == 10 and self._.a[1] == 3 and \
                    (self._.c[2] == 2 or self._.b[2] > self._.c[2]):
                s = 4
            elif th is not None and self._.a[1] != 2 and \
                    -1 - self._.b[1]/(th+1) < self._.a[1]:
                s = ceil(self._.b[0] / self._.a[1])
            else:
                s = ceil(self._.b[0] / (self._.a[1] + 1))
            v = 2*(s*(self._.a[1] + 1) - self._.b[0]) / \
                (s*(s-1)) + 1 - self._.c[2]
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
        aab = self._.a[1]*(self._.a[1]-1) / self._.b[1]
        aabc = self._.c[2]-1 > aab
        if self._.c[2] >= 2 and (small or aabc or
                                 (self._.d >= 3 and self._.c[3] > 1
                                  and 2*self._.c[2] > self._.c[3])):
            if aabc and aab < self._.b[2] - self._.b[1] + self._.a[1] + 1:
                raise InfeasibleError("Quadrangle per claw bound "
                                      "exceeded", ("BCN", "Thm. 5.2.1.(ii)"))
            elif any(self._.c[i] + self._.a[1] + self._.b[i+1] + 2
                     > self._.b[i] + self._.c[i+1]
                     for i in range(self._.d)):
                raise InfeasibleError("Terwilliger's diameter bound "
                                      "not reached", ("BCN", "Thm. 5.2.1."))

    @check(1)
    def check_secondEigenvalue(self):
        """
        For a graph with the second eigenvalue equal to b[1]-1,
        check whether it belongs to the characterization.
        """
        if not self._has("theta"):
            self.eigenvalues()
        if (self._.b[1] - 1) in self._.theta:
            if (self._.d != 2 or all(th != -2 for th in self._.theta)
                    or (self._.b[1] != 1 and self._.n > 28)) and \
                    self._.c[2] != 1 and \
                    not (self.is_hamming() or
                         self.is_locallyPetersen() or
                         self.is_johnson() or
                         self.is_halfCube() or
                         self.match(((27, 10, 1), (1, 10, 27)))):
                raise InfeasibleError("theta[1] = b[1]-1, "
                                      "not in characterization",
                                      ("BCN", "Thm. 4.4.11."))

    @check(1)
    def check_localEigenvalues(self):
        """
        For a graph of diameter at least 3,
        check whether the eigenvalues of the local graph
        are in the allowed range.
        """
        if not self._has("m"):
            self.multiplicities()
        if self._.d >= 3 and not self.match(((5, 2, 1), (1, 2, 5))) and \
                all(is_constant(th) for th in self._.theta
                    if th != self._.k[1]):
            th1, i = max((th, h) for h, th in enumerate(self._.theta)
                         if th != self._.k[1])
            thd, j = min((th, h) for h, th in enumerate(self._.theta)
                         if th != self._.k[1])
            bm = -1 - self._.b[1]/(th1+1)
            bp = -1 - self._.b[1]/(thd+1)
            if (bm > -2 and self._.c[2] != 1) or \
                    (bp < 1 and self._.a[1] != 0):
                raise InfeasibleError("local eigenvalues "
                                      "not in allowed range",
                                      ("BCN", "Thm. 4.4.3."))
            if not self._.bipartite:
                mu = self._.a[1] + bp*bm
                bd = self._.k[1] * mu - \
                    (self._.a[1] - bp) * (self._.a[1] - bm)
                fb = self._.k[1] * self._.a[1] * self._.b[1] + \
                    (th1 * (self._.a[1] + 1) + self._.k[1]) * \
                    (thd * (self._.a[1] + 1) + self._.k[1])
                if bd > 0:
                    raise InfeasibleError("bound on local eigenvalues "
                                          "exceeded", u"JurišićKoolen00")
                if fb < 0:
                    raise InfeasibleError("fundamental bound exceeded",
                                          "JKT00")
                elif bd == 0 or fb == 0:
                    try:
                        integralize(self._.c[2]*mu/2)
                        if self._.c[2] < mu + 1:
                            raise TypeError
                    except TypeError:
                        raise InfeasibleError("local graph strongly regular",
                                              u"JurišićKoolen00")
                    if self._.d == 4 and self._.antipodal:
                        try:
                            bm = integralize(bm)
                            bp = integralize(bp)
                            integralize((bp - bm) / self._.r)
                            if bp < 1 or bm > -2:
                                raise TypeError
                        except TypeError:
                            raise InfeasibleError("locally strongly regular "
                                                  "antipodal graph with d=4",
                                                  u"JurišićKoolen00")
                    self._.subconstituents[1] = self.add_subscheme(
                        DRGParameters((self._.a[1], -(bp+1)*(bm+1)),
                                      (Integer(1), mu)), "local graph")

            def checkMul(h):
                if self._.antipodal and self._.omega[h, self._.d] != 1 and \
                      self._.m[h] < self._.k[1] + self._.r - 2:
                    return ("m[%d] < k+r-2" % h, "GodsilHensel92")
                elif self._.a[self._.d] == 0 and \
                        1 not in [self._.omega[h, 2],
                                  self._.omega[h, self._.d]] \
                        and self._.m[h] < \
                        self._.k[1] + self._.b[self._.d-1] - 1:
                    return ("m[%d] < k+b[d-1]-1" % h, "GodsilKoolen95")
                elif self._.m[h] < self._.k[1]:
                    return ("m[%d] < k" % h, ("BCN", "Thm. 4.4.4."))
                else:
                    return None

            d = {h: checkMul(h) for h in range(1, self._.d)}
            s = {h for h, v in d.items() if v is not None}
            if not s.issubset([i, j]):
                m, k = min((self._.m[h], h) for h in s if h not in [i, j])
                reason, ref = d[k]
                raise InfeasibleError(reason, ref)
            r = []
            for h in s:
                t = self._.b[1] / (self._.theta[h] + 1)
                try:
                    integralize(t)
                except TypeError:
                    r.append(t)
            if len(r) == 0:
                return
            p = next(iter(r)).minpoly()
            a = NumberField(p, names=('a', )).gen()
            if len(r) == 1 or p.degree() != 2 or \
                    len({t.minpoly() for t in r}) == 2 or \
                    not a.is_integral():
                m, k = min((self._.m[h], h) for h in s)
                reason, ref = d[k]
                raise InfeasibleError(reason + ", b[1]/(theta[1]+1) and "
                                      "b[1]/(theta[d]+1) not integers "
                                      "or algebraic conjugates", ref)

    antipodalQuotient = PolyASParameters.antipodalSubscheme
    bipartiteHalf = PolyASParameters.bipartiteSubscheme
    diameter = PolyASParameters.classes
    distanceGraphs = PolyASParameters.partSchemes
    intersectionArray = PolyASParameters.parameterArray
    mergeClasses = merge
    substitute = subs
