import operator

from sage.arith.misc import GCD
from sage.combinat.q_analogues import q_int
from sage.functions.generalized import sgn
from sage.functions.log import log
from sage.functions.other import ceil
from sage.functions.other import floor
from sage.functions.other import sqrt
from sage.functions.trig import cos
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.integer import Integer
from sage.rings.infinity import Infinity
from sage.sets.real_set import RealSet
from sage.symbolic.constants import pi
from sage.symbolic.expression import Expression
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .assoc_scheme import ASParameters
from .assoc_scheme import PolyASParameters
from .aux import InfeasibleError
from .coefflist import CoefficientList
from .find import find
from .nonex import checkConditions
from .nonex import classicalFamilies
from .partition import PartitionGraph
from .util import checklist
from .util import checkNonneg
from .util import checkPos
from .util import checkPrimePower
from .util import eigenvalue_interval
from .util import hard_ceiling
from .util import hard_floor
from .util import integralize
from .util import is_algebraic_integer
from .util import is_constant
from .util import is_divisible
from .util import is_integer
from .util import is_squareSum
from .util import pair_keep
from .util import pair_swap
from .util import rewriteExp
from .util import subs
from .util import symbol
from .util import variables

PENTAGON = ((2, 1), (1, 1))
PETERSEN = ((3, 2), (1, 1))
TRIANGULAR7_COMPL = ((10, 6), (1, 6))
ICOSAHEDRON = ((5, 2, 1), (1, 2, 5))
DORO5 = ((10, 6, 4), (1, 2, 5))
GOSSET = ((27, 10, 1), (1, 10, 27))
CONWAY_SMITH = ((10, 6, 4, 1), (1, 2, 6, 10))

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

    def _compute_localEigenvalues(self):
        """
        Return the largest and smallest nontrivial eigenvalues
        together with their indices
        and the bounds for the nontrivial eigenvalues of the local graph.
        """
        th1, i = max((th, h) for h, th in enumerate(self._.theta)
                     if th != self._.k[1])
        thd, j = min((th, h) for h, th in enumerate(self._.theta)
                     if th != self._.k[1])
        bm = -1 - self._.b[1]/(th1+1)
        bp = -1 - self._.b[1]/(thd+1)
        return (th1, i, thd, j, bm, bp)

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

    def guaranteed_clique_order(self):
        """
        Return the smallest feasible order for a maximal clique in the graph.
        """
        if not self._has("maxCliques"):
            self.check_combinatorial()
        if self._.maxCliques:
            return self._.a[1] + 2
        s = Integer(3 if checkPos(self._.a[1]) else 2)
        a = self._.c[2] - 1
        b = self._.c[2] + 2*self._.a[1] + 1
        D = b**2 - 8*a*self._.k[1]
        if D > 0:
            r = hard_ceiling((b - sqrt(D))/(2*a))
            if not is_constant(r):
                r += 1
            if (b + sqrt(D))/(2*a) > r:
                t = self._.a[1] + 2 - (r-2)*a
                if t > s:
                    return t
        return s

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
        return self.match(TRIANGULAR7_COMPL, DORO5, CONWAY_SMITH)

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

    def localEigenvalue_range(self, compute=False, b=None, lowm=None,
                              return_refs=False):
        """
        Return the range of possible eigenvalues of a local graph.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        refs = []

        def out(ii):
            return (ii, refs) if return_refs else ii
        a = self._.a[1]
        if a == 0:
            return out(RealSet([0, 0]))
        elif a == 1 or self._.d == 1:
            return out(RealSet([-1, -1]) + RealSet([a, a]))
        if not self._has("m"):
            self.multiplicities()
        assert all(is_constant(th) for th in self._.theta), \
            "eigenvalues not constant"
        check_local = b is None
        if check_local:
            _, _, _, _, bm, bp = self._compute_localEigenvalues()
        else:
            bm, bp = b
        if lowm is None:
            lowm = [h for h in range(1, self._.d+1) if self._.m[h] < self._.k[1]]
        try:
            loc = self.localGraph(compute=compute, check_local=check_local)
            if isinstance(loc, DRGParameters):
                interval = sum((RealSet([th, th]) for th in loc.eigenvalues()
                                if th != a), RealSet())
                if interval.inf() < bm or interval.sup() > bp:
                    raise InfeasibleError("local eigenvalues "
                                          "not in allowed range",
                                          ("BCN", "Thm. 4.4.3."))
            else:
                raise IndexError
        except IndexError:
            interval = eigenvalue_interval(bm, bp) & RealSet([-a, a])
        orig = interval
        ll = -Infinity
        uu = Infinity
        if self._.d >= 3 and self.is_qPolynomial():
            x = SR.symbol("__x")
            s = None
            for q_order in self._.qPolynomial_ordering:
                for i in range(2, self._.d):
                    p = self.terwilligerPolynomial(x, i=i, q_order=q_order)
                    sign = sgn(p.coefficient(x**4))
                    if s is None:
                        s = sign
                    elif s == sign:
                        continue
                    tint = RealSet()
                    for sol in _solve(p >= 0, x):
                        l = u = None
                        for eq in sol:
                            op = eq.operator()
                            if op is operator.eq:
                                l = u = eq.rhs()
                            elif op is operator.ge:
                                l = eq.rhs()
                            elif op is operator.le:
                                u = eq.rhs()
                        tint += eigenvalue_interval(l, u)
                    interval &= tint
                    ll = max(ll, tint.inf())
                    uu = min(uu, tint.sup())
                    if s != sign:
                        break
            if interval != orig:
                refs.append(("GavrilyukKoolen16", "Thm. 4.2."))
        bcn443 = (bm > -a and bm > ll) or (bp < a and bp < uu)
        if bcn443:
            refs.insert(0, ("BCN", "Thm. 4.4.3."))
        if (interval - RealSet([a, a])).sup() <= -1:
            interval -= RealSet.unbounded_below_open(-1)
        interval += RealSet([a, a])
        if interval.inf() > -1:
            raise InfeasibleError("invalid eigenvalues for local graph",
                                  refs)
        if interval.cardinality() == 2:
            if not is_divisible(self._.b[0], a+1):
                raise InfeasibleError("graph with maximal cliques "
                                      "but a[1]+1 does not divide k", refs)
            if bp < a:
                if not bcn443:
                    refs.insert(0, ("BCN", "Thm. 4.4.3."))
                raise InfeasibleError(
                    "graph with maximal cliques but b+ < a[1]", refs)
        ll = uu = None
        for ii in interval:
            l, u = ii.lower(), ii.upper()
            for e, c in {l: ii.lower_closed(), u: ii.upper_closed()}.items():
                if c:
                    roots = [r for r, _ in SR(e).minpoly().roots(SR)]
                    if not all(r in interval for r in roots):
                        interval -= sum((RealSet([r, r]) for r in roots
                                         if r.is_real()), RealSet())
            if l == u:
                continue
            if ll is None:
                ll, uu = l, u
            else:
                ll, uu = min(ll, l), max(uu, u)
        if ll is not None:
            l = floor(ll)
            u = ceil(uu)
            if u - l <= 4 and uu - ll < 4:
                keep = RealSet()
                m = l + 2
                if u - l <= 3:
                    uu = m
                k = 3
                while m + 2*cos(2*pi/k) <= uu:
                    t = floor((k-1)/2)
                    if k % 2 == 1 and m + 2*cos(2*t*pi/k) < ll:
                        break
                    roots = []
                    for j in range(1, t+1):
                        if GCD(j, k) == 1:
                            r = m + 2*cos(2*j*pi/k)
                            if r not in interval:
                                break
                            roots.append(r)
                    else:
                        keep += sum((RealSet([r, r]) for r in roots),
                                    RealSet())
                    k += 1
                interval -= RealSet((l, u))
                interval += keep
                refs.append(("BrouwerKoolen99", "cf. Thm. 7.1."))
        minmult = {a: Integer(1)}
        for h in lowm:
            th = -1 - self._.b[1] / (self._.theta[h] + 1)
            minmult[th] = self._.k[1] - self._.m[h] + (1 if th == a else 0)
        posint = interval - RealSet.unbounded_below_open(0)
        th1 = posint.inf()
        th2 = (interval - RealSet.unbounded_above_open(0)).sup()
        if posint.cardinality() <= 2 and th1 != th2 and -th2 <= th1:
            rr = [("MakhnevBelousov21", "cf. Sec. 4")]
            if len(minmult) > 1 or minmult[a] > 1:
                rr.insert(0, ("BCN", "Thm. 4.4.4."))
            th3 = interval.inf()
            rest = self._.k[1] - sum(minmult.values())
            fix = sum(th * mul for th, mul in minmult.items())
            m1u = floor(-(rest * th3 + fix) / (th1 - th3))
            if rest < 0 or m1u < 0:
                raise InfeasibleError("no solution for the multiplicities "
                                      "of the eigenvalues of the local graph",
                                      refs + rr)
            m1l = ceil(-(rest * th2 + fix) / (th1 - th2))
            if m1l < 0:
                m1l = Integer(0)
            m2 = rest - m1l
            m3 = rest - m1u
            fix2 = sum(th**2 * mul for th, mul in minmult.items())
            sth2 = fix2 + m1l * th1**2 + m2 * th2**2
            sth3 = fix2 + m1u * th1**2 + m3 * th3**2
            edges = a * self._.k[1]
            if sth2 >= edges:
                refs += rr
                if m1l > 0:
                    minmult[th1] = minmult.get(th1, 0) + m1l
                if m2 > 0:
                    minmult[th2] = minmult.get(th2, 0) + m2
                if sth2 > edges or any(th not in interval for th in minmult):
                    raise InfeasibleError("lower bound for the number of edges"
                                          " in the local graph exceeded", refs)
                interval = sum((RealSet([th, th]) for th in minmult),
                               RealSet())
            elif -th3 <= th1 and sth3 <= edges:
                refs += rr
                if m1u > 0:
                    minmult[th1] = minmult.get(th1, 0) + m1u
                if m3 > 0:
                    minmult[th3] = minmult.get(th3, 0) + m3
                if sth3 < edges or any(th not in interval for th in minmult):
                    raise InfeasibleError("upper bound for the number of edges"
                                          " in the local graph exceeded", refs)
                interval = sum((RealSet([th, th]) for th in minmult),
                               RealSet())
        return out(interval)

    def localGraph(self, compute=False, check_local=True):
        """
        Return parameters of the local graph
        if it is known to be distance-regular.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        return self.subconstituent(1, compute=compute,
                                   check_local=check_local)

    def maximalCliquePolynomial(self, var='x'):
        """
        Return the maximal clique polynomial of a strongly regular graph.
        """
        assert self._.d == 2, "diameter must be 2"
        if not self._has("theta"):
            self.eigenvalues()
        m = -min(self._.theta, key=lambda x: CoefficientList(x, self._.vars))
        x = SR.symbol(var) if isinstance(var, str) else var
        M = ((x + m - 3) * (self._.k[1] - x + 1)
             - 2 * (x - 1) * (self._.a[1] - x + 2))**2 - \
            (self._.k[1] - x + 1)**2 * (x + m - 1) * (x - (m-1) * (4*m-1))
        return M.expand()

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

    def subconstituent(self, h, compute=False, check_local=True):
        """
        Return parameters of the h-th subconstituent
        if it is known to form an association scheme.
        If the resulting scheme is P-polynomial,
        the parameters are returned as such.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        if h == 1:
            if self._.subconstituents[h] is None:
                self.check_2graph()
            if self._.subconstituents[h] is None and check_local:
                self.check_localEigenvalues(check_range=False)
        elif h == 3 and self._.d == 3:
            sol = FAMILY_EXTCODE._match(*self.intersectionArray())
            if sol:
                self._.subconstituents[h] = \
                    (self.add_subscheme(FAMILY_EXTCODE_SUBC3.subs(*sol[0]),
                                        self._subconstituent_name(h)),
                     [("Vidali13", "Thm. 4.6.3")])
        if self._.subconstituents[h] is None:
            subc, refs, rels = PolyASParameters.subconstituent(self, h,
                                                               compute=compute,
                                                               return_rels=True)
            trd = tuple(range(subc._.d+1))
            if subc is not None and len(rels) > 1 and rels[1] == 1 \
                    and subc.is_pPolynomial() \
                    and trd in subc._.pPolynomial_ordering:
                old, subc = subc, DRGParameters(subc, order=trd)
                self._.subconstituents[h] = (subc, refs)
                self.add_subscheme(subc, replace=old)
        else:
            subc, refs = self._.subconstituents[h]
        return subc

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
            bcn = ("BCN", "Thm. 1.5.3.")
            try:
                mu = integralize(self._.a[1] / 2)
                n = integralize(self._.n / 4)
            except TypeError:
                raise InfeasibleError("Taylor graph with a[1] > 0 odd "
                                      "or cover of K_n with n odd", bcn)
            self._.subconstituents[1] = \
                (self.add_subscheme(DRGParameters((self._.a[1], n - mu - 1),
                                                  (Integer(1), mu)),
                                    "local graph"), [bcn])

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
        self._.maxCliques = self._.a[1] == 0
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
                raise InfeasibleError("Turán's theorem",
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
        if self._.d == 2 and all(is_integer(x)
                                 for x in self._.b + self._.c) and \
                self._.b[1] == self._.c[2] and \
                self._.b[0] == 2*self._.b[1] and \
                (not is_divisible(self._.n - 1, 4) or not is_squareSum(self._.n)):
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
                and is_integer(self._.r) and is_integer(self._.b[0]) \
                and self._.b[0] - 1 == self._.b[1] + self._.c[2]:
            ok = True
            if is_divisible(self._.r, 2):
                ok = is_squareSum(self._.b[0])
            elif is_divisible(self._.b[0], 2):
                r = Integer(self._.r if is_divisible(self._.r - 1, 4) else -self._.r)
                ok = Integer(self._.b[0]).is_square() or r.is_square() or \
                    (Integers(self._.r)(self._.b[0]).is_square() and
                     Integers(self._.b[0])(r).is_square())
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
        if self._.antipodal and self._.d >= 4 and is_divisible(self._.d, 2):
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
        g, s, t = self.genPoly_parameters()
        if g == 4 and s > 1 and t > 1:
            tf = 8*t/3 + 1
            if is_constant(tf):
                tf = floor(tf)
            if not checkNonneg(t * tf - s):
                raise InfeasibleError("infeasible parameters "
                                      "for pseudo-generalized quadrangle",
                                      "GKMP20")
        if not self._has("maxCliques"):
            self.check_combinatorial()
        if not self._.maxCliques:
            return
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
                if is_integer(m) and Integer(m) % 4 in [1, 2] and \
                        not is_squareSum(m):
                    raise InfeasibleError("Bruck-Ryser theorem",
                                          ("BCN", "Thm. 1.10.4."))
        if self._.antipodal and self._.d == 3 and self._.r > 2 and \
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
            s, r = sorted(self._.theta[1:],
                          key=lambda x: CoefficientList(x, self._.vars))
            if self._.c[2] not in [s*s, s*(s+1)] and \
                    2*(r+1) > s*(s+1)*(self._.c[2]+1):
                raise InfeasibleError("claw bound exceeded",
                                      "BrouwerVanLint84")

    @check(1)
    def check_maximalClique(self):
        """
        For a strongly regular graph,
        check whether the range of possible sizes of maximal cliques
        is nonempty.
        """
        if self._.d != 2:
            return
        m = -min(self._.theta, key=lambda x: CoefficientList(x, self._.vars))
        b = self._.c[2] - m*(m-1)
        if checkNonneg(-b):
            return
        x = SR.symbol("__x")
        M = self.maximalCliquePolynomial(x)
        c = self.guaranteed_clique_order()
        d = floor(1 + self._.k[1] / m)
        if c > self._.c[2]**2 / b - m + 1 and \
                M.subs(x == c) < 0 and M.subs(x == d) < 0:
            raise InfeasibleError("no feasible maximal clique size", "GKP21")

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
        if self._.d >= 2 and is_integer(self._.b[0]) and \
                is_integer(self._.a[1]) and is_integer(self._.c[2]):
            if all(is_constant(th) for th in self._.theta):
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
                        not self.match(PENTAGON, PETERSEN, ICOSAHEDRON):
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
                raise InfeasibleError("quadrangle per claw bound "
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
                         self.match(GOSSET)):
                raise InfeasibleError("theta[1] = b[1]-1, "
                                      "not in characterization",
                                      ("BCN", "Thm. 4.4.11."))

    @check(1)
    def check_localEigenvalues(self, compute=False, check_range=True):
        """
        For a graph of diameter at least 3 with a[1] > 2,
        check whether the eigenvalues of the local graph
        are in the allowed range.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        if not self._has("m"):
            self.multiplicities()
        if self._.d < 3 or self._.a[1] <= 2 or self.match(ICOSAHEDRON) or \
                not all(is_constant(th) for th in self._.theta
                        if th != self._.k[1]):
            return
        th1, i, thd, j, bm, bp = self._compute_localEigenvalues()
        if (bm > -2 and self._.c[2] != 1) or bp < 1:
            raise InfeasibleError("local eigenvalues not in allowed range",
                                  ("BCN", "Thm. 4.4.3."))
        if not self._.bipartite:
            mu = self._.a[1] + bp*bm
            bd = self._.k[1] * mu - \
                (self._.a[1] - bp) * (self._.a[1] - bm)
            fb = self._.k[1] * self._.a[1] * self._.b[1] + \
                (th1 * (self._.a[1] + 1) + self._.k[1]) * \
                (thd * (self._.a[1] + 1) + self._.k[1])
            refs = []
            jk = "JurišićKoolen00"
            jkt = "JKT00"
            if bd == 0:
                refs.append(jk)
            if fb == 0:
                refs.append(jkt)
            if bd > 0:
                raise InfeasibleError("bound on local eigenvalues "
                                      "exceeded", jk)
            if fb < 0:
                raise InfeasibleError("fundamental bound exceeded", jkt)
            elif refs:
                try:
                    integralize(self._.c[2]*mu/2)
                    if self._.c[2] < mu + 1:
                        raise TypeError
                except TypeError:
                    raise InfeasibleError("local graph strongly regular", jk)
                if self._.d == 4 and self._.antipodal:
                    try:
                        bm = integralize(bm)
                        bp = integralize(bp)
                        integralize((bp - bm) / self._.r)
                        if bp < 1 or bm > -2:
                            raise TypeError
                    except TypeError:
                        raise InfeasibleError("locally strongly regular "
                                              "antipodal graph with d=4", jk)
                self._.subconstituents[1] = (self.add_subscheme(
                    DRGParameters((self._.a[1], -(bp+1)*(bm+1)),
                                  (Integer(1), mu)), "local graph"), refs)

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

        d = {h: checkMul(h) for h in range(1, self._.d+1)}
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
        if len(r) != 0:
            p = next(iter(r)).minpoly()
            if len(r) == 1 or p.degree() != 2 or \
                    len({t.minpoly() for t in r}) == 2 or \
                    not is_algebraic_integer(p):
                m, k = min((self._.m[h], h) for h in s)
                reason, ref = d[k]
                raise InfeasibleError(reason + ", b[1]/(theta[1]+1) and "
                                      "b[1]/(theta[d]+1) not integers "
                                      "or algebraic conjugates", ref)
        if not check_range:
            return
        rng, refs = self.localEigenvalue_range(compute=compute,
                                               b=(bm, bp),
                                               lowm=[h for h in s if
                                                     self._.m[h] < self._.k[1]],
                                               return_refs=True)
        c = rng.cardinality()
        if rng.sup() <= bp or self._.subconstituents[1] is not None or \
                not is_integer(c):
            return
        ths = {SR.symbol("__m%d" % i): ii.lower()
               for i, ii in enumerate(rng) if ii.lower() != self._.a[1]}
        exps = {m: (0, self._.k[1] - 1) for m in ths}
        conds = [sum(m for m in ths) == self._.k[1] - 1,
                 sum(a*m for m, a in ths.items()) == -self._.a[1],
                 sum(a**2 * m for m, a in ths.items())
                 == (self._.k[1] - self._.a[1]) * self._.a[1]]
        lvl = 0
        reason = None
        ref = None
        for sol in find(exps, ths.keys(), conds):
            sp = {ths[eq.lhs()]: eq.rhs()
                  for eq in sol if eq.rhs() != 0}
            lsp = len(sp)
            if lsp <= 3:
                q = max(p ** (e+1 if p == 2 else e)
                        for p, e in Integer(self._.k[1]).factor())
                thi = {th: th**2 * m for th, m in sp.items()}
                thi[self._.a[1]] = self._.a[1]**2
                for i in range(3, q+1):
                    for th in thi:
                        thi[th] *= th
                    tr = sum(thi.values())
                    if not is_divisible(tr, self._.k[1] * (1 + i % 2)):
                        if lvl < 1:
                            lvl = 1
                            reason = "local graph has nonintegral " \
                                "number of closed %d-walks " \
                                "through a vertex" % i
                            ref = "vanDam95"
                        break
                    if i == 4:
                        xi = Integer(tr / self._.k[1] -
                                     self._.a[1] * (2*self._.a[1] - 1))
                        if xi % 2 != 0:
                            if lvl < 2:
                                lvl = 2
                                reason = "local graph has nonintegral " \
                                    "number of quadrangles " \
                                    "through a vertex"
                                ref = "vanDam95"
                            break
                        if lsp == 2 and not is_divisible(xi, self._.a[1]):
                            if lvl < 3:
                                lvl = 3
                                reason = "local graph has nonintegral " \
                                    "number of quadrangles " \
                                    "through an edge"
                                ref = ("vanDam95", "Lem. 3.1.")
                            break
                else:
                    return
            else:
                return
        if reason is None:
            reason = "no solution for the multiplicities " \
                "of the eigenvalues of the local graph"
        else:
            refs.append(ref)
        raise InfeasibleError(reason, refs)

    antipodalQuotient = PolyASParameters.antipodalSubscheme
    bipartiteHalf = PolyASParameters.bipartiteSubscheme
    diameter = PolyASParameters.classes
    distanceGraphs = PolyASParameters.partSchemes
    intersectionArray = PolyASParameters.parameterArray
    mergeClasses = merge
    substitute = subs


r = symbol("__r")
t = symbol("__t")

FAMILY_EXTCODE = DRGParameters([2*r*t*(2*r+1), (2*r-1)*(2*r*t+t+1), r*(r+t)], [1, r*(r+t), t*(4*r**2-1)])
FAMILY_EXTCODE_SUBC3 = DRGParameters([t*(2*r+1), (t+1)*(2*r-1), 1], [1, t+1, t*(2*r+1)])
