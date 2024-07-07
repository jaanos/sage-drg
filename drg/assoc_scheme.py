from copy import copy
from warnings import warn

from sage.symbolic.constants import pi
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.combinat.set_partition import SetPartitions
from sage.functions.orthogonal_polys import gegenbauer
from sage.functions.other import floor
from sage.functions.trig import cos
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import diagonal_matrix
from sage.matrix.constructor import identity_matrix
from sage.misc.latex import latex
from sage.misc.latex import LatexExpr
from sage.combinat.subset import subsets
from sage.rings.integer import Integer
from sage.structure.sage_object import SageObject
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from sage.typeset.ascii_art import ascii_art
from sage.typeset.symbols import ascii_left_curly_brace
from sage.typeset.symbols import ascii_right_curly_brace
from sage.typeset.symbols import unicode_left_curly_brace
from sage.typeset.symbols import unicode_right_curly_brace
from sage.typeset.unicode_art import unicode_art
from .array3d import Array3D
from .array3d import Array4D
from .aux import InfeasibleError
from .aux import Parameters
from .coefflist import CoefficientList
from .find import find
from .nonex import checkConditions
from .nonex import families
from .nonex import sporadic
from .view import Param
from .util import checklist
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
from .util import is_divisible
from .util import is_integral
from .util import make_expressions
from .util import nrows
from .util import refresh
from .util import rewriteExp
from .util import rewriteMatrix
from .util import rewriteTuple
from .util import sort_solution
from .util import subs
from .util import symbol
from .util import variables

TPERMS = [[0, 1, 2], [0, 2, 1], [1, 0, 2],
          [1, 2, 0], [2, 0, 1], [2, 1, 0]]
DPERMS = [[0, 1, 2], [1, 0, 2], [0, 2, 1],
          [2, 0, 1], [1, 2, 0], [2, 1, 0]]

QHPERMS = [[0, 1, 2, 3, 4, 5], [0, 2, 1, 4, 3, 5], [1, 0, 2, 3, 5, 4],
           [1, 2, 0, 5, 3, 4], [2, 0, 1, 4, 5, 3], [2, 1, 0, 5, 4, 3],
           [0, 3, 4, 1, 2, 5], [0, 4, 3, 2, 1, 5], [3, 0, 4, 1, 5, 2],
           [3, 4, 0, 5, 1, 2], [4, 0, 3, 2, 5, 1], [4, 3, 0, 5, 2, 1],
           [1, 3, 5, 0, 2, 4], [1, 5, 3, 2, 0, 4], [3, 1, 5, 0, 4, 2],
           [3, 5, 1, 4, 0, 2], [5, 1, 3, 2, 4, 0], [5, 3, 1, 4, 2, 0],
           [2, 4, 5, 0, 1, 3], [2, 5, 4, 1, 0, 3], [4, 2, 5, 0, 3, 1],
           [4, 5, 2, 3, 0, 1], [5, 2, 4, 1, 3, 0], [5, 4, 2, 3, 1, 0]]
QDPERMS = [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3],
           [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
           [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3],
           [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
           [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3],
           [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
           [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2],
           [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

DUAL_PARAMETER = "Krein parameter"
DUAL_PARTS = "eigenspaces"
DUAL_SYMBOL = "q"
OBJECT = "association scheme"
PARAMETER = "intersection number"
PARTS = "relations"
SYMBOL = "p"

check_ASParameters = []
check = checklist(check_ASParameters)


class ASParameters(SageObject):
    """
    A class for parameters of a general association scheme
    and checking their feasibility.
    """

    _ = None
    _checklist = check_ASParameters
    METRIC = False

    def __init__(self, p=None, q=None, P=None, Q=None, complement=None):
        """
        Object constructor.
        """
        self._init_storage()
        if self._get_class() is ASParameters:
            self._init_prefix()
            self._.bipartite = False
        assert (p, q, P, Q).count(None) >= 3, \
            "precisely one of p, q, P, Q must be given"
        if isinstance(p, ASParameters):
            p._copy(self)
        elif p is not None:
            self._.p = self._init_parameters(p, integral=True,
                                             name=PARAMETER, sym=SYMBOL)
            self._compute_kTable()
            self._check_consistency(self._.p, self._.k,
                                    name=PARAMETER, sym=SYMBOL)
            self.check_handshake()
        elif q is not None:
            self._.q = self._init_parameters(q, integral=False,
                                             name=DUAL_PARAMETER,
                                             sym=DUAL_SYMBOL)
            self._compute_multiplicities()
            self._check_consistency(self._.q, self._.m,
                                    name=DUAL_PARAMETER, sym=DUAL_SYMBOL)
        elif P is not None:
            self._.P = self._init_eigenmatrix(P)
        elif Q is not None:
            self._.Q = self._init_eigenmatrix(Q)
        else:
            assert self._.d is not None, "insufficient data"
        self._.subconstituents = [None] * (self._.d + 1)
        self._compute_complement(complement)
        self._init_vars()

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash(id(self))

    def __len__(self, expand=False, factor=False, simplify=False):
        """
        Return the number of vertices.
        """
        self._.n = rewriteExp(self._.n, expand=expand, factor=factor,
                              simplify=simplify)
        return self._.n

    def __repr__(self):
        """
        String representation.
        """
        return "Parameters of an association scheme on %s vertices " \
               "with %d classes" % (self._.n, self._.d)

    def _check_consistency(self, p, k, name=None, sym=None):
        """
        Check for the consistency of the intersection numbers
        or Krein parameters.
        """
        r = range(self._.d + 1)
        for h in r:
            assert p[0, h, h] == k[h], \
                "mismatch of %s %s[0, %d, %d]" % (name, sym, h, h)
            for i in r:
                s = 0
                for j in r:
                    assert p[h, i, j] == p[h, j, i], \
                        "non-symmetric %s %s[%d, %d, %d]" % \
                        (name, sym, h, i, j)
                    assert p[h, i, j] * k[h] == p[j, h, i] * k[j], \
                        "double counting mismatch for %s[%d, %d, %d]" % \
                        (sym, h, i, j)
                    s += p[h, i, j]
                    for u in r:
                        assert sum(p[v, i, j] * p[u, v, h] for v in r) == \
                               sum(p[u, i, v] * p[v, j, h] for v in r), \
                               "double counting mismatch for " \
                               "sum_l %s[l, %d, %d] %s[%d, l, %d]" % \
                               (sym, i, j, sym, u, h)
                assert s == k[i], \
                    "mismatch of sum_j %s[%d, %d, j]" % (sym, h, i)
        if not self._has("n"):
            self._.n = sum(k)

    def _check_eigenmatrices(self):
        """
        Check whether the eigenmatrices
        multiply into a multiple of the identity matrix.
        """
        if self._has("P") and self._has("Q") and \
                _simplify(_expand(self._.P * self._.Q)) \
                != self.order(expand=True, simplify=True) \
                * identity_matrix(SR, self._.d + 1):
            warn(Warning("the eigenmatrices do not multiply "
                         "into a multiple of the identity matrix"))

    def _check_family(self):
        """
        Check whether the association scheme has parameters for which
        nonexistence has been shown as a part of an infinite family.

        Currently does nothing for general association schemes.
        """
        return

    @staticmethod
    def _check_parameter(h, i, j, v, integral=False, name=None, sym=None):
        """
        Check for the feasibility
        of an intersection number or Krein parameter.

        The parameter is checked for nonnegativity,
        and, if requested, also for integrality.
        """
        if integral:
            try:
                v = integralize(v)
            except TypeError:
                raise InfeasibleError("%s %s[%d, %d, %d] is nonintegral"
                                      % (name, sym, h, i, j))
        assert checkNonneg(v), \
            "%s %s[%d, %d, %d] is negative" % (name, sym, h, i, j)
        return v

    def _check_parameters(self, p, integral=False, name=None, sym=None):
        """
        Check for the feasibility
        of all intersection numbers or Krein parameters.

        The parameters are checked for nonnegativity,
        and, if requested, also for integrality.
        """
        for h in range(self._.d + 1):
            for i in range(self._.d + 1):
                for j in range(self._.d + 1):
                    p[h, i, j] = ASParameters. \
                        _check_parameter(h, i, j, p[h, i, j],
                                         integral=integral,
                                         name=name, sym=sym)

    def _check_zero(self, h, i, j, u, v, w):
        """
        Check whether a triple intersection number is not forced to be zero
        by the intersection numbers.
        """
        return self._.p[u, h, i] != 0 and self._.p[v, h, j] != 0 and \
            self._.p[w, i, j] != 0

    def _complement(self):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        assert self._.d == 2, "the complement is only defined for two classes"
        kargs = {"complement": self}
        if self._has("p"):
            kargs["p"] = self._.p.reorder([0, 2, 1], inplace=False)
        elif self._has("q"):
            kargs["q"] = self._.q.reorder([0, 2, 1], inplace=False)
        elif self._has("P"):
            kargs["P"] = self._.P[[0, 2, 1], [0, 2, 1]]
        elif self._has("Q"):
            kargs["Q"] = self._.Q[[0, 2, 1], [0, 2, 1]]
        return ASParameters(**kargs)

    def _compute_complement(self, complement):
        """
        For a scheme with two classes,
        determine its complement if not given.
        """
        if self._.d == 2 and complement is not False:
            if complement is None:
                complement = self._complement()
            self._.complement = self.add_subscheme(complement, "complement")

    def _compute_dualEigenmatrix(self, expand=False, factor=False,
                                 simplify=False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        if self._has("Q"):
            return
        if self._has("q"):
            self._.Q = self._compute_eigenmatrix(self._.q, expand=expand,
                                                 factor=factor,
                                                 simplify=simplify)
        else:
            if not self._has("P"):
                self.eigenmatrix(expand=expand, factor=factor,
                                 simplify=simplify)
            self._.Q = self._.n * self._.P.inverse()
        self._check_eigenmatrices()

    def _compute_eigenmatrix(self, p, expand=False, factor=False,
                             simplify=False):
        """
        Compute and return an eigenmatrix of the association scheme.
        """
        B = [Matrix(SR, [M[i] for M in p]) for i in range(self._.d + 1)]
        V = SR**(self._.d + 1)
        R = [[self._.d + 1, V, [Integer(1)]]]
        for i in range(1, self._.d + 1):
            S = sorted(([k, m, V.subspace_with_basis(b)]
                        for k, b, m in B[i].eigenvectors_right()),
                       key=lambda kvb: CoefficientList(kvb[0], self._.vars),
                       reverse=True)
            j = 0
            while j < len(R):
                m, s, r = R[j]
                h = 0
                while h < len(S):
                    k, v, b = S[h]
                    sb = s.intersection(b)
                    d = sb.dimension()
                    if d == v:
                        del S[h]
                    else:
                        S[h][1] -= d
                        h += 1
                    if d == m:
                        R[j][1] = sb
                        r.append(k)
                        break
                    elif d > 0:
                        R.insert(j, [d, sb, r + [k]])
                        j += 1
                        m -= d
                        R[j][0] = m
                j += 1
        assert len(R) == self._.d + 1 and all(len(r) == self._.d + 1
                                              for _, _, r in R), \
            "failed to compute the eigenmatrix"
        return Matrix(SR, [r for _, _, r in R])

    def _compute_kreinParameters(self, expand=False, factor=False,
                                 simplify=False):
        """
        Compute the Krein parameters.
        """
        if self._has("q"):
            return
        if not self._has("m"):
            self.multiplicities(expand=expand, factor=factor,
                                simplify=simplify)
        if not self._has("k"):
            self.kTable(expand=expand, factor=factor,
                        simplify=simplify)
        q = Array3D(self._.d + 1)
        self._compute_parameters(q, self._.Q, self._.k, integral=False,
                                 name=DUAL_PARAMETER, sym=DUAL_SYMBOL)
        self._.q = q

    def _compute_kTable(self, expand=False, factor=False, simplify=False):
        """
        Compute the valencies of the relations.
        """
        if self._has("k"):
            return
        if self._has("p"):
            k = tuple(self._.p[0, i, i] for i in range(self._.d + 1))
        else:
            if not self._has("P"):
                self.eigenmatrix(expand=expand, factor=factor,
                                 simplify=simplify)
            k = tuple(integralize(x) for x in self._.P[0])
        assert k[0] == 1, \
            "the valency of the first relation is not 1"
        self._.k = k

    def _compute_multiplicities(self, expand=False, factor=False,
                                simplify=False):
        """
        Compute the multiplicities of the eigenspaces.
        """
        if self._has("m"):
            return
        if self._has("q"):
            m = tuple(integralize(self._.q[0, i, i])
                      for i in range(self._.d + 1))
        else:
            if not self._has("Q"):
                self.dualEigenmatrix(expand=expand, factor=factor,
                                     simplify=simplify)
            m = tuple(integralize(x) for x in self._.Q[0])
        assert m[0] == 1, "the multiplicity of the first eigenspace is not 1"
        self._.m = m

    def _compute_parameters(self, p, P, m, integral=False, name=None,
                            sym=None):
        """
        Compute the intersection numbers or Krein parameters
        from the eigenmatrices.
        """
        for h in range(self._.d + 1):
            for i in range(self._.d + 1):
                for j in range(self._.d + 1):
                    p[h, i, j] = full_simplify(
                        sum(m[t] * P[t, h] * P[t, i] * P[t, j]
                            for t in range(self._.d + 1))
                        / (self._.n * P[0, h]))
                    self._check_parameter(h, i, j, p[h, i, j],
                                          integral=integral,
                                          name=name, sym=sym)
        self._check_consistency(p, P[0], name=name, sym=sym)

    def _compute_primalEigenmatrix(self, expand=False, factor=False,
                                   simplify=False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        if self._has("P"):
            return
        if self._has("p"):
            self._.P = self._compute_eigenmatrix(self._.p, expand=expand,
                                                 factor=factor,
                                                 simplify=simplify)
        else:
            if not self._has("Q"):
                self.dualEigenmatrix(expand=expand, factor=factor,
                                     simplify=simplify)
            self._.P = self._.n * self._.Q.inverse()
        self._check_eigenmatrices()

    def _compute_pTable(self, expand=False, factor=False,
                        simplify=False):
        """
        Compute the intersection numbers.
        """
        if self._has("p"):
            return
        if not self._has("k"):
            self.kTable(expand=expand, factor=factor, simplify=simplify)
        if not self._has("m"):
            self.multiplicities(expand=expand, factor=factor,
                                simplify=simplify)
        p = Array3D(self._.d + 1)
        self._compute_parameters(p, self._.P, self._.m, integral=True,
                                 name=PARAMETER, sym=SYMBOL)
        self._.p = p
        self.check_handshake()

    def _copy(self, p):
        """
        Copy fields to the given object.
        """
        p._.d = self._.d
        p._.n = self._.n
        if self._has("p"):
            p._.p = copy(self._.p)
        if self._has("q"):
            p._.q = copy(self._.q)
        if self._has("P"):
            p._.P = copy(self._.P)
        if self._has("Q"):
            p._.Q = copy(self._.Q)
        if self._has("k"):
            p._.k = self._.k
        if self._has("m"):
            p._.m = self._.m
        if self._has("fsd"):
            p._.fsd = self._.fsd
        if self._has("pPolynomial_ordering"):
            p._.pPolynomial_ordering = self._.pPolynomial_ordering
        if self._has("qPolynomial_ordering"):
            p._.qPolynomial_ordering = self._.qPolynomial_ordering
        if self._has("complement"):
            p._.complement = self._.complement
        p._.fusion_schemes.update(self._.fusion_schemes)
        p._.subschemes.update(self._.subschemes)
        p._.subconstituents = list(self._.subconstituents)
        p._.triple.update(self._.triple)
        p._.triple_solution.update(self._.triple_solution)
        p._.triple_solution_generator.update(self._.triple_solution_generator)
        p._.quadruple.update(self._.quadruple)

    def _derived(self, derived=True):
        """
        Generate parameters sets of derived association schemes.
        """
        self.polynomialOrders()
        self.all_subconstituents(compute=derived > 1)
        if derived > 1:
            self.all_fusions()
        subcs = set()
        pars = self._get_parameters()
        c = self.classes()

        def derived():
            for pa, part in self._.fusion_schemes.items():
                yield (pa, part, [], True)
            for par in self._.subconstituents:
                if par is None:
                    continue
                pa, refs = par
                yield (pa, self._.subschemes[pa], refs, False)
                subcs.add(pa)
            for pa, part in self._.subschemes.items():
                if pa not in subcs:
                    yield (pa, part, [], False)
        for pa, part, refs, fusion in derived():
            if pars is not None or not fusion or pa.classes() < c:
                yield pa, part, refs, fusion

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return ASParameters

    def _get_parameters(self):
        """
        Return the defining parameter set, if any.

        Currently, this is not defined for general association schemes.
        """
        return None

    def _has(self, name):
        """
        Check whether the given parameter is available.
        """
        return hasattr(self._, name)

    def _init_eigenmatrix(self, P):
        """
        Initialize an eigenmatrix from the specified matrix.
        """
        self._.d = nrows(P) - 1
        assert all(len(r) == self._.d + 1 for r in P), \
            "parameter length mismatch"
        P = Matrix(SR, P)
        for i, x in enumerate(P[0]):
            P[0, i] = integralize(x)
        self._.n = sum(P[0])
        return P

    def _init_parameters(self, p, integral=False, name=None, sym=None):
        """
        Initialize the intersection numbers or Krein parameters
        from the specified array.
        """
        self._.d = nrows(p) - 1
        if isinstance(p, Array3D):
            a = p
        else:
            assert all(len(M) == self._.d + 1 and all(len(r) == self._.d+1
                                                      for r in M)
                       for M in p), "parameter length mismatch"
            a = Array3D(self._.d + 1)
            for h in range(self._.d + 1):
                for i in range(self._.d + 1):
                    for j in range(self._.d + 1):
                        a[h, i, j] = p[h][i][j]
        self._check_parameters(a, integral=integral, name=name, sym=sym)
        return a

    def _init_prefix(self):
        """
        Initialize prefix to be used for internal variables.
        """
        self._.prefix = "v%x" % (hash(self) % Integer(2)**32)

    def _init_schoenberg(self):
        """
        Initialize parameters for the computation of the limit
        up to which Schönberg's theorem is tested.
        """
        return (self._.d, 1 / self._.n)

    def _init_storage(self):
        """
        Initialize parameter storage object.
        """
        if self._ is None:
            self._ = Parameters(self)

    def _init_vars(self):
        """
        Initialize the list of variables.
        """
        if not self._has("vars"):
            if self._has("p"):
                self._.vars = self._.p.variables()
            elif self._has("q"):
                self._.vars = self._.q.variables()
            elif self._has("P"):
                self._.vars = variables(self._.P)
            elif self._has("Q"):
                self._.vars = variables(self._.Q)
        self._.vars_ordered = len(self._.vars) <= 1

    def _is_polynomial(self, p, i):
        """
        Check whether the association scheme is polynomial
        for the given parameters and principal relation or eigenspace.
        """
        order = [0, i]
        while len(order) <= self._.d:
            j = {h for h in range(self._.d+1)
                 if h not in order[-2:] and not p[order[-1], i, h] == 0}
            if len(j) != 1:
                return False
            j, = j
            order.append(j)
        return tuple(order)

    def _is_trivial(self):
        """
        Check whether the association scheme is trivial
        for the purposes of feasibility checking.

        Returns ``True`` if the scheme has at most one class.
        """
        return self._.d <= 1

    @staticmethod
    def _merge_parts(parts, p, sym=None):
        """
        Return a parameter set for a scheme
        with merged relations or eigenspaces.
        """
        d = len(parts)
        concat = sum(parts, [])
        assert parts[0] == [0], "identity not preserved"
        assert all(len(pt) > 0 for pt in parts), "empty group specified"
        assert len(concat) == len(set(concat)), "repeated part specified"
        assert set(concat) == set(range(len(p))), "invalid part specified"
        a = Array3D(d)
        for h in range(d):
            for i in range(d):
                for j in range(d):
                    a[h, i, j] = sum(p[parts[h][0], ii, jj]
                                     for ii in parts[i] for jj in parts[j])
                    if not all(a[h, i, j] == sum(p[hh, ii, jj]
                                                 for ii in parts[i]
                                                 for jj in parts[j])
                               for hh in parts[h][1:]):
                        raise IndexError(
                            "inconsistent parameters for %s[%d, %d, %d]" %
                            (sym, h, i, j))
        return a

    def _reorder(self, order):
        """
        Check and normalize a given order of relations or eigenspaces.
        """
        if len(order) == 1 and isinstance(order[0], (tuple, list)):
            order = order[0]
        if 0 in order:
            assert order[0] == 0, "zero cannot be reordered"
        else:
            order = [0] + list(order)
        assert len(order) == self._.d + 1, "wrong number of indices"
        assert set(order) == set(range(self._.d + 1)), \
            "repeating or nonexisting indices"
        return tuple(order)

    @staticmethod
    def _subconstituent_name(h):
        """
        Return a properly formatted ordinal for the given subconstituent.
        """
        if h == 1:
            o = "1st"
        elif h == 2:
            o = "2nd"
        elif h == 3:
            o = "3rd"
        else:
            o = "%dth" % h
        return "%s subconstituent" % o

    def _subs(self, exp, p, seen):
        """
        Substitute the given subexpressions in the parameters.
        """
        if id(self) in seen:
            return (seen[id(self)], False)
        seen[id(self)] = p
        if self._has("p") and not p._has("p"):
            p._.p = self._.p.subs(*exp)
        if self._has("q") and not p._has("q"):
            p._.q = self._.q.subs(*exp)
        if self._has("P") and not p._has("P"):
            p._.P = self._.P.subs(*exp)
        if self._has("Q") and not p._has("Q"):
            p._.Q = self._.Q.subs(*exp)
        for k, v in self._.triple.items():
            p._.triple[k] = v.subs(*exp)
        for k, v in self._.quadruple.items():
            p._.quadruple[k] = v.subs(*exp)
        for par, part in self._.subschemes.items():
            try:
                p.add_subscheme(par.subs(*exp, seen=seen), part)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part=part)
        for par, part in self._.fusion_schemes.items():
            try:
                p.add_subscheme(par.subs(*exp, seen=seen), part)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part=part)
        for h, s in enumerate(self._.subconstituents):
            if s is None:
                continue
            s, refs = s
            name = self._subconstituent_name(h)
            try:
                p._.subconstituents[h] = (p.add_subscheme(
                    s.subs(*exp, seen=seen), name), refs)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part=name)
        if self._has("complement") and not p._has("complement"):
            try:
                p._.complement = self._.complement.subs(*exp, seen=seen)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part="complement")
        return (p, True)

    def add_subscheme(self, par, part=None, replace=None):
        """
        Add a derived scheme into the list.
        """
        if par in self._.fusion_schemes:
            return next(s for s in self._.fusion_schemes if s == par)
        elif par in self._.subschemes:
            return next(s for s in self._.subschemes if s == par)
        elif not isinstance(par, ASParameters):
            try:
                par = ASParameters(*par)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part=part)
        if par._.n == self._.n:
            d = self._.fusion_schemes
        else:
            d = self._.subschemes
        if replace is not None and replace in d:
            part = d.pop(replace)
        d[par] = part
        return par

    def all_fusions(self):
        """
        Return a dictionary of parameters for all fusion schemes.
        """
        out = {}
        if self._has("p"):
            fun = self.merge_subconstituents
        elif self._has("q"):
            fun = self.merge_eigenspaces
        elif self._has("P"):
            fun = self.merge_subconstituents
        elif self._has("Q"):
            fun = self.merge_eigenspaces
        for parts in SetPartitions(range(1, self._.d+1)):
            if len(parts) == self._.d:
                continue
            parts = tuple(tuple(sorted(p)) for p in parts)
            try:
                out[parts] = fun(*parts)
            except IndexError:
                pass
        return out

    def all_subconstituents(self, compute=False):
        """
        Return a dictionary of parameters for subconstituents
        which are known to be association schemes.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        out = {}
        for i in range(self._.d+1):
            try:
                out[i] = self.subconstituent(i, compute=compute)
            except IndexError:
                pass
        return out

    def check_feasible(self, checked=None, skip=None, derived=None, levels=3,
                       queue=None, part=()):
        """
        Check whether the parameter set is feasible.
        """
        if self._is_trivial():
            return
        par = self._get_parameters()
        if checked is None:
            checked = set()
        if par in checked:
            return
        if skip is None:
            skip = set()
        elif isinstance(skip, str):
            skip = {skip}
        else:
            skip = set(skip)
        for i, lvl in enumerate(self._checklist[:levels]):
            for name, check in lvl:
                if name not in skip:
                    check(self)
                    if i > 1:
                        skip.add(name)
        if (derived is None and self.is_complete_multipartite()) \
                or not derived:
            return
        if par is not None:
            checked.add(par)
        do_bfs = False
        if queue is None:
            queue = []
            do_bfs = True
        for par, pt, refs, reorder in \
                self._derived(derived or derived is None):
            if par in checked:
                continue
            queue.append((par, (pt, *part), refs, skip if reorder else None))
        if do_bfs:
            i = 0
            while i < len(queue):
                par, pt, refs, skip = queue[i]
                try:
                    par.check_feasible(checked=checked, skip=skip,
                                       derived=derived, levels=levels,
                                       queue=queue, part=pt)
                except (InfeasibleError, AssertionError) as ex:
                    raise InfeasibleError(ex, refs=refs, part=pt)
                i += 1

    def check_handshake(self):
        """
        Verify the handshake lemma for all relations in all subconstituents.
        """
        if not self._has("k"):
            self.kTable()
        if not self._has("p"):
            self.pTable()
        d = [self._.d, 0 if self.METRIC else self._.d]
        b = 2 if self._.bipartite else 1
        odd = not is_divisible(self._.n, 2)
        ndiv3 = not is_divisible(self._.n, 3)
        for i in range(1, self._.d + 1):
            d[1] += 2
            if not is_divisible(self._.k[i], 2):
                if odd:
                    raise InfeasibleError("handshake lemma not satisfied "
                                          "for relation %d" % i)
                for j in range(b, min(d) + 1, b):
                    if not is_divisible(self._.p[i, i, j], 2):
                        raise InfeasibleError("handshake lemma not satisfied"
                                              " for relation %d in"
                                              " subconstituent %d" % (j, i))
            if ndiv3 and not is_divisible(self._.k[i], 3) \
                    and not is_divisible(self._.p[i, i, i], 3):
                raise InfeasibleError("handshake lemma not satisfied "
                                      "for triangles in relation %d" % i)

    def classes(self):
        """
        Return the number of classes of the association scheme.
        """
        return self._.d

    def complement(self):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        assert self._.d == 2, "the complement is only defined for two classes"
        return self._.complement

    def dualEigenmatrix(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the dual eigenmatrix of the association scheme.
        """
        self._compute_dualEigenmatrix(expand=expand, factor=factor,
                                      simplify=simplify)
        self._check_eigenmatrices()
        rewriteMatrix(self._.Q, expand=expand, factor=factor,
                      simplify=simplify)
        return Matrix(SR, self._.Q)

    def eigenmatrix(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the eigenmatrix of the association scheme.
        """
        self._compute_primalEigenmatrix(expand=expand, factor=factor,
                                        simplify=simplify)
        self._check_eigenmatrices()
        rewriteMatrix(self._.P, expand=expand, factor=factor,
                      simplify=simplify)
        return Matrix(SR, self._.P)

    def is_complete_multipartite(self):
        """
        Check whether the association scheme
        corresponds to a complete multipartite graph.
        """
        if self._.d != 2:
            return False
        if not self._has("p"):
            self.pTable()
        return any(self._.p[0, i, i] == self._.p[j, i, i]
                   for i, j in [(1, 2), (2, 1)])

    def is_formallySelfDual(self):
        """
        Check whether the association scheme is formally self-dual.
        """
        if not self._has("fsd"):
            self._.fsd = (self.eigenmatrix(simplify=2)
                          - self.dualEigenmatrix(simplify=2)).is_zero()
        return self._.fsd

    def is_pPolynomial(self):
        """
        Check whether the association scheme is P-polynomial,
        and return all P-polynomial orderings if it is.
        """
        if not self._has("p"):
            self.pTable()
        if not self._has("pPolynomial_ordering"):
            pPoly = tuple(filter(None, (self._is_polynomial(self._.p, i)
                                        for i in range(1, self._.d+1))))
            self._.pPolynomial_ordering = False if len(pPoly) == 0 else pPoly
        return self._.pPolynomial_ordering

    def is_qPolynomial(self):
        """
        Check whether the association scheme is Q-polynomial,
        and return all Q-polynomial orderings if it is.
        """
        if not self._has("q"):
            self.kreinParameters()
        if not self._has("qPolynomial_ordering"):
            qPoly = tuple(filter(None, (self._is_polynomial(self._.q, i)
                                        for i in range(1, self._.d+1))))
            self._.qPolynomial_ordering = False if len(qPoly) == 0 else qPoly
        return self._.qPolynomial_ordering

    def kTable(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the valencies of the relations.
        """
        self._compute_kTable(expand=expand, factor=factor,
                             simplify=simplify)
        self._.k = rewriteTuple(self._.k, expand=expand, factor=factor,
                                simplify=simplify)
        return self._.k

    def merge_eigenspaces(self, *parts):
        """
        Return a parameter set for a scheme with merged eigenspaces.
        """
        parts = [list(pt) for pt in parts]
        if parts[0] != [0]:
            parts.insert(0, [0])
        if not self._has("q"):
            self.kreinParameters()
        par = ASParameters(q=self._merge_parts(parts, self._.q, "q"))
        self.add_subscheme(par,
                           "Fusion scheme for eigenspaces %s" % parts)
        return par

    def merge_relations(self, *parts):
        """
        Return a parameter set for a scheme with merged relations.
        """
        parts = [list(pt) for pt in parts]
        if parts[0] != [0]:
            parts.insert(0, [0])
        if not self._has("p"):
            self.pTable()
        par = ASParameters(p=self._merge_parts(parts, self._.p, "p"))
        self.add_subscheme(par,
                           "Fusion scheme for relations %s" % parts)
        return par

    def mTable(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the multiplicities of the eigenspaces.
        """
        self._compute_multiplicities(expand=expand, factor=factor,
                                     simplify=simplify)
        self._.m = rewriteTuple(self._.m, expand=expand, factor=factor,
                                simplify=simplify)
        return self._.m

    def polynomialOrders(self):
        """
        Return a dictionary of all P- or Q-polynomial orderings.
        """
        from .drg import DRGParameters
        from .qpoly import QPolyParameters
        out = {}
        if self.is_pPolynomial():
            for order in self._.pPolynomial_ordering:
                pa = self.add_subscheme(DRGParameters(self, order=order),
                                        f"P-polynomial ordering {order}")
                out["P", order] = pa
        if self.is_qPolynomial():
            for order in self._.qPolynomial_ordering:
                pa = self.add_subscheme(QPolyParameters(self, order=order),
                                        f"Q-polynomial ordering {order}")
                out["Q", order] = pa
        return out

    def pTable(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the intersection numbers.
        """
        self._compute_pTable(expand=expand, factor=factor, simplify=simplify)
        self._.p.rewrite(expand=expand, factor=factor, simplify=simplify)
        return self._.p

    def qTable(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the Krein parameters.
        """
        self._compute_kreinParameters(expand=expand, factor=factor,
                                      simplify=simplify)
        self._.q.rewrite(expand=expand, factor=factor, simplify=simplify)
        return self._.q

    def quadrupleEquations(self, h, i, j, r, s, t, krein=None, params=None,
                           solve=True, fresh=False, save=None):
        """
        Solve equations for quadruples of vertices ``w, x, y, z``
        such that ``d(w, x) = h``, ``d(w, y) = i``, ``d(w, z) = j``,
        ``d(x, y) = r``, ``d(x, z) = s``, ``d(y, z) = t``.

        If ``krein`` is a list of quadruples,
        the corresponding equations are used;
        otherwise, equations for quadruples ``(A, B, C, D)``
        such that for every ``E``, ``q[E, A, B] * q[E, C, D]`` is zero,
        are used.
        If ``params`` is a dictionary mapping strings to quadruples,
        the keys will be used as variables mapped to quadruple intersection
        numbers for corresponding quadruples.
        If ``solve`` is ``False``,
        only a list of equations and a set of variables is returned,
        without solving the equations.
        """
        if solve and krein is None and params is None:
            qh = (h, i, j, r, s, t)
            if qh not in self._.quadruple:
                for p, q in zip(QHPERMS, QDPERMS):
                    hp = tuple(qh[i] for i in p)
                    if hp in self._.quadruple:
                        self._.quadruple[qh] = self._.quadruple[hp].permute(q)
                        break
            if qh in self._.quadruple:
                s = self._.quadruple[qh]
                if fresh:
                    vars = set(s.variables()).difference(self._.vars)
                    if len(vars) > 0:
                        s = s.subs(*refresh(vars))
                        if save:
                            self._.quadruple[qh] = s
                return s
        Swxy = self.tripleEquations(h, i, r, fresh=True, save=save)
        assert checkPos(Swxy[j, s, t]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        Swxz = self.tripleEquations(h, j, s, fresh=True, save=save)
        assert checkPos(Swxz[i, r, t]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        Swyz = self.tripleEquations(i, j, t, fresh=True, save=save)
        assert checkPos(Swyz[h, r, s]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        Sxyz = self.tripleEquations(r, s, t, fresh=True, save=save)
        assert checkPos(Sxyz[h, i, j]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        out = []
        R = range(self._.d+1)
        S = [[[[Integer(1) if (A, B, C, D) in [(j, s, t, 0), (i, r, 0, t),
                                               (h, 0, r, s), (0, h, i, j)]
                else SR.symbol("%s_%d_%d_%d_%d_%d_%d_%d_%d_%d_%d" %
                               (self._.prefix, h, i, j, r, s, t, A, B, C, D))
                for D in R] for C in R] for B in R] for A in R]
        vars = {x for SA in S for SB in SA for SC in SB for x in SC
                if not isinstance(x, Integer)}
        for U in R:
            for V in R:
                for W in R:
                    if Swxy[U, V, W] == sum(S[U][V][W][X] for X in R
                                            if S[U][V][W][X] not in vars):
                        for X in R:
                            if S[U][V][W][X] in vars:
                                vars.discard(S[U][V][W][X])
                                S[U][V][W][X] = Integer(0)
                    if Swxz[U, V, W] == sum(S[U][V][X][W] for X in R
                                            if S[U][V][X][W] not in vars):
                        for X in R:
                            if S[U][V][X][W] in vars:
                                vars.discard(S[U][V][X][W])
                                S[U][V][X][W] = Integer(0)
                    if Swyz[U, V, W] == sum(S[U][X][V][W] for X in R
                                            if S[U][X][V][W] not in vars):
                        for X in R:
                            if S[U][X][V][W] in vars:
                                vars.discard(S[U][X][V][W])
                                S[U][X][V][W] = Integer(0)
                    if Sxyz[U, V, W] == sum(S[X][U][V][W] for X in R
                                            if S[X][U][V][W] not in vars):
                        for X in R:
                            if S[X][U][V][W] in vars:
                                vars.discard(S[X][U][V][W])
                                S[X][U][V][W] = Integer(0)
        consts = set()
        c = [[[[len([X for X in R if S[U][V][W][X] in vars])
                for W in R] for V in R] for U in R],
             [[[len([X for X in R if S[U][V][X][W] in vars])
                for W in R] for V in R] for U in R],
             [[[len([X for X in R if S[U][X][V][W] in vars])
                for W in R] for V in R] for U in R],
             [[[len([X for X in R if S[X][U][V][W] in vars])
                for W in R] for V in R] for U in R]]
        q = []
        for X, cX in enumerate(c):
            for U, cU in enumerate(cX):
                for V, cV in enumerate(cU):
                    for W, n in enumerate(cV):
                        if n == 1:
                            q.append((X, U, V, W))
        while len(q) > 0:
            X, U, V, W = q.pop()
            if c[X][U][V][W] == 0:
                continue
            A, B, C, D = [(U, V, W, None), (U, V, None, W),
                          (U, None, V, W), (None, U, V, W)][X]
            if D is None:
                D = next(Y for Y in R if S[A][B][C][Y] in vars)
                x = S[A][B][C][D]
                S[A][B][C][D] = Swxy[A, B, C] - sum(S[A][B][C][Y] for Y in R
                                                    if Y != D)
            elif C is None:
                C = next(Y for Y in R if S[A][B][Y][D] in vars)
                x = S[A][B][C][D]
                S[A][B][C][D] = Swxz[A, B, D] - sum(S[A][B][Y][D] for Y in R
                                                    if Y != C)
            elif B is None:
                B = next(Y for Y in R if S[A][Y][C][D] in vars)
                x = S[A][B][C][D]
                S[A][B][C][D] = Swyz[A, C, D] - sum(S[A][Y][C][D] for Y in R
                                                    if Y != B)
            elif A is None:
                A = next(Y for Y in R if S[Y][B][C][D] in vars)
                x = S[A][B][C][D]
                S[A][B][C][D] = Sxyz[B, C, D] - sum(S[Y][B][C][D] for Y in R
                                                    if Y != A)
            for Y, U, V, W in [(0, A, B, C), (1, A, B, D),
                               (2, A, C, D), (3, B, C, D)]:
                c[Y][U][V][W] -= 1
                if c[Y][U][V][W] == 1:
                    q.append((Y, U, V, W))
            out.append(x == S[A][B][C][D])
            consts.add(x)
        for U in R:
            for V in R:
                for W in R:
                    Z = sum(S[U][V][W][X] for X in R) - Swxy[U, V, W]
                    if isinstance(Z, Integer) or Z.is_constant():
                        assert Z == 0, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                            (h, i, r, U, V, W)
                    else:
                        out.append(Z == 0)
                    Z = sum(S[U][V][X][W] for X in R) - Swxz[U, V, W]
                    if isinstance(Z, Integer) or Z.is_constant():
                        assert Z == 0, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                            (h, j, s, U, V, W)
                    else:
                        out.append(Z == 0)
                    Z = sum(S[U][X][V][W] for X in R) - Swyz[U, V, W]
                    if isinstance(Z, Integer) or Z.is_constant():
                        assert Z == 0, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                            (i, j, t, U, V, W)
                    else:
                        out.append(Z == 0)
                    Z = sum(S[X][U][V][W] for X in R) - Sxyz[U, V, W]
                    if isinstance(Z, Integer) or Z.is_constant():
                        assert Z == 0, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                            (r, s, t, U, V, W)
                    else:
                        out.append(Z == 0)
        if krein is None:
            if save is None:
                save = True
            Rs = set(R)
            pairs = {(A, B): {C for C in R if self._.q[C, A, B] == 0}
                     for A in R for B in R}
            krein = [(A, B, C, D)
                     for (A, B), AB in pairs.items()
                     for (C, D), CD in pairs.items() if AB | CD == Rs]
        if krein:
            for A, B, C, D in krein:
                Z = sum(self._.Q[tA, A] * self._.Q[tB, B] *
                        self._.Q[tC, C] * self._.Q[tD, D] *
                        S[tA][tB][tC][tD]
                        for tA in R for tB in R for tC in R for tD in R)
                if isinstance(Z, Integer):
                    assert Z == 0, \
                        "Krein equation for (%d, %d, %d, %d) " \
                        "not satisfied" % (A, B, C, D)
                else:
                    out.append(Z == 0)
        if params:
            for a, (A, B, C, D) in params.items():
                x = SR.symbol(a)
                out.append(S[A][B][C][D] == x)
        vars.intersection_update(x for SA in S for SB in SA
                                 for SC in SB for x in SC)
        vars.update(consts)
        vars.update(Swxy.variables())
        vars.update(Swxz.variables())
        vars.update(Swyz.variables())
        vars.update(Sxyz.variables())
        if not solve:
            return (out, vars)
        sol = _solve(out, tuple(vars))
        assert len(sol) > 0, "system of equations has no solution"
        Q = Array4D(self._.d + 1)
        for A in R:
            for B in R:
                for C in R:
                    for D in R:
                        if isinstance(S[A][B][C][D], Integer):
                            Q[A, B, C, D] = S[A][B][C][D]
                        else:
                            Q[A, B, C, D] = S[A][B][C][D].subs(sol[0])
        if save:
            self._.quadruple[h, i, j, r, s, t] = Q
        return Q

    def reorderEigenspaces(self, *order):
        """
        Specify a new order for the eigenspaces.
        """
        order = self._reorder(order)
        if self._has("m"):
            self._.m = tuple(self._.m[i] for i in order)
        if self._has("P"):
            self._.P = Matrix(SR, [self._.P[i] for i in order])
        if self._has("Q"):
            self._.Q = Matrix(SR, [[r[j] for j in order] for r in self._.Q])
        if self._has("q"):
            self._.q.reorder(order)
        if self._has("qPolynomial_ordering") and self._.qPolynomial_ordering:
            self._.qPolynomial_ordering = sorted(
                [tuple(order.index(i) for i in o)
                 for o in self._.qPolynomial_ordering])

    def reorderRelations(self, *order):
        """
        Specify a new order for the relations.
        """
        order = self._reorder(order)
        if self._has("k"):
            self._.k = tuple(self._.k[i] for i in order)
        if self._has("P"):
            self._.P = Matrix(SR, [[r[j] for j in order] for r in self._.P])
        if self._has("Q"):
            self._.Q = Matrix(SR, [self._.Q[i] for i in order])
        if self._has("p"):
            self._.p.reorder(order)
        self._.triple = {tuple(order.index(i) for i in t):
                         s.reorder(order, inplace=False)
                         for t, s in self._.triple.items()}
        self._.triple_solution = {tuple(order.index(i) for i in t):
                                  {k: s.reorder(order, inplace=False)
                                   for k, s in d.items()}
                                  for t, d in self._.triple_solution.items()}
        self._.triple_solution_generator = \
            {tuple(order.index(i) for i in t): g
             for t, g in self._.triple_solution_generator.items()}
        self._.quadruple = {tuple(order.index(i) for i in t):
                            s.reorder(order, inplace=False)
                            for t, s in self._.quadruple.items()}
        self._.subconstituents = [self._.subconstituents[i] for i in order]
        if self._has("pPolynomial_ordering") and self._.pPolynomial_ordering:
            self._.pPolynomial_ordering = sorted(
                [tuple(order.index(i) for i in o)
                 for o in self._.pPolynomial_ordering])

    def set_vars(self, vars):
        """
        Set the order of the variables for eigenvalue sorting.
        """
        if vars is False:
            self._.vars_ordered = False
        else:
            self._.vars = tuple(vars) + tuple(x for x in self._.vars
                                              if x not in vars)
            self._.vars_ordered = True

    def subconstituent(self, h, compute=False, return_rels=False):
        """
        Return parameters of the ``h``-th subconstituent
        if it is known to form an association scheme.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        if not self._has("p"):
            self.pTable()
        name = self._subconstituent_name(h)
        rels = None
        assert checkPos(self._.p[0, h, h]), \
            "%s consists of a single vertex" % name
        if self._.d == 2:
            compute = True
        if self._.subconstituents[h] is None:
            rels = [i for i in range(self._.d+1)
                    if checkPos(self._.p[h, h, i])]
            d = len(rels)
            if compute:
                for i in rels:
                    self.tripleEquations(h, h, i)
            vars = set(self._.vars)
            a = Array3D(d)
            try:
                for i in range(d):
                    for j in range(d):
                        for k in range(d):
                            a[i, j, k] = next(
                                x for x in
                                self.triple_generator((h, h, i), (h, j, k))
                                if vars.issuperset(variables(x)))
            except StopIteration:
                raise IndexError("%s is not known to be an association scheme"
                                 % name)
            subc = self.add_subscheme(ASParameters(p=a), name)
            refs = []
            self._.subconstituents[h] = (subc, refs)
        else:
            subc, refs = self._.subconstituents[h]
        if return_rels:
            return (subc, refs, rels)
        else:
            return subc

    def subs(self, *exp, **kargs):
        """
        Substitute the given subexpressions in the parameters.
        """
        par = {}
        if self._has("p"):
            par["p"] = self._.p.subs(*exp)
        elif self._has("q"):
            par["q"] = self._.q.subs(*exp)
        elif self._has("P"):
            par["P"] = self._.P.subs(*exp)
        elif self._has("Q"):
            par["Q"] = self._.Q.subs(*exp)
        p, new = self._subs(exp, ASParameters(**par), kargs.get("seen", {}))
        return p

    def triple_generator(self, t, d):
        """
        Generate computed values of triple intersecion numbers
        counting the number of vertices at distances given by the triple d
        corresponding to vertices at mutual distances given by the triple t.
        """
        if 0 in t:
            j = t.index(0)
            h = {x for k, x in enumerate(t) if j != k}
            if len(h) == 2:
                return
            i = {x for k, x in enumerate(d) if j+k != 2}
            if len(i) == 2:
                yield Integer(0)
                return
            h = next(iter(h))
            i = next(iter(i))
            j = d[2-j]
            yield self._.p[h, i, j]
            return
        for p, q in zip(TPERMS, DPERMS):
            tp = tuple(t[i] for i in p)
            if tp in self._.triple:
                yield self._.triple[tp][tuple(d[i] for i in q)]

    def tripleEquations(self, u, v, w, krein=None, params=None,
                        solve=True, fresh=False, save=None):
        """
        Solve equations for triples of vertices
        in relations ``u``, ``v``, ``w``.

        If ``krein`` is a list of triples,
        the corresponding equations are used;
        otherwise, equations for zero Krein parameters are used.
        If ``params`` is a dictionary mapping strings to triples,
        the keys will be used as variables mapped to triple intersection
        numbers for corresponding triples.
        If ``solve`` is ``False``,
        only a list of equations and a set of variables is returned,
        without solving the equations.
        """
        if solve and krein is None and params is None:
            t = (u, v, w)
            if t not in self._.triple:
                for p, q in zip(TPERMS, DPERMS):
                    tp = tuple(t[i] for i in p)
                    if tp in self._.triple:
                        self._.triple[t] = self._.triple[tp].permute(q)
                        break
            if t in self._.triple:
                s = self._.triple[t]
                if fresh:
                    vars = set(s.variables()).difference(self._.vars)
                    if len(vars) > 0:
                        s = s.subs(*refresh(vars))
                        if save:
                            self._.triple[t] = s
                return s
        if not self._has("Q"):
            self.dualEigenmatrix()
        if not self._has("p"):
            self.pTable()
        assert checkPos(self._.p[u, v, w]), \
            "no triple of vertices in relations %d, %d, %d" % (u, v, w)
        if not self._has("q"):
            self.kreinParameters()
        out = []
        r = range(self._.d+1)
        s = [[[Integer(1) if (h, i, j) in [(v, w, 0), (u, 0, w), (0, u, v)]
               else SR.symbol("%s_%d_%d_%d_%d_%d_%d" %
                              (self._.prefix, u, v, w, h, i, j))
               for j in r] for i in r] for h in r]
        for i in r:
            for j in r:
                if self._.p[u, i, j] == sum(s[i][j][t] for t in r
                                            if isinstance(s[i][j][t],
                                                          Integer)):
                    for t in r:
                        if not isinstance(s[i][j][t], Integer):
                            s[i][j][t] = Integer(0)
                if self._.p[v, i, j] == sum(s[i][t][j] for t in r
                                            if isinstance(s[i][t][j],
                                                          Integer)):
                    for t in r:
                        if not isinstance(s[i][t][j], Integer):
                            s[i][t][j] = Integer(0)
                if self._.p[w, i, j] == sum(s[t][i][j] for t in r
                                            if isinstance(s[t][i][j],
                                                          Integer)):
                    for t in r:
                        if not isinstance(s[t][i][j], Integer):
                            s[t][i][j] = Integer(0)
        vars = set(x for x in sum([sum(l, []) for l in s], [])
                   if not isinstance(x, Integer))
        consts = set()
        c = [[[len([t for t in r if s[i][j][t] in vars])
               for j in r] for i in r],
             [[len([t for t in r if s[i][t][j] in vars])
               for j in r] for i in r],
             [[len([t for t in r if s[t][i][j] in vars])
               for j in r] for i in r]]
        q = []
        for h, ch in enumerate(c):
            for i, ci in enumerate(ch):
                for j, n in enumerate(ci):
                    if n == 1:
                        q.append((h, i, j))
        while len(q) > 0:
            l, i, j = q.pop()
            if c[l][i][j] == 0:
                continue
            h, i, j = [(i, j, None), (i, None, j), (None, i, j)][l]
            if j is None:
                j = next(t for t in r if s[h][i][t] in vars)
                x = s[h][i][j]
                s[h][i][j] = self._.p[u, h, i] - sum(s[h][i][t] for t in r
                                                     if t != j)
                c[1][h][j] -= 1
                c[2][i][j] -= 1
                if c[1][h][j] == 1:
                    q.append((1, h, j))
                if c[2][i][j] == 1:
                    q.append((2, i, j))
            elif i is None:
                i = next(t for t in r if s[h][t][j] in vars)
                x = s[h][i][j]
                s[h][i][j] = self._.p[v, h, j] - sum(s[h][t][j] for t in r
                                                     if t != i)
                c[0][h][i] -= 1
                c[2][i][j] -= 1
                if c[0][h][i] == 1:
                    q.append((0, h, i))
                if c[2][i][j] == 1:
                    q.append((2, i, j))
            elif h is None:
                h = next(t for t in r if s[t][i][j] in vars)
                x = s[h][i][j]
                s[h][i][j] = self._.p[w, i, j] - sum(s[t][i][j] for t in r
                                                     if t != h)
                c[0][h][i] -= 1
                c[1][h][j] -= 1
                if c[0][h][i] == 1:
                    q.append((0, h, i))
                if c[1][h][j] == 1:
                    q.append((1, h, j))
            out.append(x == s[h][i][j])
            consts.add(x)
        for i in r:
            for j in r:
                l = sum(s[i][j][t] for t in r)
                if isinstance(l, Integer):
                    assert self._.p[u, i, j] == l, \
                        "value of p[%d, %d, %d] exceeded" % (u, i, j)
                else:
                    out.append(self._.p[u, i, j] == l)
                l = sum(s[i][t][j] for t in r)
                if isinstance(l, Integer):
                    assert self._.p[v, i, j] == l, \
                        "value of p[%d, %d, %d] exceeded" % (v, i, j)
                else:
                    out.append(self._.p[v, i, j] == l)
                l = sum(s[t][i][j] for t in r)
                if isinstance(l, Integer):
                    assert self._.p[w, i, j] == l, \
                        "value of p[%d, %d, %d] exceeded" % (w, i, j)
                else:
                    out.append(self._.p[w, i, j] == l)
        if krein is None:
            if save is None:
                save = True
            krein = []
            for h in range(1, self._.d+1):
                for i in range(1, self._.d+1):
                    for j in range(1, self._.d+1):
                        if self._.q[h, i, j] == 0:
                            krein.append((h, i, j))
        if krein:
            for h, i, j in krein:
                l = sum(self._.Q[th, h] * self._.Q[ti, i] *
                        self._.Q[tj, j] * s[th][ti][tj]
                        for th in r for ti in r for tj in r)
                if isinstance(l, Integer):
                    assert l == 0, \
                        "Krein equation for (%d, %d, %d) not satisfied" % \
                        (h, i, j)
                else:
                    out.append(l == 0)
        if params:
            for a, (h, i, j) in params.items():
                x = symbol(a)
                out.append(s[h][i][j] == x)
        vars.intersection_update(sum([sum(l, []) for l in s], []))
        vars.update(consts)
        if not solve:
            return (out, vars)
        sol = _solve(out, tuple(vars))
        assert len(sol) > 0, "system of equations has no solution"
        S = Array3D(self._.d + 1)
        for h in r:
            for i in r:
                for j in r:
                    if isinstance(s[h][i][j], Integer):
                        S[h, i, j] = s[h][i][j]
                    else:
                        S[h, i, j] = s[h][i][j].subs(sol[0])
        if save:
            self._.triple[u, v, w] = S
        return S

    def tripleSolution_generator(self, u, v, w, S=None, solver=None):
        """
        Return a generator of solutions for triples of vertices
        in relations ``u``, ``v``, ``w``.

        If ``S`` is ``None``,
        then the appropriate general solution is computed.
        """
        if S is None:
            S = self.tripleEquations(u, v, w)
        return find(make_expressions((S[h, i, j], 0,
                                      min(self._.p[u, h, i],
                                          self._.p[v, h, j],
                                          self._.p[w, i, j]))
                                     for h in range(self._.d + 1)
                                     for i in range(self._.d + 1)
                                     for j in range(self._.d + 1)),
                    S.variables(), solver=solver)

    def variables(self):
        """
        Return the variables in the graph parameters.
        """
        return self._.vars

    @Param
    def d(self):
        """
        Access function for the number of classes of the scheme.
        """
        pass

    @Param
    def k(self):
        """
        Access function for the table of valencies of the scheme.
        """
        self.kTable()

    @Param
    def m(self):
        """
        Access function for the table of multiplicities of the scheme.
        """
        self.mTable()

    @Param
    def n(self):
        """
        Access function for the number of vertices of the scheme.
        """
        pass

    @Param
    def p(self):
        """
        Access function for the table of intersection numbers of the scheme.
        """
        self.pTable()

    @Param
    def P(self):
        """
        Access function for the eigenmatrix of the scheme.
        """
        self.eigenmatrix()

    @Param
    def q(self):
        """
        Access function for the table of Krein parameters of the scheme.
        """
        self.qTable()

    @Param
    def Q(self):
        """
        Access function for the dual eigenmatrix of the scheme.
        """
        self.dualEigenmatrix()

    @check(0)
    def check_sporadic(self):
        """
        Check whether the association scheme has parameters
        for which nonexistence has been shown sporadically.
        """
        par = self._get_parameters()
        if par is None:
            return
        if par in sporadic:
            raise InfeasibleError(refs=sporadic[par])

    @check(0)
    def check_family(self):
        """
        Check whether the association scheme has parameters for which
        nonexistence has been shown as a part of an infinite family.
        """
        self._check_family()

    @check(2)
    def check_absoluteBound(self, expand=False, factor=False,
                            simplify=False):
        """
        Check whether the absolute bound is not exceeded.
        """
        if not self._has("m"):
            self.multiplicities(expand=expand, factor=factor,
                                simplify=simplify)
        if not self._has("q"):
            self.kreinParameters(expand=expand, factor=factor,
                                 simplify=simplify)
        ineqs = {}
        for i in range(self._.d + 1):
            ineq = self._.m[i]*(self._.m[i] + 1)/2 - \
                sum(self._.m[h] for h in range(self._.d + 1)
                    if self._.q[h, i, i] != 0)
            if ineq < 0:
                raise InfeasibleError("absolute bound exceeded "
                                      "for (%d, %d)" % (i, i))
            elif not (ineq >= 0):
                ineqs[i, i] = rewriteExp(ineq, expand=expand,
                                         factor=factor, simplify=simplify)
            for j in range(i+1, self._.d + 1):
                ineq = self._.m[i]*self._.m[j] - \
                    sum(self._.m[h] for h in range(self._.d + 1)
                        if self._.q[h, i, j] != 0)
                if ineq < 0:
                    raise InfeasibleError("absolute bound exceeded "
                                          "for (%d, %d)" % (i, j))
                elif not (ineq >= 0):
                    ineqs[i, j] = rewriteExp(ineq, expand=expand,
                                             factor=factor,
                                             simplify=simplify)
        return ineqs

    @check(2)
    def check_schoenberg(self, expand=False, factor=False, simplify=False):
        """
        Check whether Schönberg's theorem holds.
        """
        if len(self._.vars) > 0:
            return
        if not self._has("P"):
            self.eigenmatrix(expand=expand, factor=factor, simplify=simplify)
        if not self._has("Q"):
            self.dualEigenmatrix(expand=expand, factor=factor,
                                 simplify=simplify)
        if not self._has("q"):
            self.kreinParameters(expand=expand, factor=factor,
                                 simplify=simplify)
        from .qpoly import QPolyParameters
        if not isinstance(self, QPolyParameters) and self.is_qPolynomial():
            order = next(iter(self._.qPolynomial_ordering))
            try:
                QPolyParameters(self, order=order).check_schoenberg()
            except InfeasibleError as ex:
                raise InfeasibleError(ex, part=f"Q-polynomial ordering {order}")
            return
        rr = range(self._.d + 1)
        t = SR.symbol("__t")
        d, n = self._init_schoenberg()
        for i in rr:
            if self._.Q[0, i] <= 2:
                continue
            lm = [(q / self._.Q[0, i])**2 for q, in self._.Q[:, i]]
            if 1 in lm[1:d+1]:
                continue
            L = [identity_matrix(SR, self._.d + 1),
                 Matrix(SR, [[self._.q[h, i, j] for j in rr] for h in rr])
                 / self._.Q[0, i]]
            l = 0
            G = [1] * d
            PP = [self._.P[0, j+1] * (1 + lm[j+1]) for j in range(d)]
            while sum(g*pp for g, pp in zip(G, PP)) > n:
                if l >= 2:
                    L.append(L[1] * L[-1])
                    M = sum(integralize(2**l * c) * L[e] for c, e in
                            gegenbauer(l, self._.Q[0, i]/2 - 1, t)
                            .coefficients(t))
                    if any(m < 0 for m, in M[:, 0]):
                        raise InfeasibleError("Gegenbauer polynomial %d "
                                              "on L*[%d] not nonnegative"
                                              % (l, i),
                                              ("Kodalen19", "Corollary 3.8."))
                l += 1
                mu = l / (l + self._.Q[0, i] - 2)
                for j in range(d):
                    G[j] *= lm[j+1] if lm[j+1] * (1 + mu)**2 >= 4*mu else mu

    @check(3)
    def check_quadruples(self, solver=None):
        """
        Check whether the existence of a forbidden quadruple of vertices
        is implied by the triple intersection numbers.
        """
        if not self._has("p"):
            self.pTable()
        r = self._.triple_solution = {}
        g = self._.triple_solution_generator = {}
        zero = {}
        done = {}
        for u in range(self._.d + 1):
            for v in range(u, self._.d + 1):
                for w in range(v, self._.d + 1):
                    if self._.p[u, v, w] == 0:
                        continue
                    S = self.tripleEquations(u, v, w)
                    g[u, v, w] = self.tripleSolution_generator(u, v, w, S=S,
                                                               solver=solver)
                    try:
                        sol = sort_solution(next(g[u, v, w]))
                    except StopIteration:
                        raise InfeasibleError(
                            "no solution found for a triple of vertices "
                            "at distances (%d, %d, %d)" % (u, v, w))
                    s = S.subs(sol)
                    r[u, v, w] = {sol: s}
                    zero[u, v, w] = {(h, i, j)
                                     for h in range(self._.d + 1)
                                     for i in range(self._.d + 1)
                                     for j in range(self._.d + 1)
                                     if s[h, i, j] == 0
                                     and self._check_zero(h, i, j, u, v, w)}
                    done[u, v, w] = set()
        check = {t for t in g if len(zero[t]) > 0}
        while len(check) > 0:
            for t in list(check):
                if t not in check:
                    continue
                check.discard(t)
                u, v, w = t
                for d in list(zero[t]):
                    if d not in zero[t]:
                        continue
                    try:
                        sol = sort_solution(
                            next(g[t].send((True,
                                            self._.triple[t][d] >= 1))))
                        if sol not in r[t]:
                            s = r[t][sol] = self._.triple[t].subs(sol)
                            zero[t] -= {z for z in zero[t] if s[z] != 0}
                    except (StopIteration, KeyError):
                        h, i, j = d
                        seen = {(t, d)}
                        for lt, ld in {((u, h, i), (v, w, j)),
                                       ((v, h, j), (u, w, i)),
                                       ((w, i, j), (u, v, h))}:
                            st = tuple(sorted(lt))
                            if st not in zero:
                                continue
                            for tp, dp in zip(TPERMS, DPERMS):
                                if tuple(lt[k] for k in tp) != st:
                                    continue
                                sd = tuple(ld[k] for k in dp)
                                if (st, sd) in seen:
                                    continue
                                seen.add((st, sd))
                                l = len(r[st])
                                delete = set()
                                for sol, s in r[st].items():
                                    if s[sd] != 0:
                                        delete.add(sol)
                                for sol in delete:
                                    del r[st][sol]
                                try:
                                    g[st].send((False,
                                                self._.triple[st][sd] == 0))
                                    if len(r[st]) == 0:
                                        sol = sort_solution(next(g[st]))
                                        r[st][sol] = \
                                            self._.triple[st].subs(sol)
                                        l += 1
                                except StopIteration:
                                    del g[st]
                                except KeyError:
                                    pass
                                if len(r[st]) == 0:
                                    raise InfeasibleError(
                                        "found forbidden quadruple "
                                        "wxyz with d(w, x) = %d, "
                                        "d(w, y) = %d, d(w, z) = %d, "
                                        "d(x, y) = %d, d(x, z) = %d, "
                                        "d(y, z) = %d" % (sd + st))
                                if len(r[st]) < l:
                                    zero[st] = {(sh, si, sj)
                                                for sh in range(self._.d + 1)
                                                for si in range(self._.d + 1)
                                                for sj in range(self._.d + 1)
                                                if
                                                (sh, si, sj) not in done[st]
                                                and self._check_zero(sh, si,
                                                                     sj, *st)
                                                and all(
                                                    s[sh, si, sj] == 0
                                                    for s in r[st].values())}
                                    if len(zero[st]) == 0:
                                        check.discard(st)
                                    else:
                                        check.add(st)
                        zero[t].discard(d)
                        done[t].add(d)

    intersectionNumbers = pTable
    kreinParameters = qTable
    merge_subconstituents = merge_relations
    multiplicities = mTable
    order = __len__
    valencies = kTable
    substitute = subs


class PolyASParameters(ASParameters):
    """
    A class for parameters of a polynomial association scheme
    and checking their feasibility.
    """

    ANTIPODAL = None
    ARRAY = None
    BIPARTITE = None
    DUAL_INTEGRAL = None
    DUAL_MATRIX = None
    DUAL_PARAMETER = None
    DUAL_PARTS = None
    DUAL_SIZES = None
    DUAL_SYMBOL = None
    MATRIX = None
    OBJECT = None
    OBJECT_LATEX = None
    PARAMETER = None
    PART = None
    PARTS = None
    PART_SCHEME = None
    PTR = None
    QTR = None
    SIZE = None
    SIZES = None
    SYMBOL = None

    def __init__(self, b, c=None, order=None):
        """
        Object constructor.

        Check the basic properties of the intersection or Krein array.
        """
        self._init_storage()
        if isinstance(b, ASParameters):
            ASParameters.__init__(self, b, complement=False)
            if not isinstance(b, PolyASParameters) and \
                    (b._has("P") or b._has("Q")):
                self._copy_cosineSequences(b)
            if order is not None:
                self.reorderParameters(*order)
        else:
            if self._.d is None:
                raise NotImplementedError("PolyASParameters can not be "
                                          "instantiated directly")
            assert self._.d == len(c) == len(b), "parameter length mismatch"
            self._init_array(b, c)
            assert all(checkPos(x) for x in self._.c[1:]), \
                "c sequence not positive"
            assert all(checkPos(x) for x in self._.b[:-1]), \
                "b sequence not positive"
            self._.a = tuple(full_simplify(b[0]-x-y)
                             for x, y in zip(self._.b, self._.c))
            assert self._.c[1] == 1, "Invalid c[1] value"
            assert all(checkNonneg(x) for x in self._.a), \
                "a values negative"
            self._.vars = tuple(set(sum(map(variables, tuple(b) + tuple(c)),
                                        ())))
            ASParameters.__init__(self, complement=False)
        self._.hash_parameters = self.parameterArray(factor=True, simplify=2)
        self._init_prefix()

    def __eq__(self, other):
        """
        Compare self to other.
        """
        if isinstance(other, self._get_class()):
            return self._.hash_parameters == other._.hash_parameters

        return not isinstance(other, ASParameters) \
            and self._.hash_parameters == other

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash((self.SYMBOL, self._.hash_parameters))

    def __repr__(self):
        """
        String representation.
        """
        return "Parameters of a {} with {} {}".format(self.OBJECT, self.ARRAY, self._format_parameterArray())

    def _ascii_art_(self):
        """
        ASCII art representation.
        """
        return ascii_art(f"Parameters of a {self.OBJECT} with {self.ARRAY} ",
                         self._format_parameterArray_ascii())

    def _check_family(self):
        """
        Check whether the association scheme has parameter array for which
        nonexistence has been shown as a part of an infinite family.
        """
        for (s, (b, c)), (cond, ref) in families.items():
            if s != self.SYMBOL or len(b) != self._.d:
                continue
            vars = tuple(set(sum(map(variables, b + c), ())))
            sols = _solve([SR(l) == r for l, r
                           in zip(self._.b[:-1] + self._.c[1:], b + c)],
                          vars)
            if any(checkConditions(cond, sol) for sol in sols
                   if is_integral(sol)):
                raise InfeasibleError(refs=ref)

    def _check_multiplicity(self, k, i):
        """
        Check the valency or multiplicity
        of the ``i``-th relation or eigenspace.
        """
        for j in range(self._.d + 1):
            if self._.a[i] >= k[i]:
                raise InfeasibleError("%s of %s %d too large" %
                                      (self.SIZE, self.PART, i))

    def _check_parameter(self, h, i, j, v, integral=False,
                         name=None, sym=None):
        """
        Check for the feasibility
        of an intersection number or Krein parameter.

        The parameter is checked for nonnegativity,
        and, if requested, also for integrality.
        """
        if name is None:
            name = self.PARAMETER
        if sym is None:
            sym = self.SYMBOL
        return ASParameters._check_parameter(h, i, j, v, integral=integral,
                                             name=name, sym=sym)

    def _complement(self, k, p):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        assert self._.d == 2, "the complement is only defined for two classes"
        if checkPos(self._.b[0] - self._.c[2]):
            return self._get_class()((k[2], p[2, 2, 1]),
                                     (Integer(1), p[1, 2, 2]),
                                     complement=self)
        else:
            return ASParameters._complement(self)

    def _compute_cosineSequences(self, expand=False, factor=False,
                                 simplify=False):
        """
        Compute the cosine sequences of the association scheme.
        """
        if self._has("omega"):
            return
        if not self._has("theta"):
            self.eigenvalues(expand=expand, factor=factor,
                             simplify=simplify)
        omega = Matrix(SR, self._.d + 1)
        omega[:, 0] = 1
        for i in range(self._.d + 1):
            omega[i, 1] = self._.theta[i]/self._.b[0]
            for j in range(2, self._.d + 1):
                omega[i, j] = _simplify(_factor((
                    (self._.theta[i] - self._.a[j-1]) * omega[i, j-1]
                    - self._.c[j-1] * omega[i, j-2]) / self._.b[j-1]))
        self._.omega = omega

    def _compute_dualEigenmatrix(self, expand=False, factor=False,
                                 simplify=False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        if self._has("Q"):
            return
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self._.Q = self._compute_eigenmatrix(self.multiplicities(**params),
                                             self.QTR, **params)

    def _compute_dualParameters(self, q, k, m, tr):
        """
        Compute the Krein parameters or intersection numbers
        from the cosine sequences.
        """
        for h in range(self._.d + 1):
            for i in range(self._.d + 1):
                for j in range(self._.d + 1):
                    q[h, i, j] = full_simplify(
                        sum(k[t] * self._.omega[tr(h, t)]
                            * self._.omega[tr(i, t)]
                            * self._.omega[tr(j, t)]
                            for t in range(self._.d + 1))
                        * m[i] * m[j] / self._.n)
                    self._check_parameter(h, i, j, q[h, i, j],
                                          integral=self.DUAL_INTEGRAL,
                                          name=self.DUAL_PARAMETER,
                                          sym=self.DUAL_SYMBOL)

    def _compute_eigenmatrix(self, k, tr, expand=False, factor=False,
                             simplify=False):
        """
        Compute and return the eigenmatrix of the association scheme.
        """
        if not self._has("omega"):
            self.cosineSequences(expand=expand, factor=factor,
                                 simplify=simplify)
        return Matrix(SR, [[self._.omega[tr(i, j)] * k[j]
                            for j in range(self._.d + 1)]
                           for i in range(self._.d + 1)])

    def _compute_eigenvalues(self, p, expand=False, factor=False,
                             simplify=False):
        """
        Compute and return the eigenvalues of the association scheme.
        """
        if not self._has("theta"):
            if self._has("omega"):
                self._.theta = tuple(r[1] * p[0, 1, 1] for r in self._.omega)
            elif self.is_cyclic():
                self._.theta = tuple(2*cos(2*i*pi/self._.n)
                                     for i in range(self._.d + 1))
            else:
                B = Matrix(SR, [M[1] for M in p])
                theta = [v for v in B.eigenvalues()
                         if (v - p[0, 1, 1]).expand().simplify() != 0]
                try:
                    theta.sort(key=lambda x: CoefficientList(x, self._.vars),
                               reverse=True)
                except Exception:
                    warn(Warning("Sorting of eigenvalues failed - "
                                 "you may want to sort them manually"))
                else:
                    if not self._.vars_ordered:
                        warn(Warning("More than one variable is used - "
                                     "please check that the ordering "
                                     "of the eigenvalues is correct"))
                if len(theta) > self._.d:
                    warn(Warning("%s not identified among eigenvalues "
                                 "and may not appear in initial position"
                                 % self.SIZE.capitalize()))
                    self._.theta = theta
                else:
                    self._.theta = (p[0, 1, 1], *theta)
        self._.theta = rewriteTuple(self._.theta, expand=expand,
                                    factor=factor, simplify=simplify)
        return self._.theta

    def _compute_imprimitivity(self):
        """
        Determine whether the scheme is imprimitive
        and compute the corresponding derived schemes.
        """
        m = floor(self._.d / 2)
        self._.antipodal = all(full_simplify(
            self._.b[i] - self._.c[self._.d - i]) == 0
            for i in range(self._.d) if i != m)
        self._.bipartite = all(a == 0 for a in self._.a)
        if self._.antipodal:
            try:
                self._.r = integralize(
                    1 + self._.b[m] / self._.c[self._.d - m])
            except TypeError:
                raise InfeasibleError("covering index not integral")
            if self._.d >= 2:
                if self._.d == 2:
                    b = [self._.b[0]/(self._.b[1]+1)]
                    c = [Integer(1)]
                else:
                    b = self._.b[:m]
                    c = list(self._.c[1:m+1])
                    if is_divisible(self._.d, 2):
                        c[-1] *= self._.r
                scheme = self._get_class()(tuple(b), tuple(c))
            else:
                scheme = ASParameters(P=[[1]])
            self._.antipodal_subscheme = self.add_subscheme(scheme,
                                                            self.ANTIPODAL)
        if self._.bipartite:
            if self._.d >= 2:
                b = tuple(self._.b[2*i]*self._.b[2*i+1]/self._.c[2]
                          for i in range(m))
                c = tuple(self._.c[2*i+1]*self._.c[2*i+2]/self._.c[2]
                          for i in range(m))
                scheme = self._get_class()(b, c)
            else:
                scheme = ASParameters(P=[[1]])
            self._.bipartite_subscheme = self.add_subscheme(scheme,
                                                            self.BIPARTITE)

    def _compute_parameters(self, p, k):
        """
        Compute the intersection numbers or Krein parameters
        from the intersection or Krein array.
        """
        for i in range(self._.d + 1):
            p[0, i, i] = k[i]
            p[i, 0, i] = Integer(1)
            p[i, i, 0] = Integer(1)
        for i in range(self._.d):
            p[i+1, 1, i+1] = self._.a[i+1]
            p[i, 1, i+1] = self._.b[i]
            p[i+1, 1, i] = self._.c[i+1]
        for i in range(2, self._.d + 1):
            for j in range(1, self._.d + 1):
                for h in range(1, self._.d):
                    p[h, i, j] = self._check_parameter(
                        h, i, j,
                        _simplify(_expand((
                            self._.c[h] * p[h-1, i-1, j]
                            + self._.b[h] * p[h+1, i-1, j]
                            - self._.b[i-2] * p[h, i-2, j]
                            + (self._.a[h] - self._.a[i-1]) * p[h, i-1, j]
                        ) / self._.c[i])))
                p[self._.d, i, j] = self._check_parameter(
                    self._.d, i, j,
                    _simplify(_expand((
                        self._.c[self._.d] * p[self._.d-1, i-1, j]
                        - self._.b[i-2] * p[self._.d, i-2, j]
                        + (self._.a[self._.d] - self._.a[i-1])
                        * p[self._.d, i-1, j]
                    ) / self._.c[i])))

    def _compute_primalEigenmatrix(self, expand=False, factor=False,
                                   simplify=False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        if self._has("P"):
            return
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self._.P = self._compute_eigenmatrix(self.kTable(**params),
                                             self.PTR, **params)

    def _compute_sizes(self, k, expand=False, factor=False,
                       simplify=False):
        """
        Compute multiplicities of the eigenspaces
        or valencies of the relations.
        """
        if not self._has("omega"):
            self.cosineSequences(expand=expand, factor=factor,
                                 simplify=simplify)
        if not self._has("theta"):
            self.eigenvalues(expand=expand, factor=factor, simplify=simplify)
        if self.is_cyclic():
            m = tuple(Integer(1 if th in [2, -2] else 2)
                      for th in self._.theta)
        else:
            try:
                m = tuple(integralize(_simplify(_factor(
                    self._.n / sum(s * om**2
                                   for s, om in zip(k, omg)))))
                          for omg in self._.omega)
            except TypeError:
                raise InfeasibleError("%s not integral" % self.DUAL_SIZES)
        return m

    def _copy(self, p):
        """
        Copy fields to the given object.
        """
        ASParameters._copy(self, p)
        if isinstance(p, self._get_class()):
            if self._has("theta"):
                p._.theta = self._.theta
            if self._has("omega"):
                p._.omega = copy(self._.omega)
        elif self._has("omega"):
            if isinstance(p, PolyASParameters):
                p._.omega = self._.omega.transpose()
            elif not p._has("P") and not p._has("Q"):
                p._.P = self.eigenmatrix()
        p._.antipodal = self._.antipodal
        p._.bipartite = self._.bipartite
        if self._has("r"):
            p._.r = self._.r
        if self._has("antipodal_subscheme"):
            p._.antipodal_subscheme = self._.antipodal_subscheme
        if self._has("bipartite_subscheme"):
            p._.bipartite_subscheme = self._.bipartite_subscheme

    def _copy_cosineSequences(self, P):
        """
        Obtain the cosine sequences from an eigenmatrix.
        """
        self._.omega = P / diagonal_matrix(P[0])

    def _derived(self, derived=True):
        """
        Generate parameters sets of derived association schemes.
        """
        self.partSchemes()
        yield from ASParameters._derived(self, derived)

    def _format_parameterArray(self):
        """
        Return a string representation of the intersection array.
        """
        return "{{{}; {}}}".format(*tuple(', '.join(str(x) for x in l)
                                          for l in self.parameterArray()))

    def _format_parameterArray_ascii(self):
        """
        Return an ASCII art representation of the intersection array.
        """
        art = ascii_art(*sum(zip([ascii_art(x)
                                  for l in self.parameterArray() for x in l],
                                 ([", "] * (self.classes()-1) + ["; "]) * 2),
                             ())[:-1])
        return ascii_left_curly_brace.character_art(art.height()) + art \
            + ascii_right_curly_brace.character_art(art.height())

    def _format_parameterArray_latex(self):
        """
        Return a LaTeX representation of the intersection array.
        """
        return r"\left\{{{}; {}\right\}}".format(*tuple(', '.join(latex(x)
                                                                  for x in l)
                                                        for l in self.parameterArray()))

    def _format_parameterArray_unicode(self):
        """
        Return a Unicode art representation of the intersection array.
        """
        art = unicode_art(*sum(zip([unicode_art(x)
                                    for l in self.parameterArray()
                                    for x in l],
                                   ([", "] * (self.classes()-1)
                                    + ["; "]) * 2), ())[:-1])
        return unicode_left_curly_brace.character_art(art.height()) + art \
            + unicode_right_curly_brace.character_art(art.height())

    def _get_parameters(self):
        """
        Return the defining parameter set, if any.

        Returns the intersection or Krein array
        together with an appropriate symbol.
        """
        return (self.SYMBOL, self.parameterArray())

    def _init_array(self, b, c):
        """
        Initialize the intersection or Krein array.
        """
        self._.c = (Integer(0), ) + tuple(c)
        self._.b = tuple(b) + (Integer(0), )

    def _init_multiplicities(self):
        """
        Compute the valencies of relations
        or multiplicities of the eigenvalues
        from the intersection or Krein array.
        """
        k = [Integer(1)]
        try:
            for i in range(1, self._.d + 1):
                k.append(integralize(k[-1]*self._.b[i-1]/self._.c[i]))
                self._check_multiplicity(k, i)
        except TypeError:
            raise InfeasibleError("%s not integral" % self.SIZES)
        self._.n = sum(k)
        return k

    def _latex_(self):
        """
        LaTeX representation.
        """
        return LatexExpr(r"\text{{Parameters of a {} with {} }} {}".format(self.OBJECT_LATEX, self.ARRAY,
                                                                           self._format_parameterArray_latex()))

    def _match(self, b, c):
        """
        Return the values the variables need to take
        to match with the given array.
        """
        return _solve([SR(l) == r for l, r in
                       zip(self._.b[:-1] + self._.c[1:], tuple(b) + tuple(c))],
                      self._.vars)

    def _subs(self, exp, p, seen):
        """
        Substitute the given subexpressions in the parameters.
        """
        p, new = ASParameters._subs(self, exp, p, seen)
        if new:
            if self._has("theta"):
                p._.theta = tuple(subs(th, *exp) for th in self._.theta)
            if self._has("omega"):
                p._.omega = self._.omega.subs(*exp)
        return (p, new)

    def _unicode_art_(self):
        """
        Unicode art representation.
        """
        return unicode_art(f"Parameters of a {self.OBJECT} with {self.ARRAY} ",
                           self._format_parameterArray_unicode())

    def antipodalSubscheme(self):
        """
        Return the parameters of the antipodal quotient
        or Q-antipodal fraction.
        """
        assert self._.antipodal, "scheme not %s-antipodal" % self.MATRIX
        return self._.antipodal_subscheme

    def aTable(self, full=False, expand=False, factor=False, simplify=False):
        """
        Return the table of parameters ``a[1], a[2], ..., a[d]``,
        where ``d`` is the number of classes of the association scheme.

        If ``full`` is ``True``, the returned table also includes ``a[0]``.
        """
        self._.a = rewriteTuple(self._.a, expand=expand, factor=factor,
                                simplify=simplify)
        return tuple(self._.a) if full else self._.a[1:]

    def bipartiteSubscheme(self):
        """
        Return the parameters of the bipartite half
        or Q-antipodal quotient.
        """
        assert self._.bipartite, "scheme not %s-bipartite" % self.MATRIX
        return self._.bipartite_subscheme

    def bTable(self, full=False, expand=False, factor=False, simplify=False):
        """
        Return the table of parameters ``b[0], b[1], ..., b[d-1]``,
        where ``d`` is the number of classes of the association scheme.

        If ``full`` is ``True``, the returned table also includes ``b[d]``.
        """
        self._.b = rewriteTuple(self._.b, expand=expand, factor=factor,
                                simplify=simplify)
        return tuple(self._.b) if full else self._.b[:-1]

    def cTable(self, full=False, expand=False, factor=False, simplify=False):
        """
        Return the table of parameters ``c[1], c[2], ..., c[d]``,
        where ``d`` is the number of classes of the association scheme.

        If ``full`` is ``True``, the returned table also includes ``c[0]``.
        """
        self._.c = rewriteTuple(self._.c, expand=expand, factor=factor,
                                simplify=simplify)
        return tuple(self._.c) if full else self._.c[1:]

    def cosineSequences(self, index=None, ev=None, expand=False,
                        factor=False, simplify=False):
        """
        Compute and return the cosine sequences
        for each relation and eigenspace.
        """
        self._compute_cosineSequences(expand=expand, factor=factor,
                                      simplify=simplify)
        rewriteMatrix(self._.omega, expand=expand, factor=factor,
                      simplify=simplify)
        if ev is not None:
            if not self._has("theta"):
                self.eigenvalues(expand=expand, factor=factor,
                                 simplify=simplify)
            try:
                index = self._.theta.index(ev)
            except ValueError as ex:
                if index is None:
                    raise ex
        if index is not None:
            return self._.omega[index]
        return Matrix(SR, self._.omega)

    def eigenvalues(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the eigenvalues of the association scheme.

        Not implemented, to be overridden.
        """
        raise NotImplementedError

    def is_antipodal(self):
        """
        Check whether the association scheme is antipodal,
        and return the covering index if it is.
        """
        return self._.r if self._.antipodal else False

    def is_bipartite(self):
        """
        Check whether the graph is bipartite.
        """
        return self._.bipartite

    def is_cyclic(self):
        """
        Check whether the association scheme is cyclic.
        """
        return self._.b[0] == 2 and self._.c[-1] in [1, 2] and \
            all(x == 1 for x in self._.b[1:-1] + self._.c[1:-1])

    def match(self, *ial):
        """
        Check whether the association scheme
        matches any of the given intersection or Krein arrays.
        """
        for b, c in ial:
            assert len(b) == len(c), "parameter length mismatch"
            if self._.d != len(b):
                continue
            if len(self._match(b, c)) > 0:
                return True
        return False

    def merge(self, k, p, *args, **kargs):
        """
        Return parameters of a polynomial scheme obtained
        by merging specified relations or eigenspaces.
        """
        adj = set(args)
        conditions = kargs.get("conditions", False)
        assert all(i >= 1 and i <= self._.d for i in adj), \
            "indices out of bounds"
        if conditions:
            eqs = []
        else:
            b = [sum(k[j] for j in adj)]
            c = [1]
        cur = adj
        idx = set(range(1, self._.d+1)).difference(adj)
        while len(idx) > 0:
            nxt = {i for i in idx if any(checkPos(p[h, i, j])
                                         for h in cur for j in adj)}
            if len(nxt) == 0:
                break
            bi = {sum(p[h, i, j] for i in nxt for j in adj) for h in cur}
            ci = {sum(p[h, i, j] for i in cur for j in adj) for h in nxt}
            if conditions:
                ib = iter(bi)
                ic = iter(ci)
                b0 = SR(next(ib))
                c0 = SR(next(ic))
                for bb in ib:
                    eqs.append(b0 == bb)
                for cc in ic:
                    eqs.append(c0 == cc)
            else:
                if len(bi) > 1 or len(ci) > 1:
                    raise IndexError("merging {} {} does not yield "
                                     "a {}-polynomial scheme".format(self.PARTS, sorted(adj), self.MATRIX))
                b.append(next(iter(bi)))
                c.append(next(iter(ci)))
            cur = nxt
            idx.difference_update(nxt)
        if conditions:
            return _solve(eqs, self._.vars)
        else:
            part = self.PART_SCHEME % \
                (list(args) if len(args) > 1 else args[0])
            try:
                pa = self._get_class()(b, c)
            except (InfeasibleError, AssertionError) as ex:
                raise InfeasibleError(ex, part=part)
            self.add_subscheme(pa, part)
            return pa

    def parameterArray(self, expand=False, factor=False, simplify=False):
        """
        Return the intersection or Krein array of the association scheme
        as a tuple of two tuples.
        """
        return (self.bTable(expand=expand, factor=factor, simplify=simplify),
                self.cTable(expand=expand, factor=factor, simplify=simplify))

    def partSchemes(self):
        """
        Return a dictionary of all parameter sets
        obtained by taking all subsets of {1, ..., d}
        as relations or eigenspaces.
        """
        out = {}
        for idx in subsets(range(1, self._.d + 1)):
            if len(idx) > 0 and len(idx) < self._.d and idx != [1]:
                try:
                    out[tuple(idx)] = self.merge(*idx)
                except IndexError:
                    pass
        return out

    def reorderEigenvalues(self, *order):
        """
        Specify a new order for the eigenvalues and return it.

        Performs the part of the reordering that is common
        to P- and Q-polynomial association schemes.
        """
        order = self._reorder(order)
        if not self._has("theta"):
            self.eigenvalues()
        self._.theta = tuple(self._.theta[i] for i in order)
        if self._has("omega"):
            self._.omega = Matrix(SR, [self._.omega[i] for i in order])
        if self._has("fsd"):
            del self._.fsd
        return order

    def reorderParameters(self, p, *order):
        """
        Specify a new order for the parameters and return it.

        Performs the part of the reordering that is common
        to P- and Q-polynomial association schemes.
        """
        self._.a = tuple(p[i, i, 1] for i in range(self._.d + 1))
        self._.b = tuple(p[i, i+1, 1] if i < self._.d else Integer(0)
                         for i in range(self._.d + 1))
        self._.c = tuple(p[i, i-1, 1] if i > 0 else Integer(0)
                         for i in range(self._.d + 1))
        if self._has("omega"):
            self._.omega = Matrix(SR, [[r[i] for i in order]
                                       for r in self._.omega])
        if self._has("theta"):
            del self._.theta
        if self._has("fsd"):
            del self._.fsd

    def terwilligerPolynomial(self, var='x', i=2, p_order=None, q_order=None):
        """
        Return the Terwilliger polynomial of a P- and Q-polynomial scheme.
        """
        assert self._.d >= 3, "diameter must be at least 3"
        assert 2 <= i <= self._.d - 1, "i must be between 2 and d-1"
        if not self._has("pPolynomial_ordering"):
            assert self.is_pPolynomial(), "scheme is not P-polynomial"
        if not self._has("qPolynomial_ordering"):
            assert self.is_qPolynomial(), "scheme is not Q-polynomial"
        if p_order is None:
            p_order = self._.pPolynomial_ordering[0]
        else:
            p_order = self._reorder(p_order)
            assert p_order in self._.pPolynomial_ordering, \
                "specified order is not P-polynomial"
        if q_order is None:
            q_order = self._.qPolynomial_ordering[0]
        else:
            q_order = self._reorder(q_order)
            assert q_order in self._.qPolynomial_ordering, \
                "specified order is not Q-polynomial"
        if not self._has("p"):
            self.pTable()
        if not self._has("Q"):
            self.dualEigenmatrix()
        x = SR.symbol(var) if isinstance(var, str) else var
        ths = next(iter(zip(*self._.Q[p_order, q_order[1]]))) \
            + (Integer(0), )
        o = p_order[1]
        z = tuple(zip(p_order[:-1], p_order[1:]))
        a = self._.p[o, o, o]
        b = [self._.p[j, o, jj] for j, jj in z] + [Integer(0)]
        c = [Integer(0)] + [self._.p[jj, o, j] for j, jj in z]
        kk = (ths[1] - ths[2]) / (ths[0] - ths[2])
        kp = kk * (ths[0] + ths[1] - ths[i-1] - ths[i]) / (ths[i-1] - ths[i])
        km = kk * (ths[0] + ths[1] - ths[i] - ths[i+1]) / (ths[i] - ths[i+1])
        t1p = (ths[1] - ths[i-1]) / (ths[i-1] - ths[i])
        t1m = (ths[1] - ths[i]) / (ths[i] - ths[i+1])
        tk = b[2] / b[1] * (ths[2] - ths[3]) / (ths[1] - ths[2])
        tt = (ths[0] - ths[2]) / (ths[0] - ths[1])
        t2p = b[i] / b[1] * (ths[i] - ths[i+1]) / (ths[i-1] - ths[i]) \
            - kp * tk + t1p * tt
        t2m = b[i+1] / b[1] * (ths[i+1] - ths[i+2]) / (ths[i] - ths[i+1]) \
            - km * tk + t1m * tt
        p1p = kp * (a - c[2]) + b[1] * (t1p - t2p)
        p0p = kp * (b[0] - c[2]) - b[1] * t2p
        s = b[i] + c[i+1] - b[0] - 1
        p1m = -s - km * (a - c[2]) - b[1] * (t1m - t2m)
        p0m = -s - km * (b[0] - c[2]) + b[1] * (t2m + 1)
        ii = p_order[i]
        bc = b[i] * c[i]
        T = (self._.p[0, ii, ii] / (b[0] * b[1]))**2 * bc * \
            ((-kp * x**2 + p1p * x + p0p) * (km * x**2 + p1m * x + p0m)
             - bc * (x + 1)**2)
        return T.expand()

    @Param
    def a(self):
        """
        Access function for the table of ``a`` parameters of the scheme.
        """
        pass

    @Param
    def b(self):
        """
        Access function for the table of ``b`` parameters of the scheme.
        """
        pass

    @Param
    def c(self):
        """
        Access function for the table of ``c`` parameters of the scheme.
        """
        pass

    @Param
    def omega(self):
        """
        Access function for the table of cosine sequences of the scheme.
        """
        self.cosineSequences()

    @Param
    def r(self):
        """
        Access function for the covering index of the scheme.
        """
        assert self._.antipodal, "scheme is not antipodal"

    @Param
    def theta(self):
        """
        Access function for the table of eigenvalues of the scheme.
        """
        self.eigenvalues()

    substitute = subs
