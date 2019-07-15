from copy import copy
from warnings import warn
from sage.all import pi
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.functions.trig import cos
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import identity_matrix
from sage.matrix.special import diagonal_matrix
from sage.misc.latex import latex
from sage.misc.latex import LatexExpr
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
from .coefflist import CoefficientList
from .find import find
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
from .util import make_expressions
from .util import nrows
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

DUAL_PARAMETER = "Krein parameter"
DUAL_PARTS = "multiplicities"
DUAL_SYMBOL = "q"
OBJECT = "association scheme"
PARAMETER = "intersection number"
PARTS = "subconstituents"
SYMBOL = "p"


class InfeasibleError(Exception):
    """
    Infeasibility of a parameter set.
    """

    def __init__(self, reason=None, refs=None, part=None):
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


class Parameters:
    """
    An auxiliary class for storing the computed parameters.
    """
    d = None
    vars = None

    def __init__(self, p):
        """
        Object constructor.
        """
        self._parameters = p
        self.triple = {}
        self.triple_solution = {}
        self.triple_solution_generator = {}

    def __repr__(self):
        """
        String representation.
        """
        return "Parameter storage of <%s>" % repr(self._parameters)


class ASParameters(SageObject):
    """
    A class for parameters of a general association scheme
    and checking their feasibility.
    """
    _ = None

    def __init__(self, p=None, q=None, P=None, Q=None):
        """
        Object constructor.
        """
        self._init_storage()
        if self._get_class() is ASParameters:
            self._init_prefix()
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
                       key=lambda (k, v, b): CoefficientList(k, self._.vars),
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
        Compute the sizes of the subconstituents.
        """
        if self._has("k"):
            return
        if self._has("p"):
            k = tuple(self._.p[0, i, i] for i in range(self._.d + 1))
        else:
            if self._has("P"):
                self.eigenmatrix(expand=expand, factor=factor,
                                 simplify=simplify)
            k = tuple(integralize(x) for x in self._.P[0])
        assert k[0] == 1, \
            "the size of the first subconstituent is not 1"
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
        Copy fields to the given obejct.
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
        p._.triple.update(self._.triple)
        p._.triple_solution.update(self._.triple_solution)
        p._.triple_solution_generator.update(self._.triple_solution_generator)

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return ASParameters

    def _has(self, name):
        """
        Check whether the given parameter is available.
        """
        return name in self._.__dict__

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
                 if h not in order[-2:] and p[order[-1], i, h] != 0}
            if len(j) != 1:
                return False
            j, = j
            order.append(j)
        return tuple(order)

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

    def _subs(self, exp, p):
        """
        Substitute the given subexpressions in the paramaters.
        """
        if self._has("p") and not p._has("p"):
            p._.p = self._.p.subs(*exp)
        if self._has("q") and not p._has("q"):
            p._.q = self._.q.subs(*exp)
        if self._has("P") and not p._has("P"):
            p._.P = self._.P.subs(*exp)
        if self._has("Q") and not p._has("Q"):
            p._.Q = self.Q._.subs(*exp)
        for k, v in self._.triple.items():
            p._.triple[k] = v.subs(*exp)

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

    def check_handshake(self, metric=False, bipartite=False):
        """
        Verify the handshake lemma for all relations in all subconstituents.
        """
        if not self._has("k"):
            self.kTable()
        if not self._has("p"):
            self.pTable()
        d = [self._.d, 0 if metric else self._.d]
        b = 2 if bipartite else 1
        for i in range(1, self._.d + 1):
            if not isinstance(self._.k[i], Integer) or self._.k[i] % 2 == 0:
                continue
            d[1] += 2
            for j in range(b, min(d) + 1, b):
                if isinstance(self._.p[i, i, j], Integer) and \
                        self._.p[i, i, j] % 2 == 1:
                    raise InfeasibleError("handshake lemma not satisfied "
                                          "for relation %d in subconstituent"
                                          " %d" % (j, i))

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
                    g[u, v, w] = find(
                        make_expressions((S[h, i, j], 0,
                                          min(self._.p[u, h, i],
                                              self._.p[v, h, j],
                                              self._.p[w, i, j]))
                                         for h in range(self._.d + 1)
                                         for i in range(self._.d + 1)
                                         for j in range(self._.d + 1)),
                        S.variables(), solver=solver)
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
                                for sol, s in r[st].items():
                                    if s[sd] != 0:
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

    def classes(self):
        """
        Return the number of classes of the association scheme.
        """
        return self._.d

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
            pPoly = filter(None, (self._is_polynomial(self._.p, i)
                                  for i in range(1, self._.d+1)))
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
            qPoly = filter(None, (self._is_polynomial(self._.q, i)
                                  for i in range(1, self._.d+1)))
            self._.qPolynomial_ordering = False if len(qPoly) == 0 else qPoly
        return self._.qPolynomial_ordering

    def kTable(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the sizes of the subconstituents
        """
        self._compute_kTable(expand=expand, factor=factor,
                             simplify=simplify)
        self._.k = rewriteTuple(self._.k, expand=expand, factor=factor,
                                simplify=simplify)
        return self._.k

    def mTable(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the multiplicities of the eigenspaces.
        """
        self._compute_multiplicities(expand=expand, factor=factor,
                                     simplify=simplify)
        self._.m = rewriteTuple(self._.m, expand=expand, factor=factor,
                                simplify=simplify)
        return self._.m

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

    def subs(self, *exp):
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
        p = ASParameters(**par)
        self._subs(exp, p)
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
                        solve=True, save=None):
        """
        Solve equations for triples of vertices
        in relations ``u``, ``v``, ``w``.

        If ``krein`` is a list of triples,
        the corresponding equations are used;
        otherwise, equations for zero Krein parameters are used.
        If ``params`` is a dictionary mapping strings to triples,
        the keys will be used as variables mapped to triple intersection
        numbers for corresponding triples.
        If ``solve`` is False,
        only a list of equations and a set of variables is returned,
        without solving the equations.
        """
        if solve and krein is None and params is None:
            t = (u, v, w)
            for p, q in zip(TPERMS, DPERMS):
                tp = tuple(t[i] for i in p)
                if tp in self._.triple:
                    self._.triple[t] = self._.triple[tp].permute(q)
                    return self._.triple[t]
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
               else symbol("%s_%d_%d_%d_%d_%d_%d" %
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

    def variables(self):
        """
        Return the variables in the graph parameters.
        """
        return self._.vars

    intersectionNumbers = pTable
    kreinParameters = qTable
    multiplicities = mTable
    order = __len__
    valencies = kTable
    substitute = subs


class PolyASParameters(ASParameters):
    """
    A class for parameters of a polynomial association scheme
    and checking their feasibility.
    """
    ARRAY = None
    DUAL_INTEGRAL = None
    DUAL_PARAMETER = None
    DUAL_PARTS = None
    DUAL_SYMBOL = None
    OBJECT = None
    OBJECT_LATEX = None
    PARAMETER = None
    PART = None
    PARTS = None
    PTR = None
    QTR = None
    SYMBOL = None

    def __init__(self, b, c=None, order=None):
        """
        Object constructor.

        Check the basic properties of the intersection or Krein array.
        """
        self._init_storage()
        if isinstance(b, ASParameters):
            ASParameters.__init__(self, b)
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
            ASParameters.__init__(self)
        self._.hash_parameters = self.parameterArray(factor=True, simplify=2)
        self._init_prefix()

    def __eq__(self, other):
        """
        Compare self to other.
        """
        if isinstance(other, self._get_class()):
            return self._.hash_parameters == other._.hash_parameters
        else:
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
        return "Parameters of a %s with %s %s" % \
            (self.OBJECT, self.ARRAY, self._format_parameterArray())

    def _ascii_art_(self):
        """
        ASCII art representation.
        """
        return ascii_art("Parameters of a %s with %s " %
                         (self.OBJECT, self.ARRAY),
                         self._format_parameterArray_ascii())

    def _check_multiplicity(self, k, i):
        """
        Check the valency of the i-th subconstituent or eigenspace.
        """
        for j in range(self._.d + 1):
            if self._.a[i] >= k[i]:
                raise InfeasibleError("valency of %s %d too large" %
                                      (self.PART, i))

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
                self._.theta = B.eigenvalues()
                try:
                    self._.theta.sort(
                        key=lambda x: CoefficientList(x, self._.vars),
                        reverse=True)
                except Exception:
                    warn(Warning("Sorting of eigenvalues failed - "
                                 "you may want to sort them manually"))
                else:
                    if not self._.vars_ordered:
                        warn(Warning("More than one variable is used - "
                                     "please check that the ordering "
                                     "of the eigenvalues is correct"))
                self._.theta = tuple(self._.theta)
        self._.theta = rewriteTuple(self._.theta, expand=expand,
                                    factor=factor, simplify=simplify)
        return self._.theta

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
                    h, i, j,
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
        or sizes of the subconstituents.
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
                raise InfeasibleError("%s not integral" % self.DUAL_PARTS)
        return m

    def _copy(self, p):
        """
        Copy fields to the given obejct.
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

    def _copy_cosineSequences(self, P):
        """
        Obtain the cosine sequences from an eigenmatrix.
        """
        self._.omega = P / diagonal_matrix(P[0])

    def _format_parameterArray(self):
        """
        Return a string representation of the intersection array.
        """
        return "{%s; %s}" % tuple(', '.join(str(x) for x in l)
                                  for l in self.parameterArray())

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
        return r"\left\{%s; %s\right\}" % tuple(', '.join(latex(x)
                                                          for x in l) for l
                                                in self.parameterArray())

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

    def _init_array(self, b, c):
        """
        Initialize the intersection or Krein array.
        """
        self._.c = (Integer(0), ) + tuple(c)
        self._.b = tuple(b) + (Integer(0), )

    def _init_multiplicities(self):
        """
        Compute the sizes of subconstituents
        or multiplicities of the eigenvalues
        from the intersection or Krein array.
        """
        k = [Integer(1)]
        try:
            for i in range(1, self._.d + 1):
                k.append(integralize(k[-1]*self._.b[i-1]/self._.c[i]))
                self._check_multiplicity(k, i)
        except TypeError:
            raise InfeasibleError("%s not integral" % self.PARTS)
        self._.n = sum(k)
        return k

    def _latex_(self):
        """
        LaTeX representation.
        """
        return LatexExpr(r"\text{Parameters of a %s with %s } %s" %
                         (self.OBJECT_LATEX, self.ARRAY,
                          self._format_parameterArray_latex()))

    def _subs(self, exp, p):
        """
        Substitute the given subexpressions in the parameters.
        """
        if self._has("theta"):
            p._.theta = tuple(subs(th, *exp) for th in self._.theta)
        if self._has("omega"):
            p._.omega = self._.omega.subs(*exp)
        ASParameters._subs(self, exp, p)

    def _unicode_art_(self):
        """
        Unicode art representation.
        """
        return unicode_art("Parameters of a %s with %s " %
                           (self.OBJECT, self.ARRAY),
                           self._format_parameterArray_unicode())

    def aTable(self, full=False, expand=False, factor=False, simplify=False):
        """
        Return the table of parameters ``a[1], a[2], ..., a[d]``,
        where ``d`` is the number of classes of the association scheme.

        If ``full`` is ``True``, the returned table also includes ``a[0]``.
        """
        self._.a = rewriteTuple(self._.a, expand=expand, factor=factor,
                                simplify=simplify)
        return tuple(self._.a) if full else self._.a[1:]

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
        for each subconstituent and eigenspace.
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
            if len(_solve([SR(l) == r for l, r
                          in zip(self._.b[:-1] + self._.c[1:],
                                 tuple(b) + tuple(c))], self._.vars)) > 0:
                return True
        return False

    def parameterArray(self, expand=False, factor=False, simplify=False):
        """
        Return the intersection or Krein array of the association scheme
        as a tuple of two tuples.
        """
        return (self.bTable(expand=expand, factor=factor, simplify=simplify),
                self.cTable(expand=expand, factor=factor, simplify=simplify))

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

    substitute = subs
