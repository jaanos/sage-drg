from copy import copy
from warnings import warn
from sage.all import pi
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.functions.trig import cos
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import diagonal_matrix
from sage.matrix.constructor import identity_matrix
from sage.rings.integer import Integer
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .array3d import Array4D
from .coefflist import CoefficientList
from .find import find
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
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

class ASParameters:
    d = None
    vars = None

    def __init__(self, p = None, q = None, P = None, Q = None):
        """
        Object constructor.
        """
        if self._get_class() is ASParameters:
            self._init_prefix()
        self.triple = {}
        self.triple_solution = {}
        self.triple_solution_generator = {}
        self.quadruple = {}
        assert (p, q, P, Q).count(None) >= 3, \
            "precisely one of p, q, P, Q must be given"
        if isinstance(p, ASParameters):
            p._copy(self)
        elif p is not None:
            self.p = self._init_parameters(p, integral = True,
                                           name = PARAMETER, sym = SYMBOL)
            self._compute_kTable()
            self._check_consistency(self.p, self.k,
                                    name = PARAMETER, sym = SYMBOL)
        elif q is not None:
            self.q = self._init_parameters(q, integral = False,
                                           name = DUAL_PARAMETER,
                                           sym = DUAL_SYMBOL)
            self._compute_multiplicities()
            self._check_consistency(self.q, self.m,
                                    name = DUAL_PARAMETER, sym = DUAL_SYMBOL)
        elif P is not None:
            self.P = self._init_eigenmatrix(P)
        elif Q is not None:
            self.Q = self._init_eigenmatrix(Q)
        else:
            assert self.d is not None, "insufficient data"
        self._init_vars()

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
        return "Parameters of an association scheme on %s vertices " \
               "with %d classes" % (self.n, self.d)

    def _check_consistency(self, p, k, name = None, sym = None):
        """
        Check for the consistency of the intersection numbers
        or Krein parameters.
        """
        r = range(self.d + 1)
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
        if "n" not in self.__dict__:
            self.n = sum(k)

    def _check_eigenmatrices(self):
        """
        Check whether the eigenmatrices
        multiply into a multiple of the identity matrix.
        """
        if "P" in self.__dict__ and "Q" in self.__dict__ and \
                _simplify(_expand(self.P * self.Q)) \
                    != self.order(expand = True, simplify = True) \
                        * identity_matrix(SR, self.d + 1):
            warn(Warning("the eigenmatrices do not multiply "
                         "into a multiple of the identity matrix"))

    @staticmethod
    def _check_parameter(h, i, j, v, integral = False,
                         name = None, sym = None):
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

    def _check_parameters(self, p, integral = False, name = None, sym = None):
        """
        Check for the feasibility
        of all intersection numbers or Krein parameters.

        The parameters are checked for nonnegativity,
        and, if requested, also for integrality.
        """
        for h in range(self.d + 1):
            for i in range(self.d + 1):
                for j in range(self.d + 1):
                    p[h, i, j] = ASParameters. \
                        _check_parameter(h, i, j, p[h, i, j],
                                         integral = integral,
                                         name = name, sym = sym)

    def _check_zero(self, h, i, j, u, v, w):
        """
        Check whether a triple intersection number is not forced to be zero
        by the intersection numbers.
        """
        return self.p[u, h, i] != 0 and self.p[v, h, j] != 0 and \
            self.p[w, i, j] != 0

    def _compute_dualEigenmatrix(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        if "Q" in self.__dict__:
            return
        if "q" in self.__dict__:
            self.Q = self._compute_eigenmatrix(self.q, expand = expand,
                                               factor = factor,
                                               simplify = simplify)
        else:
            if "P" not in self.__dict__:
                self.eigenmatrix(expand = expand, factor = factor,
                                 simplify = simplify)
            self.Q = self.n * self.P.inverse()
        self._check_eigenmatrices()

    def _compute_eigenmatrix(self, p, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return an eigenmatrix of the association scheme.
        """
        B = [Matrix(SR, [M[i] for M in p]) for i in range(self.d + 1)]
        V = SR**(self.d + 1)
        R = [[self.d + 1, V, [Integer(1)]]]
        for i in range(1, self.d + 1):
            S = sorted(([k, m, V.subspace_with_basis(b)]
                        for k, b, m in B[i].eigenvectors_right()),
                       key = lambda (k, v, b): CoefficientList(k, self.vars),
                       reverse = True)
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
        assert len(R) == self.d + 1 and all(len(r) == self.d + 1
                                            for _, _, r in R), \
            "failed to compute the eigenmatrix"
        return Matrix(SR, [r for _, _, r in R])

    def _compute_kreinParameters(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the Krein parameters.
        """
        if "q" in self.__dict__:
            return
        if "m" not in self.__dict__:
            self.multiplicities(expand = expand, factor = factor,
                                simplify = simplify)
        if "k" not in self.__dict__:
            self.kTable(expand = expand, factor = factor,
                        simplify = simplify)
        q = Array3D(self.d + 1)
        self._compute_parameters(q, self.Q, self.k, integral = False,
                                 name = DUAL_PARAMETER, sym = DUAL_SYMBOL)
        self.q = q

    def _compute_kTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the sizes of the subconstituents.
        """
        if "k" in self.__dict__:
            return
        if "p" in self.__dict__:
            k = tuple(self.p[0, i, i] for i in range(self.d + 1))
        else:
            if "P" not in self.__dict__:
                self.eigenmatrix(expand = expand, factor = factor,
                                 simplify = simplify)
            k = tuple(integralize(x) for x in self.P[0])
        assert k[0] == 1, \
            "the size of the first subconstituent is not 1"
        self.k = k

    def _compute_multiplicities(self, expand = False, factor = False,
                                simplify = False):
        """
        Compute the multiplicities of the eigenspaces.
        """
        if "m" in self.__dict__:
            return
        if "q" in self.__dict__:
            m = tuple(integralize(self.q[0, i, i])
                      for i in range(self.d + 1))
        else:
            if "Q" not in self.__dict__:
                self.dualEigenmatrix(expand = expand, factor = factor,
                                     simplify = simplify)
            m = tuple(integralize(x) for x in self.Q[0])
        assert m[0] == 1, "the multiplicity of the first eigenspace is not 1"
        self.m = m

    def _compute_parameters(self, p, P, m, integral = False, name = None,
                            sym = None):
        """
        Compute the intersection numbers or Krein parameters
        from the eigenmatrices.
        """
        for h in range(self.d + 1):
            for i in range(self.d + 1):
                for j in range(self.d + 1):
                    p[h, i, j] = full_simplify(
                                    sum(m[t] * P[t, h] * P[t, i] * P[t, j]
                                        for t in range(self.d + 1))
                                    / (self.n * P[0, h]))
                    self._check_parameter(h, i, j, p[h, i, j],
                                          integral = integral,
                                          name = name, sym = sym)
        self._check_consistency(p, P[0], name = name, sym = sym)

    def _compute_primalEigenmatrix(self, expand = False, factor = False,
                                   simplify = False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        if "P" in self.__dict__:
            return
        if "p" in self.__dict__:
            self.P = self._compute_eigenmatrix(self.p, expand = expand,
                                               factor = factor,
                                               simplify = simplify)
        else:
            if "Q" not in self.__dict__:
                self.dualEigenmatrix(expand = expand, factor = factor,
                                     simplify = simplify)
            self.P = self.n * self.Q.inverse()
        self._check_eigenmatrices()

    def _compute_pTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the intersection numbers.
        """
        if "p" in self.__dict__:
            return
        if "k" not in self.__dict__:
            self.kTable(expand = expand, factor = factor,
                        simplify = simplify)
        if "m" not in self.__dict__:
            self.multiplicities(expand = expand, factor = factor,
                                simplify = simplify)
        p = Array3D(self.d + 1)
        self._compute_parameters(p, self.P, self.m, integral = True,
                                 name = PARAMETER, sym = SYMBOL)
        self.p = p
        self.check_handshake()

    def _copy(self, p):
        """
        Copy fields to the given obejct.
        """
        p.d = self.d
        p.n = self.n
        if "p" in self.__dict__:
            p.p = copy(self.p)
        if "q" in self.__dict__:
            p.q = copy(self.q)
        if "P" in self.__dict__:
            p.P = copy(self.P)
        if "Q" in self.__dict__:
            p.Q = copy(self.Q)
        if "k" in self.__dict__:
            p.k = self.k
        if "m" in self.__dict__:
            p.m = self.m
        if "fsd" in self.__dict__:
            p.fsd = self.fsd
        if "pPolynomial_ordering" in self.__dict__:
            p.pPolynomial_ordering = self.pPolynomial_ordering
        if "qPolynomial_ordering" in self.__dict__:
            p.qPolynomial_ordering = self.qPolynomial_ordering
        p.triple.update(self.triple)
        p.triple_solution.update(self.triple_solution)
        p.triple_solution_generator.update(self.triple_solution_generator)
        p.quadruple.update(self.quadruple)

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return ASParameters

    def _init_eigenmatrix(self, P):
        """
        Initialize an eigenmatrix from the specified matrix.
        """
        self.d = nrows(P) - 1
        assert all(len(r) == self.d + 1 for r in P), \
            "parameter length mismatch"
        P = Matrix(SR, P)
        for i, x in enumerate(P[0]):
            P[0, i] = integralize(x)
        self.n = sum(P[0])
        return P

    def _init_parameters(self, p, integral = False, name = None, sym = None):
        """
        Initialize the intersection numbers or Krein parameters
        from the specified array.
        """
        self.d = nrows(p) - 1
        if isinstance(p, Array3D):
            a = p
        else:
            assert all(len(M) == self.d + 1 and all(len(r) == self.d+1
                                                    for r in M)
                       for M in p), "parameter length mismatch"
            a = Array3D(self.d + 1)
            for h in range(self.d + 1):
                for i in range(self.d + 1):
                    for j in range(self.d + 1):
                        a[h, i, j] = p[h][i][j]
        self._check_parameters(a, integral = integral,
                               name = name, sym = sym)
        return a

    def _init_prefix(self):
        """
        Initialize prefix to be used for internal variables.
        """
        self.prefix = "v%x" % (hash(self) % Integer(2)**32)

    def _init_vars(self):
        """
        Initialize the list of variables.
        """
        if "vars" not in self.__dict__:
            if "p" in self.__dict__:
                self.vars = self.p.variables()
            elif "q" in self.__dict__:
                self.vars = self.q.variables()
            elif "P" in self.__dict__:
                self.vars = variables(self.P)
            elif "Q" in self.__dict__:
                self.vars = variables(self.Q)
        self.vars_ordered = len(self.vars) <= 1

    def _is_polynomial(self, p, i):
        """
        Check whether the association scheme is polynomial
        for the given parameters and principal relation or eigenspace.
        """
        order = [0, i]
        while len(order) <= self.d:
            j = {h for h in range(self.d+1)
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
        assert len(order) == self.d + 1, "wrong number of indices"
        assert set(order) == set(range(self.d + 1)), \
            "repeating or nonexisting indices"
        return tuple(order)

    def _subs(self, exp, p):
        """
        Substitute the given subexpressions in the paramaters.
        """
        if "p" in self.__dict__ and not "p" in p.__dict__:
            p.p = self.p.subs(*exp)
        if "q" in self.__dict__ and not "q" in p.__dict__:
            p.q = self.q.subs(*exp)
        if "P" in self.__dict__ and not "P" in p.__dict__:
            p.P = self.P.subs(*exp)
        if "Q" in self.__dict__ and not "Q" in p.__dict__:
            p.Q = self.Q.subs(*exp)
        for k, v in self.triple.items():
            p.triple[k] = v.subs(*exp)
        for k, v in self.quadruple.items():
            p.quadruple[k] = v.subs(*exp)

    def check_absoluteBound(self, expand = False, factor = False,
                            simplify = False):
        """
        Check whether the absolute bound is not exceeded.
        """
        if "m" not in self.__dict__:
            self.multiplicities(expand = expand, factor = factor,
                                simplify = simplify)
        if "q" not in self.__dict__:
            self.kreinParameters(expand = expand, factor = factor,
                                 simplify = simplify)
        ineqs = {}
        for i in range(self.d + 1):
            ineq = self.m[i]*(self.m[i] + 1)/2 - \
                sum(self.m[h] for h in range(self.d + 1)
                    if self.q[h, i, i] != 0)
            if ineq < 0:
                raise InfeasibleError("absolute bound exceeded "
                                      "for (%d, %d)" % (i, i))
            elif not (ineq >= 0):
                ineqs[i, i] = rewriteExp(ineq, expand = expand,
                                         factor = factor,
                                         simplify = simplify)
            for j in range(i+1, self.d + 1):
                ineq = self.m[i]*self.m[j] - \
                    sum(self.m[h] for h in range(self.d + 1)
                        if self.q[h, i, j] != 0)
                if ineq < 0:
                    raise InfeasibleError("absolute bound exceeded "
                                          "for (%d, %d)" % (i, j))
                elif not (ineq >= 0):
                    ineqs[i, j] = rewriteExp(ineq, expand = expand,
                                             factor = factor,
                                             simplify = simplify)
        return ineqs

    def check_handshake(self, metric = False, bipartite = False):
        """
        Verify the handshake lemma for all relations in all subconstituents.
        """
        if "k" not in self.__dict__:
            self.kTable()
        if "p" not in self.__dict__:
            self.pTable()
        d = [self.d, 0 if metric else self.d]
        b = 2 if bipartite else 1
        for i in range(1, self.d + 1):
            if not isinstance(self.k[i], Integer) or self.k[i] % 2 == 0:
                continue
            d[1] += 2
            for j in range(b, min(d) + 1, b):
                if isinstance(self.p[i, i, j], Integer) and \
                        self.p[i, i, j] % 2 == 1:
                    raise InfeasibleError("handshake lemma not satisfied "
                                          "for relation %d in subconstituent"
                                          " %d" % (j, i))

    def check_quadruples(self, solver = None):
        """
        Check whether the existence of a forbidden quadruple of vertices
        is implied by the triple intersection numbers.
        """
        if "p" not in self.__dict__:
            self.pTable()
        r = self.triple_solution = {}
        g = self.triple_solution_generator = {}
        zero = {}
        done = {}
        for u in range(self.d + 1):
            for v in range(u, self.d + 1):
                for w in range(v, self.d + 1):
                    if self.p[u, v, w] == 0:
                        continue
                    S = self.tripleEquations(u, v, w)
                    g[u, v, w] = find(make_expressions((S[h, i, j], 0,
                                                        min(self.p[u, h, i],
                                                            self.p[v, h, j],
                                                            self.p[w, i, j]))
                                       for h in range(self.d + 1)
                                       for i in range(self.d + 1)
                                       for j in range(self.d + 1)),
                                      S.variables(), solver = solver)
                    try:
                        sol = sort_solution(next(g[u, v, w]))
                    except StopIteration:
                        raise InfeasibleError("no solution found "
                                    "for a triple of vertices at distances "
                                    "(%d, %d, %d)" % (u, v, w))
                    s = S.subs(sol)
                    r[u, v, w] = {sol: s}
                    zero[u, v, w] = {(h, i, j) for h in range(self.d + 1)
                                               for i in range(self.d + 1)
                                               for j in range(self.d + 1)
                                     if s[h, i, j] == 0 and
                                        self._check_zero(h, i, j, u, v, w)}
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
                        sol = sort_solution(next(g[t].send((True,
                                                self.triple[t][d] >= 1))))
                        if sol not in r[t]:
                            s = r[t][sol] = self.triple[t].subs(sol)
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
                                                self.triple[st][sd] == 0))
                                    if len(r[st]) == 0:
                                        sol = sort_solution(next(g[st]))
                                        r[st][sol] = \
                                            self.triple[st].subs(sol)
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
                                                for sh in range(self.d + 1)
                                                for si in range(self.d + 1)
                                                for sj in range(self.d + 1)
                                                if (sh, si, sj)
                                                    not in done[st]
                                                and self._check_zero(sh, si,
                                                                     sj, *st)
                                                and all(s[sh, si, sj] == 0
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
        return self.d

    def dualEigenmatrix(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute and return the dual eigenmatrix of the association scheme.
        """
        self._compute_dualEigenmatrix(expand = expand, factor = factor,
                                      simplify = simplify)
        self._check_eigenmatrices()
        rewriteMatrix(self.Q, expand = expand, factor = factor,
                      simplify = simplify)
        return Matrix(SR, self.Q)

    def eigenmatrix(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the eigenmatrix of the association scheme.
        """
        self._compute_primalEigenmatrix(expand = expand, factor = factor,
                                        simplify = simplify)
        self._check_eigenmatrices()
        rewriteMatrix(self.P, expand = expand, factor = factor,
                      simplify = simplify)
        return Matrix(SR, self.P)

    def is_formallySelfDual(self):
        """
        Check whether the association scheme is formally self-dual.
        """
        if "fsd" not in self.__dict__:
            self.fsd = (self.eigenmatrix(simplify = 2)
                        - self.dualEigenmatrix(simplify = 2)).is_zero()
        return self.fsd

    def is_pPolynomial(self):
        """
        Check whether the association scheme is P-polynomial,
        and return all P-polynomial orderings if it is.
        """
        if "p" not in self.__dict__:
            self.pTable()
        if "pPolynomial_ordering" not in self.__dict__:
            pPoly = filter(None, (self._is_polynomial(self.p, i)
                                  for i in range(1, self.d+1)))
            self.pPolynomial_ordering = False if len(pPoly) == 0 else pPoly
        return self.pPolynomial_ordering

    def is_qPolynomial(self):
        """
        Check whether the association scheme is Q-polynomial,
        and return all Q-polynomial orderings if it is.
        """
        if "q" not in self.__dict__:
            self.kreinParameters()
        if "qPolynomial_ordering" not in self.__dict__:
            qPoly = filter(None, (self._is_polynomial(self.q, i)
                                  for i in range(1, self.d+1)))
            self.qPolynomial_ordering = False if len(qPoly) == 0 else qPoly
        return self.qPolynomial_ordering

    def kreinParameters(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute and return the Krein parameters.
        """
        self._compute_kreinParameters(expand = expand, factor = factor,
                                      simplify = simplify)
        self.q.rewrite(expand = expand, factor = factor, simplify = simplify)
        return self.q

    def kTable(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the sizes of the subconstituents
        """
        self._compute_kTable(expand = expand, factor = factor,
                             simplify = simplify)
        self.k = rewriteTuple(self.k, expand = expand, factor = factor,
                              simplify = simplify)
        return self.k

    def multiplicities(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the multiplicities of the eigenspaces.
        """
        self._compute_multiplicities(expand = expand, factor = factor,
                                     simplify = simplify)
        self.m = rewriteTuple(self.m, expand = expand, factor = factor,
                              simplify = simplify)
        return self.m

    def pTable(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the intersection numbers.
        """
        self._compute_pTable(expand = expand, factor = factor,
                             simplify = simplify)
        self.p.rewrite(expand = expand, factor = factor, simplify = simplify)
        return self.p

    def quadrupleEquations(self, h, i, j, r, s, t, krein = None,
                           params = None, solve = True, fresh = False,
                           save = None):
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
            if qh not in self.quadruple:
                for p, q in zip(QHPERMS, QDPERMS):
                    hp = tuple(qh[i] for i in p)
                    if hp in self.quadruple:
                        self.quadruple[qh] = self.quadruple[hp].permute(q)
                        break
            if qh in self.quadruple:
                s = self.quadruple[qh]
                if fresh:
                    vars = set(s.variables()).difference(self.vars)
                    if len(vars) > 0:
                        s = s.subs(*refresh(vars))
                        if save:
                            self.quadruple[qh] = s
                return s
        Swxy = self.tripleEquations(h, i, r, fresh = True, save = save)
        assert checkPos(Swxy[j, s, t]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        Swxz = self.tripleEquations(h, j, s, fresh = True, save = save)
        assert checkPos(Swxz[i, r, t]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        Swyz = self.tripleEquations(i, j, t, fresh = True, save = save)
        assert checkPos(Swyz[h, r, s]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        Sxyz = self.tripleEquations(r, s, t, fresh = True, save = save)
        assert checkPos(Sxyz[h, i, j]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" \
            % (h, i, j, r, s, t)
        out = []
        R = range(self.d+1)
        S = [[[[Integer(1) if (A, B, C, D) in [(j, s, t, 0), (i, r, 0, t),
                                               (h, 0, r, s), (0, h, i, j)]
                else SR.symbol("%s_%d_%d_%d_%d_%d_%d_%d_%d_%d_%d" %
                               (self.prefix, h, i, j, r, s, t, A, B, C, D))
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
            pairs = {(A, B): {C for C in R if self.q[C, A, B] == 0}
                     for A in R for B in R}
            krein = [(A, B, C, D) for (A, B), AB in pairs.items()
                                  for (C, D), CD in pairs.items()
                                  if AB | CD == Rs]
        if krein:
            for A, B, C, D in krein:
                Z = sum(self.Q[tA, A] * self.Q[tB, B] *
                        self.Q[tC, C] * self.Q[tD, D] *
                        S[tA][tB][tC][tD] for tA in R for tB in R
                                          for tC in R for tD in R)
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
        Q = Array4D(self.d + 1)
        for A in R:
            for B in R:
                for C in R:
                    for D in R:
                        if isinstance(S[A][B][C][D], Integer):
                            Q[A, B, C, D] = S[A][B][C][D]
                        else:
                            Q[A, B, C, D] = S[A][B][C][D].subs(sol[0])
        if save:
            self.quadruple[h, i, j, r, s, t] = Q
        return Q

    def reorderEigenspaces(self, *order):
        """
        Specify a new order for the eigenspaces.
        """
        order = self._reorder(order)
        if "m" in self.__dict__:
            self.m = tuple(self.m[i] for i in order)
        if "P" in self.__dict__:
            self.P = Matrix(SR, [self.P[i] for i in order])
        if "Q" in self.__dict__:
            self.Q = Matrix(SR, [[r[j] for j in order] for r in self.Q])
        if "q" in self.__dict__:
            self.q.reorder(order)
        if "qPolynomial_ordering" in self.__dict__ \
                and self.qPolynomial_ordering:
            self.qPolynomial_ordering = sorted([tuple(order.index(i)
                                                      for i in o)
                                        for o in self.qPolynomial_ordering])

    def reorderRelations(self, *order):
        """
        Specify a new order for the relations.
        """
        order = self._reorder(order)
        if "k" in self.__dict__:
            self.k = tuple(self.k[i] for i in order)
        if "P" in self.__dict__:
            self.P = Matrix(SR, [[r[j] for j in order] for r in self.P])
        if "Q" in self.__dict__:
            self.Q = Matrix(SR, [self.Q[i] for i in order])
        if "p" in self.__dict__:
            self.p.reorder(order)
        self.triple = {tuple(order.index(i) for i in t):
                       s.reorder(order, inplace = False)
                       for t, s in self.triple.items()}
        self.triple_solution = {tuple(order.index(i) for i in t):
                                {k: s.reorder(order, inplace = False)
                                 for k, s in d.items()}
                                for t, d in self.triple_solution.items()}
        self.triple_solution_generator = {tuple(order.index(i) for i in t): g
                        for t, g in self.triple_solution_generator.items()}
        self.quadruple = {tuple(order.index(i) for i in t):
                          s.reorder(order, inplace = False)
                          for t, s in self.quadruple.items()}
        if "pPolynomial_ordering" in self.__dict__ \
                and self.pPolynomial_ordering:
            self.pPolynomial_ordering = sorted([tuple(order.index(i)
                                                      for i in o)
                                        for o in self.pPolynomial_ordering])

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

    def subs(self, *exp):
        """
        Substitute the given subexpressions in the parameters.
        """
        par = {}
        if "p" in self.__dict__:
            par["p"] = self.p.subs(*exp)
        elif "q" in self.__dict__:
            par["q"] = self.q.subs(*exp)
        elif "P" in self.__dict__:
            par["P"] = self.P.subs(*exp)
        elif "Q" in self.__dict__:
            par["Q"] = self.Q.subs(*exp)
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
            yield self.p[h, i, j]
            return
        for p, q in zip(TPERMS, DPERMS):
            tp = tuple(t[i] for i in p)
            if tp in self.triple:
                yield self.triple[tp][tuple(d[i] for i in q)]

    def tripleEquations(self, u, v, w, krein = None, params = None,
                        solve = True, fresh = False, save = None):
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
            if t not in self.triple:
                for p, q in zip(TPERMS, DPERMS):
                    tp = tuple(t[i] for i in p)
                    if tp in self.triple:
                        self.triple[t] = self.triple[tp].permute(q)
                        break
            if t in self.triple:
                s = self.triple[t]
                if fresh:
                    vars = set(s.variables()).difference(self.vars)
                    if len(vars) > 0:
                        s = s.subs(*refresh(vars))
                        if save:
                            self.triple[t] = s
                return s
        if "Q" not in self.__dict__:
            self.dualEigenmatrix()
        if "p" not in self.__dict__:
            self.pTable()
        assert checkPos(self.p[u, v, w]), \
            "no triple of vertices in relations %d, %d, %d" % (u, v, w)
        if "q" not in self.__dict__:
            self.kreinParameters()
        out = []
        r = range(self.d+1)
        s = [[[Integer(1) if (h, i, j) in [(v, w, 0), (u, 0, w), (0, u, v)]
               else symbol("%s_%d_%d_%d_%d_%d_%d" %
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
                s[h][i][j] = self.p[u, h, i] - sum(s[h][i][t] for t in r
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
                s[h][i][j] = self.p[v, h, j] - sum(s[h][t][j] for t in r
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
                s[h][i][j] = self.p[w, i, j] - sum(s[t][i][j] for t in r
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
                l = sum(self.Q[th, h] * self.Q[ti, i] *
                        self.Q[tj, j] * s[th][ti][tj]
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

    def variables(self):
        """
        Return the variables in the graph parameters.
        """
        return self.vars

    order = __len__


class PolyASParameters(ASParameters):
    ARRAY = None
    DUAL_INTEGRAL = None
    DUAL_PARAMETER = None
    DUAL_PARTS = None
    DUAL_SYMBOL = None
    OBJECT = None
    PARAMETER = None
    PART = None
    PARTS = None
    PTR = None
    QTR = None
    SYMBOL = None

    def __init__(self, b, c = None, order = None):
        """
        Object constructor.

        Check the basic properties of the intersection or Krein array.
        """
        if isinstance(b, ASParameters):
            ASParameters.__init__(self, b)
            if not isinstance(b, PolyASParameters) and \
                    ("P" in b.__dict__ or "Q" in b.__dict__):
                self._copy_cosineSequences(b)
            if order is not None:
                self.reorderParameters(*order)
        else:
            if self.d is None:
                raise NotImplementedError("PolyASParameters can not be "
                                          "instantiated directly")
            assert self.d == len(c) == len(b), "parameter length mismatch"
            self._init_array(b, c)
            assert all(checkPos(x) for x in self.c[1:]), \
                "c sequence not positive"
            assert all(checkPos(x) for x in self.b[:-1]), \
                "b sequence not positive"
            self.a = tuple(full_simplify(b[0]-x-y)
                           for x, y in zip(self.b, self.c))
            assert self.c[1] == 1, "Invalid c[1] value"
            assert all(checkNonneg(x) for x in self.a), \
                "a values negative"
            self.vars = tuple(set(sum(map(variables, tuple(b) + tuple(c)),
                                      ())))
            ASParameters.__init__(self)
        self.hash_parameters = self.parameterArray(factor = True,
                                                   simplify = 2)
        self._init_prefix()

    def __eq__(self, other):
        """
        Compare self to other.
        """
        if isinstance(other, self._get_class()):
            return self.hash_parameters == other.hash_parameters
        else:
            return not isinstance(other, ASParameters) \
                   and self.hash_parameters == other

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash((self.SYMBOL, self.hash_parameters))

    def __repr__(self):
        """
        String representation.
        """
        return "Parameters of a %s with %s %s" % (self.OBJECT, self.ARRAY,
                                                self.format_parameterArray())

    def _check_multiplicity(self, k, i):
        """
        Check the valency of the i-th subconstituent or eigenspace.
        """
        for j in range(self.d + 1):
            if self.a[i] >= k[i]:
                raise InfeasibleError("valency of %s %d too large" %
                                      (self.PART, i))

    def _check_parameter(self, h, i, j, v, integral = False,
                         name = None, sym = None):
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
        return ASParameters._check_parameter(h, i, j, v, integral = integral,
                                             name = name, sym = sym)

    def _compute_cosineSequences(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the cosine sequences of the association scheme.
        """
        if "omega" in self.__dict__:
            return
        if "theta" not in self.__dict__:
            self.eigenvalues(expand = expand, factor = factor,
                             simplify = simplify)
        omega = Matrix(SR, self.d + 1)
        omega[:, 0] = 1
        for i in range(self.d + 1):
            omega[i, 1] = self.theta[i]/self.b[0]
            for j in range(2, self.d + 1):
                omega[i, j] = _simplify(_factor((
                    (self.theta[i] - self.a[j-1]) * omega[i, j-1]
                    - self.c[j-1] * omega[i, j-2]) / self.b[j-1]))
        self.omega = omega

    def _compute_dualEigenmatrix(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        if "Q" in self.__dict__:
            return
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self.Q = self._compute_eigenmatrix(self.multiplicities(**params),
                                           self.QTR, **params)

    def _compute_dualParameters(self, q, k, m, tr):
        """
        Compute the Krein parameters or intersection numbers
        from the cosine sequences.
        """
        for h in range(self.d + 1):
            for i in range(self.d + 1):
                for j in range(self.d + 1):
                    q[h, i, j] = full_simplify(
                                    sum(k[t] * self.omega[tr(h, t)]
                                             * self.omega[tr(i, t)]
                                             * self.omega[tr(j, t)]
                                        for t in range(self.d + 1))
                                    * m[i] * m[j] / self.n)
                    self._check_parameter(h, i, j, q[h, i, j],
                                          integral = self.DUAL_INTEGRAL,
                                          name = self.DUAL_PARAMETER,
                                          sym = self.DUAL_SYMBOL)

    def _compute_eigenmatrix(self, k, tr, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return the eigenmatrix of the association scheme.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        return Matrix(SR, [[self.omega[tr(i, j)] * k[j]
                            for j in range(self.d + 1)]
                           for i in range(self.d + 1)])

    def _compute_eigenvalues(self, p, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return the eigenvalues of the association scheme.
        """
        if "theta" not in self.__dict__:
            if "omega" in self.__dict__:
                self.theta = tuple(r[1] * p[0, 1, 1] for r in self.omega)
            elif self.is_cyclic():
                self.theta = tuple(2*cos(2*i*pi/self.n)
                                   for i in range(self.d + 1))
            else:
                B = Matrix(SR, [M[1] for M in p])
                self.theta = B.eigenvalues()
                try:
                    self.theta.sort(
                        key = lambda x: CoefficientList(x, self.vars),
                        reverse = True)
                except:
                    warn(Warning("Sorting of eigenvalues failed - "
                                 "you may want to sort them manually"))
                else:
                    if not self.vars_ordered:
                        warn(Warning("More than one variable is used - "
                                     "please check that the ordering "
                                     "of the eigenvalues is correct"))
                self.theta = tuple(self.theta)
        self.theta = rewriteTuple(self.theta, expand = expand,
                                  factor = factor, simplify = simplify)
        return self.theta

    def _compute_parameters(self, p, k):
        """
        Compute the intersection numbers or Krein parameters
        from the intersection or Krein array.
        """
        for i in range(self.d + 1):
            p[0, i, i] = k[i]
            p[i, 0, i] = Integer(1)
            p[i, i, 0] = Integer(1)
        for i in range(self.d):
            p[i+1, 1, i+1] = self.a[i+1]
            p[i, 1, i+1] = self.b[i]
            p[i+1, 1, i] = self.c[i+1]
        for i in range(2, self.d + 1):
            for j in range(1, self.d + 1):
                for h in range(1, self.d):
                    p[h, i, j] = self._check_parameter(h, i, j,
                        _simplify(_expand(
                            ( self.c[h] * p[h-1, i-1, j]
                            + self.b[h] * p[h+1, i-1, j]
                            - self.b[i-2] * p[h, i-2, j]
                            + (self.a[h] - self.a[i-1]) * p[h, i-1, j]
                            ) / self.c[i])))
                p[self.d, i, j] = self._check_parameter(h, i, j,
                    _simplify(_expand(
                        ( self.c[self.d] * p[self.d-1, i-1, j]
                        - self.b[i-2] * p[self.d, i-2, j]
                        + (self.a[self.d] - self.a[i-1])
                            * p[self.d, i-1, j]
                        ) / self.c[i])))

    def _compute_primalEigenmatrix(self, expand = False, factor = False,
                                   simplify = False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        if "P" in self.__dict__:
            return
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self.P = self._compute_eigenmatrix(self.kTable(**params),
                                           self.PTR, **params)

    def _compute_sizes(self, k, expand = False, factor = False,
                       simplify = False):
        """
        Compute multiplicities of the eigenspaces
        or sizes of the subconstituents.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        if "theta" not in self.__dict__:
            self.eigenvalues(expand = expand, factor = factor,
                             simplify = simplify)
        if self.is_cyclic():
            m = tuple(Integer(1 if th in [2, -2] else 2)
                      for th in self.theta)
        else:
            try:
                m = tuple(integralize(_simplify(_factor(
                                        self.n / sum(s * om**2 for s, om
                                                in zip(k, omg)))))
                               for omg in self.omega)
            except TypeError:
                raise InfeasibleError("%s not integral" % self.DUAL_PARTS)
        return m

    def _copy(self, p):
        """
        Copy fields to the given obejct.
        """
        ASParameters._copy(self, p)
        if isinstance(p, self._get_class()):
            if "theta" in self.__dict__:
                p.theta = self.theta
            if "omega" in self.__dict__:
                p.omega = copy(self.omega)
        elif "omega" in self.__dict__:
            if isinstance(p, PolyASParameters):
                p.omega = self.omega.transpose()
            elif "P" not in p.__dict__ and "Q" not in p.__dict__:
                p.P = p.eigenmatrix()

    def _copy_cosineSequences(self, P):
        """
        Obtain the cosine sequences from an eigenmatrix.
        """
        self.omega = P / diagonal_matrix(P[0])

    def _init_array(self, b, c):
        """
        Initialize the intersection or Krein array.
        """
        self.c = (Integer(0), ) + tuple(c)
        self.b = tuple(b) + (Integer(0), )

    def _init_multiplicities(self):
        """
        Compute the sizes of subconstituents
        or multiplicities of the eigenvalues
        from the intersection or Krein array.
        """
        k = [Integer(1)]
        try:
            for i in range(1, self.d + 1):
                k.append(integralize(k[-1]*self.b[i-1]/self.c[i]))
                self._check_multiplicity(k, i)
        except TypeError:
            raise InfeasibleError("%s not integral" % self.PARTS)
        self.n = sum(k)
        return k

    def _subs(self, exp, p):
        """
        Substitute the given subexpressions in the parameters.
        """
        if "theta" in self.__dict__:
            p.theta = tuple(subs(th, *exp) for th in self.theta)
        if "omega" in self.__dict__:
            p.omega = self.omega.subs(*exp)
        ASParameters._subs(self, exp, p)

    def aTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of parameters ``a[1], a[2], ..., a[d]``,
        where ``d`` is the number of classes of the association scheme.
        """
        self.a = rewriteTuple(self.a, expand = expand, factor = factor,
                              simplify = simplify)
        return self.a[1:]

    def bTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of parameters ``b[0], b[1], ..., b[d-1]``,
        where ``d`` is the number of classes of the association scheme.
        """
        self.b = rewriteTuple(self.b, expand = expand, factor = factor,
                              simplify = simplify)
        return self.b[:-1]

    def cTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of parameters ``c[1], c[2], ..., c[d]``,
        where ``d`` is the number of classes of the association scheme.
        """
        self.c = rewriteTuple(self.c, expand = expand, factor = factor,
                              simplify = simplify)
        return self.c[1:]

    def cosineSequences(self, index = None, ev = None, expand = False,
                        factor = False, simplify = False):
        """
        Compute and return the cosine sequences
        for each subconstituent and eigenspace.
        """
        self._compute_cosineSequences(expand = expand, factor = factor,
                                      simplify = simplify)
        rewriteMatrix(self.omega, expand = expand, factor = factor,
                      simplify = simplify)
        if ev is not None:
            if "theta" not in self.__dict__:
                self.eigenvalues(expand = expand, factor = factor,
                                 simplify = simplify)
            try:
                index = self.theta.index(ev)
            except ValueError as ex:
                if index is None:
                    raise ex
        if index is not None:
            return self.omega[index]
        return Matrix(SR, self.omega)

    def eigenvalues(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the eigenvalues of the association scheme.

        Not implemented, to be overridden.
        """
        raise NotImplementedError

    def format_parameterArray(self):
        """
        Return a string representation of the intersection array.
        """
        return "{%s; %s}" % tuple(', '.join(str(x) for x in l)
                                  for l in self.parameterArray())

    def is_cyclic(self):
        """
        Check whether the association scheme is cyclic.
        """
        return self.b[0] == 2 and self.c[-1] in [1, 2] and \
            all(x == 1 for x in self.b[1:-1] + self.c[1:-1])

    def match(self, *ial):
        """
        Check whether the association scheme
        matches any of the given intersection or Krein arrays.
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

    def parameterArray(self, expand = False, factor = False,
                       simplify = False):
        """
        Return the intersection or Krein array of the association scheme
        as a tuple of two tuples.
        """
        return (self.bTable(expand = expand, factor = factor,
                            simplify = simplify),
                self.cTable(expand = expand, factor = factor,
                            simplify = simplify))

    def reorderEigenvalues(self, *order):
        """
        Specify a new order for the eigenvalues and return it.

        Performs the part of the reordering that is common
        to P- and Q-polynomial association schemes.
        """
        order = self._reorder(order)
        if "theta" not in self.__dict__:
            self.eigenvalues()
        self.theta = tuple(self.theta[i] for i in order)
        if "omega" in self.__dict__:
            self.omega = Matrix(SR, [self.omega[i] for i in order])
        if "fsd" in self.__dict__:
            del self.fsd
        return order

    def reorderParameters(self, p, *order):
        """
        Specify a new order for the parameters and return it.

        Performs the part of the reordering that is common
        to P- and Q-polynomial association schemes.
        """
        self.a = tuple(p[i, i, 1] for i in range(self.d + 1))
        self.b = tuple(p[i, i+1, 1] if i < self.d else Integer(0)
                       for i in range(self.d + 1))
        self.c = tuple(p[i, i-1, 1] if i > 0 else Integer(0)
                       for i in range(self.d + 1))
        if "omega" in self.__dict__:
            self.omega = Matrix(SR, [[r[i] for i in order]
                                     for r in self.omega])
        if "theta" in self.__dict__:
            del self.theta
        if "fsd" in self.__dict__:
            del self.fsd
