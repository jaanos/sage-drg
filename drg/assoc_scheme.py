from warnings import warn
from sage.all import pi
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.functions.trig import cos
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import identity_matrix
from sage.rings.integer import Integer
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .coefflist import CoefficientList
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
from .util import rewriteExp
from .util import rewriteMatrix
from .util import rewriteTuple
from .util import subs
from .util import variables

TPERMS = [[0, 1, 2], [0, 2, 1], [1, 0, 2],
          [1, 2, 0], [2, 0, 1], [2, 1, 0]]
DPERMS = [[0, 1, 2], [1, 0, 2], [0, 2, 1],
          [2, 0, 1], [1, 2, 0], [2, 1, 0]]

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

    def __init__(self, p = None, q = None):
        """
        Object constructor.
        """
        # TODO: initialize from p or q array
        self._init_vars()
        self.prefix = "v%x" % (hash(self) % Integer(2)**32)
        self.triple = {}
        self.triple_solution = {}
        self.triple_solution_generator = {}

    def __len__(self, expand = False, factor = False, simplify = False):
        """
        Return the number of vertices.
        """
        self.n = rewriteExp(self.n, expand = expand, factor = factor,
                            simplify = simplify)
        return self.n

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
        # TODO
        pass

    def _compute_eigenmatrix(self, p, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return an eigenmatrix of the association scheme.
        """
        # TODO
        B = [Matrix(SR, [M[i] for M in p]) for i in range(self.d + 1)]

    def _compute_kreinParameters(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the Krein parameters.
        """
        # TODO
        pass

    def _compute_kTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the sizes of the subconstituents.
        """
        # TODO
        pass

    def _compute_multiplicities(self, expand = False, factor = False,
                                simplify = False):
        """
        Compute the multiplicities of the eigenspaces.
        """
        # TODO
        pass

    def _compute_primalEigenmatrix(self, expand = False, factor = False,
                                   simplify = False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        # TODO
        pass

    def _compute_pTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the intersection numbers.
        """
        # TODO
        pass

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return ASParameters

    def _init_vars(self):
        """
        Initialize the list of variables.
        """
        # TODO: obtain variables if not yet available
        self.vars_ordered = len(self.vars) <= 1

    def _subs(self, exp, p):
        """
        Substitute the given subexpressions in the eigenmatrices.
        """
        if "P" in self.__dict__:
            p.P = self.P.subs(exp)
        if "Q" in self.__dict__:
            p.Q = self.Q.subs(exp)
        for k, v in self.triple.items():
            p.triple[k] = v.subs(exp)

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
                    g[u, v, w] = S.find(solver = solver)
                    try:
                        sol = next(g[u, v, w])
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
                try:
                    sol = next(g[t])
                    s = r[t][sol] = self.triple[t].subs(sol)
                    zero[t] -= {d for d in zero[t] if s[d] != 0}
                    if len(zero[t]) == 0:
                        check.discard(t)
                    continue
                except StopIteration:
                    del g[t]
                except KeyError:
                    pass
                check.discard(t)
                u, v, w = t
                for h, i, j in list(zero[t]):
                    for lt, ld in {((u, h, i), (v, w, j)),
                                   ((v, h, j), (u, w, i)),
                                   ((w, i, j), (u, v, h))}:
                        st = tuple(sorted(lt))
                        if st not in zero:
                            continue
                        seen = set()
                        if st == t:
                            seen.add((h, i, j))
                        for tp, dp in zip(TPERMS, DPERMS):
                            if tuple(lt[k] for k in tp) != st:
                                continue
                            sd = tuple(ld[k] for k in dp)
                            if sd in seen:
                                continue
                            seen.add(sd)
                            l = len(r[st])
                            for sol, s in r[st].items():
                                if s[sd] != 0:
                                    del r[st][sol]
                            try:
                                sol = g[st].send(sd)
                                r[st][sol] = self.triple[st].subs(sol)
                                zero[st] -= {d for d in zero[st]
                                             if s[d] != 0}
                                if len(zero[st]) == 0:
                                    check.discard(st)
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
                                zero[st] = {(h, i, j)
                                            for h in range(self.d + 1)
                                            for i in range(self.d + 1)
                                            for j in range(self.d + 1)
                                            if (h, i, j) not in done[st]
                                            and self._check_zero(h, i, j,
                                                                 *st)
                                            and all(s[h, i, j] == 0 for s
                                                    in r[st].values())}
                                if len(zero[st]) == 0:
                                    check.discard(st)
                                else:
                                    check.add(st)
                    zero[t].discard((h, i, j))
                    done[t].add((h, i, j))

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

    def subs(self, exp):
        """
        Substitute the given subexpressions in the parameters.
        """
        par = {}
        if "p" in self.__dict__:
            par["p"] = self.p.subs(exp)
        if "q" in self.__dict__:
            par["q"] = self.q.subs(exp)
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
                        solve = True, save = None):
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
                if tp in self.triple:
                    self.triple[t] = self.triple[tp].permute(q)
                    return self.triple[t]
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
                x = SR.symbol(a)
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
    PARTS = None
    PTR = None
    QTR = None
    SYMBOL = None

    def __init__(self, b, c):
        """
        Object constructor.

        Check the basic properties of the intersection or Krein array.
        """
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
        self.vars = tuple(set(sum(map(variables, tuple(b) + tuple(c)), ())))
        ASParameters.__init__(self)

    def __eq__(self, other):
        """
        Compare self to other.
        """
        ia = self.parameterArray()
        if isinstance(other, self._get_class()):
            return ia == other.parameterArray()
        else:
            return not isinstance(other, ASParameters) and ia == other

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash((self.SYMBOL, self.parameterArray()))

    def __repr__(self):
        """
        String representation.
        """
        return "Parameters of a %s with %s %s" % (self.OBJECT, self.ARRAY,
                                                self.format_parameterArray())

    def _check_multiplicity(self, k, i):
        """
        Check for the feasibility of the i-th multiplicity.

        By default, no checks are performed.
        """
        pass

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

    def _compute_dualEigenmatrix(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self.Q = self._compute_eigenmatrix(self.multiplicities(*params),
                                           self.QTR, *params)

    def _compute_dualParameters(self, q, k, m, tr, n = 1):
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
            if self.is_cyclic():
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
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self.P = self._compute_eigenmatrix(self.kTable(*params),
                                           self.PTR, *params)

    def _compute_sizes(self, k, expand = False, factor = False,
                       simplify = False):
        """
        Compute multiplicities of the eigenspaces
        or sizes of the subconstituents.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
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
            for i in range(self.d):
                k.append(integralize(k[-1]*self.b[i]/self.c[i+1]))
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
            p.theta = tuple(subs(th, exp) for th in self.theta)
        if "omega" in self.__dict__:
            p.omega = self.omega.subs(exp)
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
            try:
                index = self.theta.index(ev)
            except ValueError as ex:
                if index is None:
                    raise ex
        if index is not None:
            return self.omega[index]
        return Matrix(SR, self.omega)

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
            all(x == 1 for x in self.b[1:] + self.c[:-1])

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
        if "fsd" in self.__dict__:
            del self.fsd
        return order
