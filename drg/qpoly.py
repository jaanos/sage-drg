from sage.matrix.constructor import Matrix
from sage.rings.integer import Integer
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .array3d import Array4D
from .assoc_scheme import ASParameters
from .assoc_scheme import PolyASParameters
from .util import checkPos
from .util import pair_keep
from .util import pair_swap
from .util import subs
from .util import variables

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

class QPolyParameters(PolyASParameters):
    """
    A class for parameters of a Q-polynomial association scheme
    and checking their feasibility.
    """

    ARRAY = "Krein array"
    DUAL_INTEGRAL = True
    DUAL_PARAMETER = "intersection number"
    DUAL_PARTS = "subconstituents"
    DUAL_SYMBOL = "p"
    OBJECT = "Q-polynomial association scheme"
    PARAMETER = "Krein parameter"
    PART = "eigenspace"
    PARTS = "multiplicities"
    SYMBOL = "q"
    PTR = pair_swap
    QTR = pair_keep

    def __init__(self, b, c = None, order = None):
        """
        Object constructor.

        Takes two iterables of the same length ``d`` as input,
        representing the Krein array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}``.
        The basic checks on nonnegativity
        of the Krein array are performed.
        """
        if isinstance(b, ASParameters):
            o = b.is_qPolynomial()
            assert o, "scheme not Q-polynomial"
            self.d = b.d
            if order is None:
                order = o[0]
            else:
                order = self._reorder(order)
            assert order in o, "scheme not Q-polynomial for given order"
            PolyASParameters.__init__(self, b, order = order)
            if isinstance(b, QPolyParameters):
                return
        else:
            self.d = Integer(len(b))
            PolyASParameters.__init__(self, b, c)
            self.m = tuple(self._init_multiplicities())
            self.q = Array3D(self.d + 1)
            self._compute_parameters(self.q, self.m)
        self.bipartite = all(a == 0 for a in self.a)

    def _compute_kreinParameters(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the Krein parameters.

        Does nothing, as they are already computed
        for Q-polynomial association schemes,
        """
        pass

    def _compute_kTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the sizes of the subconstituents.
        """
        if "k" not in self.__dict__:
            self.k = self._compute_sizes(self.m, expand = expand,
                                         factor = factor, simplify = simplify)

    def _compute_multiplicities(self, expand = False, factor = False,
                                simplify = False):
        """
        Compute the multiplicities of the eigenspaces.

        Does nothing, as they are already computed
        for Q-polynomial association schemes,
        """
        pass

    def _compute_pTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the intersection numbers.
        """
        if "k" not in self.__dict__:
            self.kTable(expand = expand, factor = factor, simplify = simplify)
        if "p" not in self.__dict__:
            p = Array3D(self.d + 1)
            self._compute_dualParameters(p, self.m, self.k, self.QTR)
            self.p = p
            self.check_handshake()

    def _copy(self, p):
        """
        Copy fields to the given obejct.
        """
        PolyASParameters._copy(self, p)
        if isinstance(p, QPolyParameters):
            p.bipartite = self.bipartite

    def _copy_cosineSequences(self, p):
        """
        Obtain the cosine sequences from the dual eigenmatrix.
        """
        PolyASParameters._copy_cosineSequences(self, p.dualEigenmatrix())

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return QPolyParameters

    def eigenvalues(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the dual eigenvalues of the first eigenspace
        of the Q-polynomial association scheme.
        """
        return self._compute_eigenvalues(self.q, expand = expand,
                                         factor = factor, simplify = simplify)

    def reorderEigenspaces(self, *order):
        """
        Specify a new order for the eigenspaces.
        """
        self.reorderParameters(*order)

    def reorderEigenvalues(self, *order):
        """
        Specify a new order for the eigenvalues and return it.
        """
        order = PolyASParameters.reorderEigenvalues(self, *order)
        PolyASParameters.reorderRelations(self, *order)
        return self.theta

    def reorderParameters(self, *order):
        """
        Specify a new order for the parameters and return them.
        """
        order = self._reorder(order)
        assert order in self.is_qPolynomial(), \
            "scheme not Q-polynomial for the given order"
        PolyASParameters.reorderEigenspaces(self, *order)
        PolyASParameters.reorderParameters(self, self.q, *order)
        return self.parameterArray()

    def reorderRelations(self, *order):
        """
        Specify a new order for the relations.
        """
        self.reorderEigenvalues(*order)

    def subs(self, *exp):
        """
        Substitute the given subexpressions in the parameters.
        """
        p = QPolyParameters(*[[subs(x, *exp) for x in l]
                              for l in self.kreinArray()])
        self._subs(exp, p)
        if "p" in self.__dict__:
            p.p = self.p.subs(*exp)
            p._check_parameters(p.p, integral = self.DUAL_INTEGRAL,
                                name = self.DUAL_PARAMETER,
                                sym = self.DUAL_SYMBOL)
        return p

    kreinArray = PolyASParameters.parameterArray

class QBipartiteParameters(QPolyParameters):
    """
    A class for parameters of a Q-bipartite association scheme
    and checking their feasibility.
    """

    def __init__(self, b):
        """
        Object constructor.

        Takes an iterable as input,
        representing the first part of the Krein array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}``.
        The second part is computed as
        ``c[i] = b[0] - b[i]``, where ``b[d] == 0``.
        The basic checks on nonnegativity
        of the Krein array are performed.
        """
        QPolyParameters.__init__(self, b, [b[0] - x for x in b[1:]] + [b[0]])
        self.quadruple = {}

    def quadrupleEquations(self, h, i, j, r, s, t, params = None,
                           solve = True, save = True):
        """
        Solve equations for quadruples of vertices ``w, x, y, z``
        such that ``d(w, x) = h``, ``d(w, y) = i``, ``d(w, z) = j``,
        ``d(x, y) = r``, ``d(x, z) = s``, ``d(y, z) = t``.

        If ``params`` is a dictionary mapping strings to quadruples,
        the keys will be used as variables mapped to quadruple intersection
        numbers for corresponding quadruples.
        If ``solve`` is ``False``,
        only a list of equations and a set of variables is returned,
        without solving the equations.
        """
        if solve and params is None:
            qh = (h, i, j, r, s, t)
            for p, q in zip(QHPERMS, QDPERMS):
                hp = tuple(qh[i] for i in p)
                if hp in self.quadruple:
                    self.quadruple[qh] = self.quadruple[hp].permute(q)
                    return self.quadruple[qh]
        Swxy = self.tripleEquations(h, i, r, solve = solve, save = save)
        assert checkPos(Swxy[j, s, t]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" % \
            (h, i, j, r, s, t)
        Swxz = self.tripleEquations(h, j, s, solve = solve, save = save)
        assert checkPos(Swxz[i, r, t]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" % \
            (h, i, j, r, s, t)
        Swyz = self.tripleEquations(i, j, t, solve = solve, save = save)
        assert checkPos(Swyz[h, r, s]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" % \
            (h, i, j, r, s, t)
        Sxyz = self.tripleEquations(r, s, t, solve = solve, save = save)
        assert checkPos(Sxyz[h, i, j]), \
            "no quadruple of vertices in relations %d, %d, %d, %d, %d, %d" % \
            (h, i, j, r, s, t)
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
                    Z = sum(S[U][V][W][X] for X in R)
                    if isinstance(Z, Integer):
                        assert Swxy[U, V, W] == Z, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                                (h, i, r, U, V, W)
                    else:
                        out.append(Swxy[U, V, W] == Z)
                    Z = sum(S[U][V][X][W] for X in R)
                    if isinstance(Z, Integer):
                        assert Swxz[U, V, W] == Z, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                                (h, j, s, U, V, W)
                    else:
                        out.append(Swxz[U, V, W] == Z)
                    Z = sum(S[U][X][V][W] for X in R)
                    if isinstance(Z, Integer):
                        assert Swyz[U, V, W] == Z, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                                (i, j, t, U, V, W)
                    else:
                        out.append(Swyz[U, V, W] == Z)
                    Z = sum(S[X][U][V][W] for X in R)
                    if isinstance(Z, Integer):
                        assert Sxyz[U, V, W] == Z, \
                            "value of s[%d, %d, %d][%d, %d, %d] exceeded" % \
                                (r, s, t, U, V, W)
                    else:
                        out.append(Sxyz[U, V, W] == Z)
        for A in range(1, self.d+1):
            for B in range(1, self.d+1):
                for C in range(1, self.d+1):
                    for D in range((A+B+C+1) % 2, self.d+1, 2):
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

class MUBParameters(QBipartiteParameters):
    """
    A class for parameters of an association scheme
    corresponding to a collection of real mutually unbiases bases
    and checking their feasibility.
    """

    def __init__(self, d, w):
        """
        Object constructor.

        Constructs the parameters of the association schemes
        of ``w`` mutually unbiased bases in a ``d``-dimensional
        vector space over the real numbers.
        """
        QBipartiteParameters.__init__(self, [d, d-1, d*(w-1)/w, 1])
