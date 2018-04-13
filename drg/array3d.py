from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.matrix.constructor import Matrix
from sage.numerical.mip import MIPSolverException
from sage.numerical.mip import MixedIntegerLinearProgram
from sage.rings.integer import Integer
from sage.symbolic.ring import SR
from .util import checkNonneg
from .util import integralize
from .util import is_constant
from .util import _factor
from .util import full_simplify
from .util import variables

class Array3D:
    """
    A three-dimensional array of expressions.
    """

    def __init__(self, n):
        """
        Object constructor.

        ``n`` is the size of the array in each dimension.
        """
        self.A = [Matrix(SR, n) for i in range(n)]
        self.n = n

    def __eq__(self, other):
        """
        Equality comparison.
        """
        if isinstance(other, Array3D):
            return self.n == other.n and self.A == other.A
        return all(x == other for M in self for r in M for x in r)

    def __getitem__(self, key):
        """
        Return the value at item ``key``,
        which must be an integer, a slice,
        or a tuple of at most three of those.
        """
        if isinstance(key, tuple):
            if len(key) == 1:
                key, = key
            else:
                if len(key) == 2:
                    s1, sm = key
                elif len(key) == 3:
                    s1, s2, s3 = key
                    sm = (s2, s3)
                else:
                    raise IndexError("index must be an integer, a slice, "
                                     "or a tuple of at most three of those")
                if isinstance(s1, slice):
                    return [M[sm] for M in self.A[s1]]
                else:
                    return self.A[s1][sm]
        return self.A[key]

    def __len__(self):
        """
        Return the size of the array in each dimension.
        """
        return self.n

    def __repr__(self):
        """
        String representation of the array.
        """
        l = len(repr(self.n - 1))
        fmt = '%{}d: '.format(l)
        return '\n\n'.join((fmt % i) + repr(M).replace('\n',
                                                       '\n' + (' ' * (l+2)))
                           for i, M in enumerate(self.A))

    def __setitem__(self, key, value):
        """
        Set ``value`` at position determined by ``key``,
        which must be a triple of integers.
        """
        k1, k2, k3 = key
        self.A[k1][k2, k3] = value

    def find(self, vars = None, zeros = None, solver = None):
        """
        Generate assignments of values to variables
        such that the values in the array are nonnegative integers.

        Assumes that the entries are linear in the variables.
        """
        if vars is None:
            vars = self.variables()
        zeros = set() if zeros is None else set(zeros)
        if len(vars) > 0:
            x, rest = vars[0], vars[1:]
            zero = [z == 0 for z in vars]
            lp = MixedIntegerLinearProgram(maximization = False,
                                           solver = solver)
            v = lp.new_variable(integer = True)
            lp.add_constraint(lp[1] == 1)
            def makeLPExpression(e):
                return sum(e.coefficient(y) * v[str(y)] for y in vars) \
                       + e.subs(zero) * lp[1]
        else:
            x = None
        for h, M in enumerate(self):
            for i, r in enumerate(M):
                for j, e in enumerate(r):
                    if is_constant(e):
                        try:
                            integralize(e)
                        except TypeError:
                            return
                        if not checkNonneg(e):
                            return
                        continue
                    elif x is None:
                        return
                    lpe = makeLPExpression(e)
                    lp.add_constraint(lpe == 0 if (h, i, j) in zeros
                                               else lpe >= 0)
        if x is None:
            yield ()
            return
        lp.set_objective(-v[str(x)])
        try:
            vmax = -lp.solve()
        except MIPSolverException as ex:
            if len(ex.args) == 0 or 'feasible' in ex.args[0]:
                return
        lp.set_objective(v[str(x)])
        vmin = lp.solve()
        while vmin <= vmax:
            eq = x == Integer(vmin)
            g = self.subs(eq).find(vars = rest, zeros = zeros)
            try:
                t = None
                while True:
                    t = (yield (eq, ) + g.send(t))
                    if t is not None:
                        if t in zeros:
                            t = None
                            continue
                        zeros.add(t)
                        lp.add_constraint(makeLPExpression(self[t]) == 0)
                        lp.set_objective(-v[str(x)])
                        try:
                            vmax = -lp.solve()
                        except MIPSolverException:
                            return
                        lp.set_objective(v[str(x)])
                        vnew = lp.solve()
                        if vnew > vmin:
                            vmin = vnew
                            break
            except StopIteration:
                vmin += 1

    def map(self, fun):
        """
        Replace each value by its image under ``fun``.
        """
        for M in self.A:
            for i in range(self.n):
                M[i] = map(fun, M[i])

    def permute(self, p):
        """
        Return an array with permuted dimensions.
        """
        if tuple(p) == (0, 1, 2):
            return self
        A = Array3D(self.n)
        for h in range(self.n):
            for i in range(self.n):
                for j in range(self.n):
                    t = (h, i, j)
                    A[t] = self[tuple(t[i] for i in p)]
        return A

    def reorder(self, order):
        """
        Reorder each dimension in the array.
        """
        assert len(order) == self.n, "wrong number of indices"
        assert set(order) == set(range(self.n)), \
            "repeating or nonexisting indices"
        self.A = [Matrix(SR, [[self.A[h][i, j] for j in order] for i in order])
                  for h in order]

    def rewrite(self, expand = False, factor = False, simplify = False):
        """
        Rewrite the array.
        """
        if expand:
            self.map(_expand)
        if factor:
            self.map(_factor)
        if simplify > 1:
            self.map(full_simplify)
        elif simplify:
            self.map(_simplify)

    def subs(self, exp):
        """
        Substitute the given subexpressions in the array.
        """
        A = Array3D(self.n)
        for i, M in enumerate(self.A):
            A.A[i] = M.subs(exp)
        return A

    def variables(self):
        """
        Return the variables occuring in the array.
        """
        return tuple(set(sum((variables(x)
                              for M in self for r in M for x in r), ())))

    substitute = subs
