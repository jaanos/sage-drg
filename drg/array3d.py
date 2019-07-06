from copy import copy
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.matrix.constructor import Matrix
from sage.symbolic.ring import SR
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

    def __copy__(self):
        """
        Return a copy of the array.
        """
        A = Array3D(self.n)
        A.A = [copy(M) for M in self.A]
        return A

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
        return int(self.n)

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

    def reorder(self, order, inplace=True):
        """
        Reorder each dimension in the array.
        """
        assert len(order) == self.n, "wrong number of indices"
        assert set(order) == set(range(self.n)), \
            "repeating or nonexisting indices"
        A = self if inplace else Array3D(self.n)
        A.A = [Matrix(SR, [[self.A[h][i, j] for j in order] for i in order])
               for h in order]
        return A

    def rewrite(self, expand=False, factor=False, simplify=False):
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

    def subs(self, *exp):
        """
        Substitute the given subexpressions in the array.
        """
        A = Array3D(self.n)
        for i, M in enumerate(self.A):
            A.A[i] = M.subs(*exp)
        return A

    def variables(self):
        """
        Return the variables occuring in the array.
        """
        return tuple(set(sum((variables(x)
                              for M in self for r in M for x in r), ())))

    substitute = subs
