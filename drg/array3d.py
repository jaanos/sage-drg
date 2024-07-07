from copy import copy
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.matrix.constructor import Matrix
from sage.misc.latex import latex
from sage.misc.latex import LatexExpr
from sage.structure.sage_object import SageObject
from sage.symbolic.ring import SR
from sage.typeset.ascii_art import ascii_art
from sage.typeset.unicode_art import unicode_art
from .util import _factor
from .util import full_simplify
from .util import variables


class Array3D(SageObject):
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
        fmt = f'%{l}d: '
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

    def _ascii_art_(self):
        """
        ASCII art representation of the array.
        """
        l = len(repr(self.n - 1))
        fmt = f'%{l}d: '
        art = [ascii_art(M) for M in self.A]
        return ascii_art("\n".join((fmt % i) + "\n"*a.height()
                                   for i, a in enumerate(art))) + \
            ascii_art("\n".join(sum([a._matrix + [""] for a in art], [])))

    def _latex_(self):
        """
        LaTeX representation of the array.
        """
        return LatexExpr(r"\begin{aligned}%s\end{aligned}" %
                         "\n".join(r"%d: &\ %s \\" % (i, latex(M))
                                   for i, M in enumerate(self.A)))

    def _unicode_art_(self):
        """
        Unicode art representation of the array.
        """
        l = len(repr(self.n - 1))
        fmt = f'%{l}d: '
        art = [unicode_art(M) for M in self.A]
        return unicode_art("\n".join((fmt % i) + "\n"*a.height()
                                     for i, a in enumerate(art))) + \
            unicode_art("\n".join(sum([a._matrix + [""] for a in art], [])))

    def map(self, fun):
        """
        Replace each value by its image under ``fun``.
        """
        for M in self.A:
            for i in range(self.n):
                M[i] = tuple(map(fun, M[i]))

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
        Return the variables occurring in the array.
        """
        return tuple(set(sum((variables(x)
                              for M in self for r in M for x in r), ())))

    substitute = subs


class Array4D(SageObject):
    """
    A four-dimensional array of expressions.
    """

    def __init__(self, n):
        """
        Object constructor.

        ``n`` is the size of the array in each dimension.
        """
        self.A = [Array3D(n) for i in range(n)]
        self.n = n

    def __copy__(self):
        """
        Return a copy of the array.
        """
        Q = Array4D(self.n)
        Q.A = [copy(A) for A in self.A]
        return Q

    def __eq__(self, other):
        """
        Equality comparison.
        """
        if isinstance(other, Array4D):
            return self.n == other.n and self.A == other.A
        return all(x == other for A in self for M in A for r in M for x in r)

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
                elif len(key) == 4:
                    s1, s2, s3, s4 = key
                    sm = (s2, s3, s4)
                else:
                    raise IndexError("index must be an integer, a slice, "
                                     "or a tuple of at most four of those")
                if isinstance(s1, slice):
                    return [A[sm] for A in self.A[s1]]
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
        fmt = f'%{l}d'
        return '\n\n'.join((f'({fmt % i}, {fmt % j}): ') +
                           repr(M).replace('\n', '\n' + (' ' * (2*l+6)))
                           for i, A in enumerate(self.A)
                           for j, M in enumerate(A))

    def __setitem__(self, key, value):
        """
        Set ``value`` at position determined by ``key``,
        which must be a quadruple of integers.
        """
        k1, k2, k3, k4 = key
        self.A[k1][k2, k3, k4] = value

    def _ascii_art_(self):
        """
        ASCII art representation of the array.
        """
        l = len(repr(self.n - 1))
        fmt = f'%{l}d'
        art = [(f"({fmt % i}, {fmt % j}): ", ascii_art(M))
               for i, A in enumerate(self.A) for j, M in enumerate(A)]
        return ascii_art("\n".join(i + "\n"*a.height() for i, a in art)) + \
            ascii_art("\n".join(sum([a._matrix + [""] for i, a in art], [])))

    def _latex_(self):
        """
        LaTeX representation of the array.
        """
        return LatexExpr(r"\begin{aligned}%s\end{aligned}" %
                         "\n".join(r"(%d, %d): &\ %s \\" % (i, j, latex(M))
                                   for i, A in enumerate(self.A)
                                   for j, M in enumerate(A)))

    def _unicode_art_(self):
        """
        Unicode art representation of the array.
        """
        l = len(repr(self.n - 1))
        fmt = f'%{l}d'
        art = [(f"({fmt % i}, {fmt % j}): ", unicode_art(M))
               for i, A in enumerate(self.A) for j, M in enumerate(A)]
        return unicode_art("\n".join(i + "\n"*a.height() for i, a in art)) + \
            unicode_art("\n".join(sum([a._matrix + [""] for i, a in art],
                                      [])))

    def map(self, fun):
        """
        Replace each value by its image under ``fun``.
        """
        for A in self.A:
            for M in A:
                for i in range(self.n):
                    M[i] = map(fun, M[i])

    def permute(self, p):
        """
        Return an array with permuted dimensions.
        """
        if tuple(p) == (0, 1, 2, 3):
            return self
        A = Array4D(self.n)
        for h in range(self.n):
            for i in range(self.n):
                for j in range(self.n):
                    for k in range(self.n):
                        t = (h, i, j, k)
                        A[t] = self[tuple(t[i] for i in p)]
        return A

    def reorder(self, order, inplace=True):
        """
        Reorder each dimension in the array.
        """
        assert len(order) == self.n, "wrong number of indices"
        assert set(order) == set(range(self.n)), \
            "repeating or nonexisting indices"
        A = [Array3D(self.n) for k in range(self.n)]
        for l, h in enumerate(order):
            A[l].A = [Matrix(SR, [[self.A[h][i, j, k] for k in order]
                                  for j in order]) for i in order]
        Q = self if inplace else Array4D(self.n)
        Q.A = A
        return Q

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
        S = Array4D(self.n)
        S.A = [A.subs(*exp) for i, A in enumerate(self)]
        return S

    def variables(self):
        """
        Return the variables occurring in the array.
        """
        return tuple(set(sum((variables(x)
                              for A in self for M in A for r in M for x in r),
                             ())))

    substitute = subs
