from sage.misc.functional import numerical_approx
from sage.rings.integer import Integer
from sage.symbolic.expression import Expression
from sage.symbolic.ring import SR

from .util import checkPos
from .util import variables

try:
    from sage.rings.complex_mpfr import ComplexNumber
except ImportError:
    from sage.rings.complex_number import ComplexNumber


class CoefficientList:
    """
    A list of coefficients of an expression.
    """

    def __init__(self, exp, vars=None):
        """
        Object constructor.

        ``exp`` is the expression,
        and ``vars`` is the optional list of variables.
        """
        if vars is None:
            vars = variables(exp)
        self.height = len(vars)
        if self.height == 0:
            self.val = exp
        else:
            if isinstance(exp, Expression):
                c = exp.coefficients(vars[0])
            else:
                c = [[exp, 0]]
            v1 = vars[1:]
            self.val = {k: CoefficientList(v, v1) for v, k in c}

    def __cmp__(self, other):
        """
        Compare two coefficient lists of the same height.
        """
        if other is not None:
            assert self.height == other.height, "comparing unequal heights"
        if self.height == 0:
            if other is None:
                val = Integer(0)
            else:
                val = other.val
            d = SR(self.val - val)
            if d.is_constant():
                d = numerical_approx(d)
                if isinstance(d, ComplexNumber):
                    p = (d.real_part(), d.imag_part())
                else:
                    p = (d, 0)
                if p > (0, 0):
                    return 1
                elif p < (0, 0):
                    return -1
            elif checkPos(self.val - val):
                return 1
            elif checkPos(val - self.val):
                return -1
            return 0
        if other is None:
            keys = set()
        else:
            keys = set(other.val)
        for k in sorted(keys.union(self.val), reverse=True):
            if k not in keys:
                c = self.val[k].__cmp__(None)
            elif k not in self.val:
                c = -other.val[k].__cmp__(None)
            else:
                c = self.val[k].__cmp__(other.val[k])
            if c != 0:
                return c
        return 0

    def __eq__(self, other):
        """
        Equality comparison.
        """
        return self.height == other.height and self.val == other.val

    def __ge__(self, other):
        """
        Greater-or-equal comparison.
        """
        return self.__cmp__(other) >= 0

    def __gt__(self, other):
        """
        Greater-than comparison.
        """
        return self.__cmp__(other) > 0

    def __le__(self, other):
        """
        Lesser-or-equal comparison.
        """
        return self.__cmp__(other) <= 0

    def __lt__(self, other):
        """
        Lesser-than comparison.
        """
        return self.__cmp__(other) < 0

    def __ne__(self, other):
        """
        Nonequality comparison.
        """
        return not self.__eq__(other)

    def __repr__(self):
        """
        String representation.
        """
        return repr(self.val)
