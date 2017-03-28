from sage.arith.misc import factor as factorize
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.functions.other import sqrt
from sage.rings.integer import Integer
from sage.rings.real_mpfr import create_RealNumber
from sage.structure.factorization_integer import IntegerFactorization
from sage.symbolic.expression import Expression

def checkNonneg(exp):
    """
    Check whether an expression can be nonnegative.

    Returns ``True`` if ``exp`` is an integer
    or an expression that is not always negative.
    Otherwise, returns ``False``.
    """
    return not (exp < 0)

def checkPos(exp):
    """
    Check whether an expression can be positive.

    Returns ``True`` if ``exp`` is an integer
    or an expression that is not always negative.
    Otherwise, returns ``False``.
    """
    return not (exp <= 0)

def _factor(exp):
    """
    Factor an expression.
    """
    if isinstance(exp, Expression) and not exp.is_zero():
        return exp.factor()
    return exp

def full_simplify(exp):
    """
    Fully simplify an expression.
    """
    if isinstance(exp, Expression):
        return exp.full_simplify()
    return exp

def integralize(exp):
    """
    Coerce an expression into an integer if possible,
    else return an error.

    Returns the corresponding integer if ``exp`` is integral.
    Returns ``exp`` if ``exp`` is an expression
    which is not known to be integral.
    Otherwise, an exception is raised.
    """
    if isinstance(exp, float):
        exp = create_RealNumber(exp)
    elif isinstance(exp, Expression) and not exp.is_constant():
        return exp
    try:
        if isinstance(exp, (int, IntegerFactorization)):
            return exp + Integer(0)
        elif exp.is_integer():
            return Integer(exp)
    except:
        pass
    raise TypeError("attempt to coerce non-integer to Integer")

def is_constant(x):
    """
    Determine whether an expression is constant.
    """
    return not isinstance(x, Expression) or x.is_constant()

def is_squareSum(x):
    """
    Determine whether an integer is a sum of two squares.
    """
    if x.is_prime():
        return x == 2 or x % 4 == 1
    i, j, y = -1, 0, x
    while j <= y:
        if sqrt(y).is_integer():
            return True
        i += 2
        j += i
        y -= i
    return False

def matrixMap(fun, M):
    """
    Replace each value in matrix ``M`` by its image under ``fun``.
    """
    for i in range(M.nrows()):
        M[i] = map(fun, M[i])

def rewriteExp(exp, expand = False, factor = False, simplify = False):
    """
    Rewrite an expression.
    """
    if expand:
        exp = _expand(exp)
    if factor:
        exp = _factor(exp)
    if simplify > 1:
        exp = full_simplify(exp)
    elif simplify:
        exp = _simplify(exp)
    return exp

def rewriteMatrix(M, expand = False, factor = False, simplify = False):
    """
    Rewrite a matrix.
    """
    if expand:
        matrixMap(_expand, M)
    if factor:
        matrixMap(_factor, M)
    if simplify > 1:
        matrixMap(full_simplify, M)
    elif simplify:
        matrixMap(_simplify, M)

def rewriteTuple(t, expand = False, factor = False, simplify = False):
    """
    Rewrite a tuple.
    """
    if expand:
        t = tuple(map(_expand, t))
    if factor:
        t = tuple(map(_factor, t))
    if simplify > 1:
        t = tuple(map(full_simplify, t))
    elif simplify:
        t = tuple(map(_simplify, t))
    return t

def variables(exp):
    """
    Return a list of variables in an expression.
    """
    if isinstance(exp, Expression):
        return exp.variables()
    else:
        return ()
