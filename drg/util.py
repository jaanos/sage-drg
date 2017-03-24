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

def factor(exp):
    """
    Factor an expression.
    """
    if isinstance(exp, Expression) and not exp.is_zero():
        return exp.factor()
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
        if isinstance(exp, IntegerFactorization):
            return exp + Integer(0)
        elif exp.is_integer():
            return Integer(exp)
    except:
        pass
    raise TypeError("Attempt to coerce non-integer to Integer")

def matrixMap(fun, M):
    """
    Replace each value in matrix ``M`` by its image under ``fun``.
    """
    for i in range(M.nrows()):
        M[i] = map(fun, M[i])

def variables(exp):
    """
    Return a list of variables in an expression.
    """
    if isinstance(exp, Expression):
        return exp.variables()
    else:
        return ()
