from sage.rings.integer import Integer
from sage.rings.real_mpfr import create_RealNumber
from sage.symbolic.expression import Expression

def checkNonneg(exp):
    """
    Check whether an expression can be nonnegative.

    Returns ``True'' if ``exp'' is an integer
    or an expression that is not always negative.
    Otherwise, returns ``False''.
    """
    return not (exp < 0)

def checkPos(exp):
    """
    Check whether an expression can be positive.

    Returns ``True'' if ``exp'' is an integer
    or an expression that is not always negative.
    Otherwise, returns ``False''.
    """
    return not (exp <= 0)

def factor(exp):
    """
    Factor an expression.
    """
    if isinstance(exp, Expression):
        return exp.factor()
    return exp

def integralize(exp):
    """
    Coerce an expression into an integer if possible,
    else return an error.

    Returns the corresponding integer if ``exp'' is integral.
    Returns ``exp'' if ``exp'' is an expression
    which is not known to be integral.
    Otherwise, an exception is raised.
    """
    if isinstance(exp, float):
        exp = create_RealNumber(exp)
    try:
        if exp.is_integer():
            return Integer(exp)
    except:
        pass
    if isinstance(exp, Expression):
        return exp
    raise TypeError("Attempt to coerce non-integer to Integer")
