from sage.rings.integer import Integer
from sage.symbolic.expression import Expression

def checkNonneg(exp):
    """
    Check whether an expression can be nonnegative.

    Returns ``True'' if ``exp'' is an integer
    or an expression that is not always negative.
    Otherwise, returns ``False''.
    """
    return not (exp < 0)

def checkInteger(exp):
    """
    Check whether an expression can be integral.

    Returns ``True'' if ``exp'' is an integer or an expression,
    and ``False'' otherwise.
    """
    return isinstance(exp, (Integer, int, Expression))
