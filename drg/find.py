import operator
from sage.numerical.mip import MIPSolverException
from sage.numerical.mip import MixedIntegerLinearProgram
from sage.rings.infinity import Infinity
from sage.symbolic.relation import solve
from .util import is_constant
from .util import integralize
from .util import make_expressions
from .util import round
from .util import symbol
from .util import variables
from .util import verify


def find(expressions, vars, conditions=None, solver=None):
    """
    Generate assignments of values to variables
    such that the values of the expressions are integral
    and subject to the specified lower and upper bounds.

    Assumes that the expressions and conditions are linear in the variables.
    """
    expressions = dict(expressions)
    conditions = set() if conditions is None else set(conditions)
    vars = set(vars)
    for c in set(conditions):
        if verify(c):
            conditions.discard(c)
        elif verify(c.negation()):
            return
    if len(vars) > 0:
        _, opt = min((Infinity if None in (u, l) else u-l, e)
                     for e, (l, u) in expressions.items()
                     if not is_constant(e))
        _, x = min((abs(opt.coefficient(y)), y) for y in variables(opt))
        s = symbol("__opt")
        xsol = solve(s == opt, x)[0]
        rest = vars - {x}
        zero = [z == 0 for z in vars]
        lp = MixedIntegerLinearProgram(maximization=False,
                                       solver=solver)
        v = lp.new_variable(real=True)
        w = lp.new_variable(integer=True)
        lp.add_constraint(lp[1] == 1)

        def makeLPExpression(e):
            return sum(e.coefficient(y) * v[str(y)] for y in vars) \
                + e.subs(zero) * lp[1]

        lpopt = makeLPExpression(opt)

        def addCondition(c):
            op = c.operator()
            if op is operator.gt:
                op = operator.ge
            elif op is operator.lt:
                op = operator.le
            elif op not in [operator.eq, operator.ge, operator.le]:
                return
            lp.add_constraint(op(makeLPExpression(c.lhs()),
                                 makeLPExpression(c.rhs())))

    else:
        x = None
    delete = set()
    for i, (e, (l, u)) in enumerate(expressions.items()):
        if is_constant(e):
            try:
                integralize(e)
            except TypeError:
                return
            if e < l or e > u:
                return
            delete.add(e)
            continue
        elif x is None:
            return
        lp.add_constraint(w[i] == makeLPExpression(e))
        lp.set_min(w[i], l)
        lp.set_max(w[i], u)
    for e in delete:
        del expressions[e]
    if x is None:
        yield ()
        return
    for c in conditions:
        addCondition(c)
    lp.set_objective(-lpopt)
    try:
        vmax = round(-lp.solve())
    except MIPSolverException as ex:
        if len(ex.args) == 0 or 'feasible' in ex.args[0]:
            return
    lp.set_objective(lpopt)
    vnew = vmin = round(lp.solve())
    while vmin <= vmax:
        eq = xsol.subs(s == vmin)
        g = find(make_expressions((e.subs(eq), l, u)
                                  for e, (l, u) in expressions.items()),
                 vars=rest, conditions={c.subs(eq) for c in conditions})
        try:
            while vnew == vmin:
                sol = next(g)
                t = (yield (eq.subs(sol), ) + sol)
                while t is not None:
                    b, c = t
                    if b:
                        t = (yield find(expressions, vars=vars,
                                        conditions=conditions | {c}))
                    else:
                        if c in conditions or verify(c):
                            t = yield
                            continue
                        elif verify(c.negation()):
                            return
                        conditions.add(c)
                        addCondition(c)
                        lp.set_objective(-lpopt)
                        try:
                            vmax = round(-lp.solve())
                        except MIPSolverException:
                            return
                        lp.set_objective(lpopt)
                        vnew = round(lp.solve())
                        if vnew == vmin:
                            g.send((False, c.subs(eq)))
                        t = yield
            vmin = vnew
        except StopIteration:
            vmin += 1
            vnew = vmin
        finally:
            g.close()
