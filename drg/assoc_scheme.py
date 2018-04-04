from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.rings.integer import Integer
from .util import checkNonneg
from .util import checkPos
from .util import full_simplify
from .util import integralize
from .util import rewriteExp
from .util import rewriteTuple
from .util import variables

class InfeasibleError(Exception):
    """
    Infeasibility of a parameter set.
    """

    def __init__(self, reason = None, refs = None, part = None):
        """
        Exception constructor.
        """
        part = () if part is None else (part, )
        if isinstance(reason, InfeasibleError):
            self.reason = reason.reason
            self.refs = reason.refs
            self.part = reason.part + part
        elif isinstance(reason, Exception):
            self.reason = ", ".join(str(x) for x in reason.args)
            self.refs = []
            self.part = part
        else:
            self.reason = reason
            if refs is None:
                refs = []
            elif not isinstance(refs, list):
                refs = [refs]
            self.refs = [ref if isinstance(ref, tuple) else (ref, None)
                         for ref in refs]
            self.part = part
        msg = []
        if len(self.part) > 0:
            msg.append(" of ".join(self.part))
        if self.reason is not None:
            msg.append(self.reason)
        if len(self.refs) > 0:
            msg.append("nonexistence by %s" %
                       "; ".join(self.formatRef(ref) for ref in self.refs))
        msg = ": ".join(msg)
        if isinstance(msg, unicode):
            msg = msg.encode("utf-8")
        self.args = (msg, )

    @staticmethod
    def formatRef(ref):
        """
        Format reason for nonexistence.
        """
        pap, thm = ref
        if thm is None:
            return pap
        else:
            return "%s, %s" % (pap, thm)

class ASParameters:
    d = None
    vars = None

    def __init__(self, p = None, q = None):
        """
        Object constructor.
        """
        # TODO: initialize from p or q array
        self._init_vars()
        self.prefix = "v%x" % (hash(self) % Integer(2)**32)
        self.triple = {}

    def __len__(self, expand = False, factor = False, simplify = False):
        """
        Return the number of vertices.
        """
        self.n = rewriteExp(self.n, expand = expand, factor = factor,
                            simplify = simplify)
        return self.n

    def _init_vars(self):
        """
        Initialize the list of variables.
        """
        # TODO: obtain variables if not yet available
        self.vars_ordered = len(self.vars) <= 1

    def diameter(self):
        """
        Return the diameter (number of classes) of the association scheme.
        """
        return self.d

    def variables(self):
        """
        Return the variables in the graph parameters.
        """
        return self.vars

    order = __len__


class PolyASParameters(ASParameters):
    PARAMETER = None
    PARAMETER_SYMBOL = None
    PARTS = None

    def __init__(self, b, c):
        """
        Object constructor.

        Check the basic properties of the intersection or Krein array.
        """
        if self.d is None:
            raise NotImplementedError("PolyASParameters can not be "
                                      "instantiated directly")
        assert self.d == len(c) == len(b), "parameter length mismatch"
        self._init_array(b, c)
        assert all(checkPos(x) for x in self.c[1:]), \
            "c sequence not positive"
        assert all(checkPos(x) for x in self.b[:-1]), \
            "b sequence not positive"
        self.a = tuple(full_simplify(b[0]-x-y)
                       for x, y in zip(self.b, self.c))
        assert self.c[1] == 1, "Invalid c[1] value"
        assert all(checkNonneg(x) for x in self.a), \
            "a values negative"
        self.vars = tuple(set(sum(map(variables, tuple(b) + tuple(c)), ())))
        ASParameters.__init__(self)

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash((self.PARAMETER_SYMBOL, self.intersectionArray()))

    def _check_multiplicity(self, k, i):
        """
        Check for the feasibility of the i-th multiplicity.

        By default, no checks are performed.
        """
        pass

    def _check_parameter(self, h, i, j, v):
        """
        Check for the feasibility
        of an intersection number of Krein parameter.

        The parameter is checked for nonnegativity.
        """
        assert checkNonneg(v), "%s %s[%d, %d, %d] is negative" % \
                               (self.PARAMETER, self.PARAMETER_SYMBOL,
                                h, i, j)
        return v

    def _compute_parameters(self, p, k):
        """
        Compute intersection numbers or Krein parameters
        from the intersection or Krein array.
        """
        for i in range(self.d + 1):
            p[0, i, i] = k[i]
            p[i, 0, i] = Integer(1)
            p[i, i, 0] = Integer(1)
        for i in range(self.d):
            p[i+1, 1, i+1] = self.a[i+1]
            p[i, 1, i+1] = self.b[i]
            p[i+1, 1, i] = self.c[i+1]
        for i in range(2, self.d + 1):
            for j in range(1, self.d + 1):
                for h in range(1, self.d):
                    p[h, i, j] = self._check_parameter(h, i, j,
                        _simplify(_expand(
                            ( self.c[h] * p[h-1, i-1, j]
                            + self.b[h] * p[h+1, i-1, j]
                            - self.b[i-2] * p[h, i-2, j]
                            + (self.a[h] - self.a[i-1]) * p[h, i-1, j]
                            ) / self.c[i])))
                p[self.d, i, j] = self._check_parameter(h, i, j,
                    _simplify(_expand(
                        ( self.c[self.d] * p[self.d-1, i-1, j]
                        - self.b[i-2] * p[self.d, i-2, j]
                        + (self.a[self.d] - self.a[i-1])
                            * p[self.d, i-1, j]
                        ) / self.c[i])))

    def _init_array(self, b, c):
        """
        Initialize the intersection or Krein array.
        """
        self.c = c
        self.b = b

    def _init_multiplicities(self):
        k = [Integer(1)]
        try:
            for i in range(self.d):
                k.append(integralize(k[-1]*self.b[i]/self.c[i+1]))
                self._check_multiplicity(k, i)
        except TypeError:
            raise InfeasibleError("%s not integral" % self.PARTS)
        self.n = sum(k)
        return k

    def aTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of parameters ``a[1], a[2], ..., a[d]``,
        where ``d`` is the number of classes of the association scheme.
        """
        self.a = rewriteTuple(self.a, expand = expand, factor = factor,
                              simplify = simplify)
        return self.a[1:]

    def bTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of parameters ``b[0], b[1], ..., b[d-1]``,
        where ``d`` is the number of classes of the association scheme.
        """
        self.b = rewriteTuple(self.b, expand = expand, factor = factor,
                              simplify = simplify)
        return self.b[:-1]

    def cTable(self, expand = False, factor = False, simplify = False):
        """
        Return the table of parameters ``c[1], c[2], ..., c[d]``,
        where ``d`` is the number of classes of the association scheme.
        """
        self.c = rewriteTuple(self.c, expand = expand, factor = factor,
                              simplify = simplify)
        return self.c[1:]
