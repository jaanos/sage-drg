from warnings import warn
from sage.calculus.functional import expand as _expand
from sage.calculus.functional import simplify as _simplify
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import identity_matrix
from sage.rings.integer import Integer
from sage.symbolic.ring import SR
from .coefflist import CoefficientList
from .util import checkNonneg
from .util import checkPos
from .util import _factor
from .util import full_simplify
from .util import integralize
from .util import rewriteExp
from .util import rewriteMatrix
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

    def _check_eigenmatrices(self):
        if "P" in self.__dict__ and "Q" in self.__dict__ and \
                _simplify(_expand(self.P * self.Q)) \
                    != self.order(expand = True, simplify = True) \
                        * identity_matrix(SR, self.d + 1):
            warn(Warning("the eigenmatrices do not multiply "
                         "into a multiple of the identity matrix"))

    @staticmethod
    def _check_parameter(h, i, j, v, integral = False,
                         name = None, sym = None):
        """
        Check for the feasibility
        of an intersection number or Krein parameter.

        The parameter is checked for nonnegativity,
        and, if requested, also for integrality.
        """
        if integral:
            try:
                v = integralize(v)
            except TypeError:
                raise InfeasibleError("%s %s[%d, %d, %d] is nonintegral"
                                       % (name, sym, h, i, j))
        assert checkNonneg(v), \
            "%s %s[%d, %d, %d] is negative" % (name, sym, h, i, j)
        return v

    def _check_parameters(self, p, integral = False, name = None, sym = None):
        """
        Check for the feasibility
        of all intersection numbers or Krein parameters.

        The parameters are checked for nonnegativity,
        and, if requested, also for integrality.
        """
        for h in range(self.d + 1):
            for i in range(self.d + 1):
                for j in range(self.d + 1):
                    p[h, i, j] = ASParameters. \
                        _check_parameter(h, i, j, p[h, i, j],
                                         integral = integral,
                                         name = name, sym = sym)

    def _compute_dualEigenmatrix(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        # TODO
        pass

    def _compute_eigenmatrix(self, p, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return an eigenmatrix of the association scheme.
        """
        # TODO
        B = [Matrix(SR, [M[i] for M in p]) for i in range(self.d + 1)]

    def _compute_kreinParameters(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the Krein parameters.
        """
        # TODO
        pass

    def _compute_kTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the sizes of the subconstituents.
        """
        # TODO
        pass

    def _compute_multiplicities(self, expand = False, factor = False,
                                simplify = False):
        """
        Compute the multiplicities of the eigenspaces.
        """
        # TODO
        pass

    def _compute_primalEigenmatrix(self, expand = False, factor = False,
                                   simplify = False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        # TODO
        pass

    def _compute_pTable(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute the intersection numbers.
        """
        # TODO
        pass

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return ASParameters

    def _init_vars(self):
        """
        Initialize the list of variables.
        """
        # TODO: obtain variables if not yet available
        self.vars_ordered = len(self.vars) <= 1

    def classes(self):
        """
        Return the number of classes of the association scheme.
        """
        return self.d

    def dualEigenmatrix(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute and return the dual eigenmatrix of the association scheme.
        """
        self._compute_dualEigenmatrix(expand = expand, factor = factor,
                                      simplify = simplify)
        self._check_eigenmatrices()
        rewriteMatrix(self.Q, expand = expand, factor = factor,
                      simplify = simplify)
        return Matrix(SR, self.Q)

    def eigenmatrix(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the eigenmatrix of the association scheme.
        """
        self._compute_primalEigenmatrix(expand = expand, factor = factor,
                                        simplify = simplify)
        self._check_eigenmatrices()
        rewriteMatrix(self.P, expand = expand, factor = factor,
                      simplify = simplify)
        return Matrix(SR, self.P)

    def is_formallySelfDual(self):
        """
        Check whether the association scheme is formally self-dual.
        """
        if "fsd" not in self.__dict__:
            self.fsd = (self.eigenmatrix(simplify = 2)
                        - self.dualEigenmatrix(simplify = 2)).is_zero()
        return self.fsd

    def kreinParameters(self, expand = False, factor = False,
                        simplify = False):
        """
        Compute and return the Krein parameters.
        """
        self._compute_kreinParameters(expand = expand, factor = factor,
                                      simplify = simplify)
        self.q.rewrite(expand = expand, factor = factor, simplify = simplify)
        return self.q

    def kTable(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the sizes of the subconstituents
        """
        self._compute_kTable(expand = expand, factor = factor,
                             simplify = simplify)
        self.k = rewriteTuple(self.k, expand = expand, factor = factor,
                              simplify = simplify)
        return self.k

    def multiplicities(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the multiplicities of the eigenspaces.
        """
        self._compute_multiplicities(expand = expand, factor = factor,
                                     simplify = simplify)
        self.m = rewriteTuple(self.m, expand = expand, factor = factor,
                              simplify = simplify)
        return self.m

    def pTable(self, expand = False, factor = False, simplify = False):
        """
        Compute and return the intersection numbers.
        """
        self._compute_pTable(expand = expand, factor = factor,
                             simplify = simplify)
        self.p.rewrite(expand = expand, factor = factor, simplify = simplify)
        return self.p

    def variables(self):
        """
        Return the variables in the graph parameters.
        """
        return self.vars

    order = __len__


class PolyASParameters(ASParameters):
    ARRAY = None
    DUAL_INTEGRAL = None
    DUAL_PARAMETER = None
    DUAL_PARTS = None
    DUAL_SYMBOL = None
    OBJECT = None
    PARAMETER = None
    PARTS = None
    PTR = None
    QTR = None
    SYMBOL = None

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

    def __eq__(self, other):
        """
        Compare self to other.
        """
        ia = self.parameterArray()
        if isinstance(other, self._get_class()):
            return ia == other.parameterArray()
        else:
            return not isinstance(other, ASParameters) and ia == other

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash((self.SYMBOL, self.parameterArray()))

    def __repr__(self):
        """
        String representation.
        """
        return "Parameters of a %s with %s %s" % (self.OBJECT, self.ARRAY,
                                                self.format_parameterArray())

    def _check_multiplicity(self, k, i):
        """
        Check for the feasibility of the i-th multiplicity.

        By default, no checks are performed.
        """
        pass

    def _check_parameter(self, h, i, j, v, integral = False,
                         name = None, sym = None):
        """
        Check for the feasibility
        of an intersection number or Krein parameter.

        The parameter is checked for nonnegativity,
        and, if requested, also for integrality.
        """
        if name is None:
            name = self.PARAMETER
        if sym is None:
            sym = self.SYMBOL
        return ASParameters._check_parameter(h, i, j, v, integral = integral,
                                             name = name, sym = sym)

    def _compute_cosineSequences(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the cosine sequences of the association scheme.
        """
        if "theta" not in self.__dict__:
            self.eigenvalues(expand = expand, factor = factor,
                             simplify = simplify)
        if "omega" not in self.__dict__:
            self.omega = Matrix(SR, self.d + 1)
            self.omega[:, 0] = 1
            for i in range(self.d + 1):
                self.omega[i, 1] = self.theta[i]/self.b[0]
                for j in range(2, self.d + 1):
                    self.omega[i, j] = _simplify(_factor((
                        (self.theta[i] - self.a[j-1]) * self.omega[i, j-1]
                        - self.c[j-1] * self.omega[i, j-2]) / self.b[j-1]))

    def _compute_dualEigenmatrix(self, expand = False, factor = False,
                                 simplify = False):
        """
        Compute the dual eigenmatrix of the association scheme.
        """
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self.Q = self._compute_eigenmatrix(self.multiplicities(*params),
                                           self.QTR, *params)

    def _compute_dualParameters(self, q, k, m, tr, n = 1):
        """
        Compute the Krein parameters or intersection numbers
        from the cosine sequences.
        """
        for h in range(self.d + 1):
            for i in range(self.d + 1):
                for j in range(self.d + 1):
                    q[h, i, j] = full_simplify(
                                    sum(k[t] * self.omega[tr(h, t)]
                                             * self.omega[tr(i, t)]
                                             * self.omega[tr(j, t)]
                                        for t in range(self.d + 1))
                                    * m[i] * m[j] / self.n)
                    self._check_parameter(h, i, j, q[h, i, j],
                                          integral = self.DUAL_INTEGRAL,
                                          name = self.DUAL_PARAMETER,
                                          sym = self.DUAL_SYMBOL)

    def _compute_eigenmatrix(self, k, tr, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return the eigenmatrix of the association scheme.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        return Matrix(SR, [[self.omega[tr(i, j)] * k[j]
                            for j in range(self.d + 1)]
                           for i in range(self.d + 1)])

    def _compute_eigenvalues(self, p, expand = False, factor = False,
                             simplify = False):
        """
        Compute and return the eigenvalues of the association scheme.
        """
        if "theta" not in self.__dict__:
            if self.is_cyclic():
                self.theta = tuple(2*cos(2*i*pi/self.n)
                                   for i in range(self.d + 1))
            else:
                B = Matrix(SR, [M[1] for M in p])
                self.theta = B.eigenvalues()
                try:
                    self.theta.sort(
                        key = lambda x: CoefficientList(x, self.vars),
                        reverse = True)
                except:
                    warn(Warning("Sorting of eigenvalues failed - "
                                 "you may want to sort them manually"))
                else:
                    if not self.vars_ordered:
                        warn(Warning("More than one variable is used - "
                                     "please check that the ordering "
                                     "of the eigenvalues is correct"))
                self.theta = tuple(self.theta)
        self.theta = rewriteTuple(self.theta, expand = expand,
                                  factor = factor, simplify = simplify)
        return self.theta

    def _compute_parameters(self, p, k):
        """
        Compute the intersection numbers or Krein parameters
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

    def _compute_primalEigenmatrix(self, expand = False, factor = False,
                                   simplify = False):
        """
        Compute the primal eigenmatrix of the association scheme.
        """
        params = {"expand": expand, "factor": factor, "simplify": simplify}
        self.P = self._compute_eigenmatrix(self.kTable(*params),
                                           self.PTR, *params)

    def _compute_sizes(self, k, expand = False, factor = False,
                       simplify = False):
        """
        Compute multiplicities of the eigenspaces
        or sizes of the subconstituents.
        """
        if "omega" not in self.__dict__:
            self.cosineSequences(expand = expand, factor = factor,
                                 simplify = simplify)
        if self.is_cyclic():
            m = tuple(Integer(1 if th in [2, -2] else 2)
                      for th in self.theta)
        else:
            try:
                m = tuple(integralize(_simplify(_factor(
                                        self.n / sum(s * om**2 for s, om
                                                in zip(k, omg)))))
                               for omg in self.omega)
            except TypeError:
                raise InfeasibleError("%s not integral" % self.DUAL_PARTS)
        return m

    def _init_array(self, b, c):
        """
        Initialize the intersection or Krein array.
        """
        self.c = (Integer(0), ) + tuple(c)
        self.b = tuple(b) + (Integer(0), )

    def _init_multiplicities(self):
        """
        Compute the sizes of subconstituents
        or multiplicities of the eigenvalues
        from the intersection or Krein array.
        """
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

    def cosineSequences(self, index = None, ev = None, expand = False,
                        factor = False, simplify = False):
        """
        Compute and return the cosine sequences
        for each subconstituent and eigenspace.
        """
        self._compute_cosineSequences(expand = expand, factor = factor,
                                      simplify = simplify)
        rewriteMatrix(self.omega, expand = expand, factor = factor,
                      simplify = simplify)
        if ev is not None:
            try:
                index = self.theta.index(ev)
            except ValueError as ex:
                if index is None:
                    raise ex
        if index is not None:
            return self.omega[index]
        return Matrix(SR, self.omega)

    def format_parameterArray(self):
        """
        Return a string representation of the intersection array.
        """
        return "{%s; %s}" % tuple(', '.join(str(x) for x in l)
                                  for l in self.parameterArray())

    def is_cyclic(self):
        """
        Check whether the association scheme is cyclic.
        """
        return self.b[0] == 2 and self.c[-1] in [1, 2] and \
            all(x == 1 for x in self.b[1:] + self.c[:-1])

    def parameterArray(self, expand = False, factor = False,
                       simplify = False):
        """
        Return the intersection or Krein array of the association scheme
        as a tuple of two tuples.
        """
        return (self.bTable(expand = expand, factor = factor,
                            simplify = simplify),
                self.cTable(expand = expand, factor = factor,
                            simplify = simplify))
