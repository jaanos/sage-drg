from sage.matrix.constructor import Matrix
from sage.rings.integer import Integer
from sage.symbolic.relation import solve as _solve
from sage.symbolic.ring import SR
from .array3d import Array3D
from .assoc_scheme import ASParameters
from .assoc_scheme import PolyASParameters
from .util import pair_keep
from .util import pair_swap
from .util import subs


class QPolyParameters(PolyASParameters):
    """
    A class for parameters of a Q-polynomial association scheme
    and checking their feasibility.
    """

    ARRAY = "Krein array"
    DUAL_INTEGRAL = True
    DUAL_PARAMETER = "intersection number"
    DUAL_PARTS = "subconstituents"
    DUAL_SYMBOL = "p"
    OBJECT = "Q-polynomial association scheme"
    PARAMETER = "Krein parameter"
    PART = "eigenspace"
    PARTS = "multiplicities"
    SYMBOL = "q"
    PTR = pair_swap
    QTR = pair_keep

    def __init__(self, b, c=None, order=None):
        """
        Object constructor.

        Takes two iterables of the same length ``d`` as input,
        representing the Krein array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}``.
        The basic checks on nonnegativity
        of the Krein array are performed.
        """
        self._init_storage()
        if isinstance(b, ASParameters):
            o = b.is_qPolynomial()
            assert o, "scheme not Q-polynomial"
            self._.d = b._.d
            if order is None:
                order = o[0]
            else:
                order = self._reorder(order)
            assert order in o, "scheme not Q-polynomial for given order"
            PolyASParameters.__init__(self, b, order=order)
            if isinstance(b, QPolyParameters):
                return
        else:
            self._.d = Integer(len(b))
            PolyASParameters.__init__(self, b, c)
            self._.m = tuple(self._init_multiplicities())
            self._.q = Array3D(self._.d + 1)
            self._compute_parameters(self._.q, self._.m)
        self._.bipartite = all(a == 0 for a in self._.a)

    def _compute_kreinParameters(self, expand=False, factor=False,
                                 simplify=False):
        """
        Compute the Krein parameters.

        Does nothing, as they are already computed
        for Q-polynomial association schemes,
        """
        pass

    def _compute_kTable(self, expand=False, factor=False, simplify=False):
        """
        Compute the sizes of the subconstituents.
        """
        if not self._has("k"):
            self._.k = self._compute_sizes(self._.m, expand=expand,
                                           factor=factor, simplify=simplify)

    def _compute_multiplicities(self, expand=False, factor=False,
                                simplify=False):
        """
        Compute the multiplicities of the eigenspaces.

        Does nothing, as they are already computed
        for Q-polynomial association schemes,
        """
        pass

    def _compute_pTable(self, expand=False, factor=False, simplify=False):
        """
        Compute the intersection numbers.
        """
        if not self._has("k"):
            self.kTable(expand=expand, factor=factor, simplify=simplify)
        if not self._has("p"):
            p = Array3D(self._.d + 1)
            self._compute_dualParameters(p, self._.m, self._.k, self.QTR)
            self._.p = p
            self.check_handshake()

    def _copy(self, p):
        """
        Copy fields to the given obejct.
        """
        PolyASParameters._copy(self, p)
        if isinstance(p, QPolyParameters):
            p._.bipartite = self._.bipartite

    def _copy_cosineSequences(self, p):
        """
        Obtain the cosine sequences from the dual eigenmatrix.
        """
        PolyASParameters._copy_cosineSequences(self, p.dualEigenmatrix())

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return QPolyParameters

    def eigenvalues(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the dual eigenvalues of the first eigenspace
        of the Q-polynomial association scheme.
        """
        return self._compute_eigenvalues(self._.q, expand=expand,
                                         factor=factor, simplify=simplify)

    def reorderEigenspaces(self, *order):
        """
        Specify a new order for the eigenspaces.
        """
        self.reorderParameters(*order)

    def reorderEigenvalues(self, *order):
        """
        Specify a new order for the eigenvalues and return it.
        """
        order = PolyASParameters.reorderEigenvalues(self, *order)
        PolyASParameters.reorderRelations(self, *order)
        return self._.theta

    def reorderParameters(self, *order):
        """
        Specify a new order for the parameters and return them.
        """
        order = self._reorder(order)
        assert order in self.is_qPolynomial(), \
            "scheme not Q-polynomial for the given order"
        PolyASParameters.reorderEigenspaces(self, *order)
        PolyASParameters.reorderParameters(self, self._.q, *order)
        return self.parameterArray()

    def reorderRelations(self, *order):
        """
        Specify a new order for the relations.
        """
        self.reorderEigenvalues(*order)

    def subs(self, *exp):
        """
        Substitute the given subexpressions in the parameters.
        """
        p = QPolyParameters(*[[subs(x, *exp) for x in l]
                              for l in self.kreinArray()])
        self._subs(exp, p)
        if self._has("p"):
            p._.p = self._.p.subs(*exp)
            p._check_parameters(p._.p, integral=self.DUAL_INTEGRAL,
                                name=self.DUAL_PARAMETER,
                                sym=self.DUAL_SYMBOL)
        return p

    kreinArray = PolyASParameters.parameterArray
