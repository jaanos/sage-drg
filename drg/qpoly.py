from sage.functions.other import floor
from sage.rings.integer import Integer
from sage.rings.rational_field import Q as QQ
from sage.symbolic.ring import SR
from .array3d import Array3D
from .assoc_scheme import ASParameters
from .assoc_scheme import PolyASParameters
from .aux import InfeasibleError
from .util import checklist
from .util import checkNonneg
from .util import is_constant
from .util import pair_keep
from .util import pair_swap
from .util import subs

check_QPolyParameters = []
check = checklist(check_QPolyParameters, PolyASParameters._checklist)


class QPolyParameters(PolyASParameters):
    """
    A class for parameters of a Q-polynomial association scheme
    and checking their feasibility.
    """

    ANTIPODAL = "Q-antipodal fraction"
    ARRAY = "Krein array"
    BIPARTITE = "Q-bipartite quotient"
    DUAL_INTEGRAL = True
    DUAL_MATRIX = "P"
    DUAL_PARAMETER = "intersection number"
    DUAL_PARTS = "relations"
    DUAL_SIZES = "valencies"
    DUAL_SYMBOL = "p"
    MATRIX = "Q"
    METRIC = False
    OBJECT = "Q-polynomial association scheme"
    OBJECT_LATEX = "$Q$-polynomial association scheme"
    PARAMETER = "Krein parameter"
    PART = "eigenspace"
    PARTS = "eigenspaces"
    PART_SCHEME = "eigenspace-%s scheme"
    PTR = pair_swap
    QTR = pair_keep
    SIZE = "multiplicity"
    SIZES = "multiplicities"
    SYMBOL = "q"

    def __init__(self, b, c=None, order=None, complement=None):
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
        self._compute_imprimitivity()
        self._compute_complement(complement)
        if self._.antipodal:
            r = self._.r
            if not is_constant(r):
                r = 3
            self._.dismantled_schemes = [None] * r

    def _complement(self):
        """
        Return the parameters of the complement of a strongly regular graph.
        """
        return PolyASParameters._complement(self, self._.m, self._.q)

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
        Compute the valencies of the relations.
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

    def _derived(self, derived=True):
        """
        Generate parameters sets of derived association schemes.
        """
        if self._.antipodal and self._.d >= 3:
            self.all_dismantlements()
        yield from PolyASParameters._derived(self, derived)

    def _copy(self, p):
        """
        Copy fields to the given object.
        """
        PolyASParameters._copy(self, p)
        if self._has("dismantled_schemes"):
            p._.dismantled_schemes = self._.dismantled_schemes[:]

    def _copy_cosineSequences(self, p):
        """
        Obtain the cosine sequences from the dual eigenmatrix.
        """
        PolyASParameters._copy_cosineSequences(self, p.dualEigenmatrix())

    def _dismantle(self, r):
        """
        Return parameters for an r-part dismantlement
        of a Q-antipodal association scheme.
        """
        if r == self._.r:
            return self
        elif r == 1:
            return self.antipodalFraction()
        if self._.d == 1:
            scheme = QPolyParameters((r-1, ), (Integer(1), ))
        elif self._.d == 2:
            m = self._.m[1] * r / self._.r
            scheme = QPolyParameters((m, r-1), (Integer(1), m))
        else:
            m = floor(self._.d / 2)
            b, c = (list(t) for t in self.kreinArray())
            c[self._.d - m - 1] *= self._.r / r
            b[m] = (r-1) * c[self._.d - m - 1]
            scheme = QPolyParameters(b, c)
        r = min(len(scheme._.dismantled_schemes),
                len(self._.dismantled_schemes))
        scheme._.dismantled_schemes[:r] = self._.dismantled_schemes[:r]
        return scheme

    @classmethod
    def _dismantlement_name(cls, r):
        """
        Return a properly formatted name for the given dismantlement.
        """
        if r == 1:
            return cls.ANTIPODAL
        else:
            return "%d-part dismantlement" % r

    @staticmethod
    def _get_class():
        """
        Return the principal class of the object.
        """
        return QPolyParameters

    def _init_schoenberg(self):
        """
        Initialize parameters for the computation of the limit
        up to which Schönberg's theorem is tested.

        The case of Q-bipartite schemes is treated specially.
        """
        if self._.bipartite:
            return (self._.d - 1, 4 / self._.n)
        else:
            return PolyASParameters._init_schoenberg(self)

    def _is_trivial(self):
        """
        Check whether the Q-polynomial association scheme is trivial
        for the purposes of feasibility checking.

        Returns ``True`` if the scheme has one class
        or principal multiplicity two.
        """
        return PolyASParameters._is_trivial(self) or self._.m[1] == 2

    def _subs(self, exp, p, seen):
        """
        Substitute the given subexpressions in the parameters.
        """
        p, new = PolyASParameters._subs(self, exp, p, seen)
        if new:
            if self._has("p") and not p._has("p"):
                p._.p = self._.p.subs(*exp)
                p._check_parameters(p._.p, integral=self.DUAL_INTEGRAL,
                                    name=self.DUAL_PARAMETER,
                                    sym=self.DUAL_SYMBOL)
            if self._has("dismantled_schemes"):
                r = min(len(self._.dismantled_schemes),
                        len(p._.dismantled_schemes))
                for h, s in enumerate(self._.dismantled_schemes[:r]):
                    if s is None:
                        continue
                    name = self._dismantlement_name(h)
                    try:
                        p._.dismantled_schemes[h] = p.add_subscheme(
                            self._.dismantled_schemes[h].subs(*exp, seen=seen),
                            name)
                    except (InfeasibleError, AssertionError) as ex:
                        raise InfeasibleError(ex, part=name)
        return p

    def all_dismantlements(self):
        """
        Return a dictionary of parameters for all dismantled schemes.
        """
        assert self._.antipodal, "scheme is not Q-antipodal"
        return {r: self.dismantle(r) for r
                in range(2, len(self._.dismantled_schemes))}

    def dismantle(self, r):
        """
        Return parameters for an r-part dismantlement
        of a Q-antipodal association scheme.
        """
        assert self._.antipodal, "scheme is not Q-antipodal"
        assert r >= 1, "at least one part should be kept"
        if is_constant(r) and r < len(self._.dismantled_schemes):
            scheme = self._.dismantled_schemes[r]
            if scheme is None:
                scheme = self.add_subscheme(self._dismantle(r),
                                            self._dismantlement_name(r))
                self._.dismantled_schemes[r] = scheme
        else:
            scheme = self._dismantle(r)
        return scheme

    def eigenvalues(self, expand=False, factor=False, simplify=False):
        """
        Compute and return the dual eigenvalues of the first eigenspace
        of the Q-polynomial association scheme.
        """
        return self._compute_eigenvalues(self._.q, expand=expand,
                                         factor=factor, simplify=simplify)

    def merge(self, *args, **kargs):
        """
        Return parameters of a Q-polynomial association scheme obtained
        by merging specified eigenspaces.
        """
        return PolyASParameters.merge(self, self._.m, self._.q,
                                      *args, **kargs)

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

    def subconstituent(self, h, compute=False):
        """
        Return parameters of the h-th subconstituent
        if it is known to form an association scheme.

        If the resulting scheme is Q-polynomial,
        the parameters are returned as such.

        If ``compute`` is set to ``True``,
        then the relevant triple intersection numbers will be computed.
        """
        if self._.subconstituents[h] is None:
            subc, refs, rels = PolyASParameters.subconstituent(self, h,
                                                               compute=compute,
                                                               return_rels=True)
            if subc is not None and subc.is_qPolynomial():
                old, subc = subc, QPolyParameters(subc)
                self._.subconstituents[h] = (subc, refs)
                self.add_subscheme(subc, replace=old)
        else:
            subc, refs = self._.subconstituents[h]
        return subc

    def subs(self, *exp, **kargs):
        """
        Substitute the given subexpressions in the parameters.
        """
        return self._subs(exp, QPolyParameters(*[[subs(x, *exp) for x in l]
                                                 for l in self.kreinArray()]),
                          kargs.get("seen", {}))

    @check(1)
    def check_splittingField(self):
        """
        Verify that the splitting field of a Q-polynomial scheme
        with principal multiplicity more than 2
        is at most a degree 2 extension of the field of rational numbers.
        """
        if checkNonneg(2 - self._.m[1]):
            return
        if self._has("Q"):
            M = self._.Q
        elif self._has("P"):
            M = self._.P
        else:
            M = self.dualEigenmatrix()
        t = None
        for r in M[1:, 1:]:
            for v in r:
                if len(SR(v).variables()) > 0:
                    continue
                mp = v.minpoly()
                if mp.degree() == 1:
                    continue
                elif mp.degree() == 2:
                    if t is None:
                        t = QQ.extension(mp, 'a')['t'].gen()
                        continue
                    elif not mp(t).is_irreducible():
                        continue
                raise InfeasibleError("splitting field of Q-polynomial scheme"
                                      " with m[1] > 2 is more than degree 2"
                                      " extension of rationals",
                                      ["CerzoSuzuki09", "MartinWilliford09"])

    antipodalFraction = PolyASParameters.antipodalSubscheme
    bipartiteQuotient = PolyASParameters.bipartiteSubscheme
    kreinArray = PolyASParameters.parameterArray
