from sage.rings.integer import Integer
from .array3d import Array3D
from .assoc_scheme import PolyASParameters

class QPolyParameters(PolyASParameters):
    """
    A class for parameters of a Q-polynomial association scheme
    and checking their feasibility.
    """

    ARRAY = "Krein array"
    OBJECT = "Q-polynomial association scheme"
    PARAMETER = "Krein parameter"
    PARAMETER_SYMBOL = "q"
    PARTS = "multiplicities"

    def __init__(self, b, c):
        """
        Object constructor.

        Takes two iterables of the same length ``d`` as input,
        representing the Krein array
        ``{b[0], b[1], ..., b[d-1]; c[1], c[2], ..., c[d]}``.
        The basic checks on nonnegativity
        of the Krein array are performed.
        """
        self.d = Integer(len(b))
        PolyASParameters.__init__(self, b, c)
        self.bipartite = all(a == 0 for a in self.a)
        self.m = tuple(self._init_multiplicities())
        self.q = Array3D(self.d + 1)
        self._compute_parameters(self.q, self.m)

    kreinArray = PolyASParameters.parameterArray
