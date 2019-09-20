import operator
from types import InstanceType
from sage.misc.latex import latex
from sage.misc.latex import LatexExpr
from sage.structure.sage_object import SageObject
from sage.typeset.ascii_art import ascii_art
from sage.typeset.symbols import ascii_left_parenthesis
from sage.typeset.symbols import ascii_right_parenthesis
from sage.typeset.symbols import unicode_left_parenthesis
from sage.typeset.symbols import unicode_right_parenthesis
from sage.typeset.unicode_art import unicode_art


def attr(fun, nonex=None):
    """
    Decorator for providing values to the view methods.
    """
    def decorated(self, *args, **kargs):
        try:
            val = getattribute(self, 'fetch')()
        except getattribute(self, 'exception') as ex:
            if nonex is not None:
                return nonex(self)
            raise ex
        return fun(val, *args, **kargs)
    if isinstance(fun, InstanceType):
        decorated.__name__ = fun.__class__.__name__
    else:
        decorated.__name__ = fun.__name__
    decorated.__doc__ = fun.__doc__
    decorated.__module__ = fun.__module__
    return decorated


def fetch(pars, fun):
    """
    Fetch a parameter from a parameter set, computing it first if necessary.
    """
    if not pars._has(fun.__name__):
        fun(pars)
    return pars._.__getattribute__(fun.__name__)


getattribute = SageObject.__getattribute__
setattribute = SageObject.__setattr__
getitem = attr(operator.getitem)

RICH_REPR = ('_ascii_art_', '_unicode_art_', '_latex_')


class View(SageObject):
    """
    Abstract class for parameter views.
    """

    def __init__(self):
        """
        Object constructor.

        The class is abstract and cannot be instantiated directly.
        """
        raise NotImplementedError("View can not be instantiated directly")

    def __getattribute__(self, name):
        """
        Get a named attribute from an object.
        """
        if name in RICH_REPR:
            return getattribute(self, name)
        try:
            val = getattribute(self, 'fetch')()
        except getattribute(self, 'exception') as ex:
            if name == '__class__':
                return None
            raise ex
        return getattr(val, name)

    def __getitem__(self, key):
        """
        Return a view for the value indexed by ``key``.
        """
        getitem(self, key)
        return KeyView(self, key)

    @attr
    def __call__(val, *args, **kargs):
        """
        Call the object.
        """
        return val(*args, **kargs)

    @attr
    def __radd__(val, other):
        """
        ``other + val``
        """
        return val.__radd__(other)

    @attr
    def __rsub__(val, other):
        """
        ``other - val``
        """
        return val.__rsub__(other)

    @attr
    def __rmul__(val, other):
        """
        ``other * val``
        """
        return val.__rmul__(other)

    @attr
    def __rdiv__(val, other):
        """
        ``other / val`` (``__future__.division`` not in effect)
        """
        return val.__rdiv__(other)

    @attr
    def __rtruediv__(val, other):
        """
        ``other / val`` (``__future__.division`` in effect)
        """
        return val.__rtruediv__(other)

    @attr
    def __rfloordiv__(val, other):
        """
        ``other // val``
        """
        return val.__rfloordiv__(other)

    @attr
    def __rmod__(val, other):
        """
        ``other % val``
        """
        return val.__rmod__(other)

    @attr
    def __rdivmod__(val, other):
        """
        ``divmod(other, val)``
        """
        return val.__rdivmod__(other)

    @attr
    def __rpow__(val, other):
        """
        ``other ** val``
        """
        return val.__rpow__(other)

    @attr
    def __rlshift__(val, other):
        """
        ``other << val``
        """
        return val.__rlshift__(other)

    @attr
    def __rrshift__(val, other):
        """
        ``other >> val``
        """
        return val.__rrshift__(other)

    @attr
    def __rand__(val, other):
        """
        ``other & val``
        """
        return val.__rand__(other)

    @attr
    def __rxor__(val, other):
        """
        ``other ^^ val``
        """
        return val.__rxor__(other)

    @attr
    def __ror__(val, other):
        """
        ``other | val``
        """
        return val.__ror__(other)

    def ascii_art_nonex(self):
        """
        ASCII art representation in case of nonexistent parameter.
        """
        part, key, obj = getattribute(self, 'nonex')()
        art = ascii_art(" ", obj, " ")
        return ascii_art("View of nonexistent %s " % part, key, " of ",
                         ascii_left_parenthesis.character_art(art.height())
                         + art +
                         ascii_right_parenthesis.character_art(art.height()))

    def latex_nonex(self):
        """
        LaTeX representation in case of nonexistent parameter.
        """
        part, key, obj = getattribute(self, 'nonex')()
        return LatexExpr(r"\text{View of nonexistent %s }%s"
                         r"\text{ of }\left\langle%s\right\rangle" %
                         (part, latex(key), latex(obj)))

    def repr_nonex(self):
        """
        String representation in case of nonexistent parameter.
        """
        return "View of nonexistent %s %s of <%s>" % \
            getattribute(self, 'nonex')()

    def unicode_art_nonex(self):
        """
        Unicode art representation in case of nonexistent parameter.
        """
        part, key, obj = getattribute(self, 'nonex')()
        art = unicode_art(" ", obj, " ")
        return unicode_art("View of nonexistent %s " % part, key, " of ",
                           unicode_left_parenthesis.character_art(
                            art.height())
                           + art +
                           unicode_right_parenthesis.character_art(
                            art.height()))

    __repr__ = attr(repr, repr_nonex)
    __str__ = attr(str)
    __lt__ = attr(operator.lt)
    __le__ = attr(operator.le)
    __eq__ = attr(operator.eq)
    __ne__ = attr(operator.ne)
    __gt__ = attr(operator.gt)
    __ge__ = attr(operator.ge)
    __cmp__ = attr(cmp)
    __hash__ = attr(hash)
    __nonzero__ = attr(bool)
    __unicode__ = attr(unicode)
    __setattr__ = attr(setattr)
    __delattr__ = attr(delattr)
    __instancecheck__ = attr(isinstance)
    __subclasscheck__ = attr(issubclass)
    __len__ = attr(len)
    __setitem__ = attr(operator.setitem)
    __delitem__ = attr(operator.delitem)
    __iter__ = attr(iter)
    __reversed__ = attr(reversed)
    __contains__ = attr(operator.contains)
    __add__ = attr(operator.add)
    __sub__ = attr(operator.sub)
    __mul__ = attr(operator.mul)
    __floordiv__ = attr(operator.floordiv)
    __mod__ = attr(operator.mod)
    __divmod__ = attr(divmod)
    __pow__ = attr(pow)
    __lshift__ = attr(operator.lshift)
    __rshift__ = attr(operator.rshift)
    __and__ = attr(operator.and_)
    __xor__ = attr(operator.xor)
    __or__ = attr(operator.or_)
    __div__ = attr(operator.div)
    __truediv__ = attr(operator.truediv)
    __add__ = attr(operator.iadd)
    __sub__ = attr(operator.isub)
    __mul__ = attr(operator.imul)
    __div__ = attr(operator.idiv)
    __truediv__ = attr(operator.itruediv)
    __floordiv__ = attr(operator.ifloordiv)
    __mod__ = attr(operator.imod)
    __pow__ = attr(operator.ipow)
    __lshift__ = attr(operator.ilshift)
    __rshift__ = attr(operator.irshift)
    __and__ = attr(operator.iand)
    __xor__ = attr(operator.ixor)
    __or__ = attr(operator.ior)
    __neg__ = attr(operator.neg)
    __pos__ = attr(operator.pos)
    __abs__ = attr(abs)
    __invert__ = attr(operator.invert)
    __complex__ = attr(complex)
    __int__ = attr(int)
    __long__ = attr(long)
    __float__ = attr(float)
    __oct__ = attr(oct)
    __hex__ = attr(hex)
    __index__ = attr(operator.index)
    __coerce__ = attr(coerce)
    _ascii_art_ = attr(ascii_art, ascii_art_nonex)
    _latex_ = attr(latex, latex_nonex)
    _unicode_art_ = attr(unicode_art, unicode_art_nonex)


class AttrView(View):
    """
    Class for views of parameters as attributes of ``aux.Parameters``.
    """

    exception = AttributeError

    def __init__(self, pars, fun):
        """
        Object constructor.
        """
        setattribute(self, 'pars', pars)
        setattribute(self, 'fun', fun)
        setattribute(self, 'fetch', lambda: fetch(pars, fun))

    def nonex(self):
        """
        Data for the representation in case of nonexistent attribute.
        """
        pars = getattribute(self, 'pars')
        fun = getattribute(self, 'fun')
        return LatexExpr("attribute", fun.__name__, pars)


class KeyView(View):
    """
    Class for views of parameters derived by indexing.
    """

    exception = IndexError

    def __init__(self, view, key):
        """
        Object constructor.
        """
        setattribute(self, 'view', view)
        setattribute(self, 'key', key)
        setattribute(self, 'fetch', lambda: getitem(view, key))

    def nonex(self):
        """
        Data for the representation in case of nonexistent attribute.
        """
        view = getattribute(self, 'view')
        key = getattribute(self, 'key')
        return ("key", key, view)


class Param(object):
    """
    Descriptor class for read-only parameters.
    """

    def __init__(self, fun):
        """
        Object constructor.
        """
        self.fun = fun

    def __get__(self, instance, owner):
        """
        Getter method.
        """
        assert instance is not None, "parameter cannot be fetched from class"
        fetch(instance, self.fun)
        return AttrView(instance, self.fun)

    def __set__(self, instance, value):
        """
        Setter method.

        Prevents changing the attribute.
        """
        raise AttributeError("parameter is read-only")

    def __delete__(self, instance):
        """
        Deleter method.

        Prevents deleting the attribute.
        """
        raise AttributeError("parameter is read-only")
