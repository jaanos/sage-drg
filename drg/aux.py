from .references import refs as references


class InfeasibleError(Exception):
    """
    Infeasibility of a parameter set.
    """

    def __init__(self, reason=None, refs=None, part=None):
        """
        Exception constructor.
        """
        if part is None:
            part = ()
        elif not isinstance(part, tuple):
            part = (part, )
        if refs is None:
            refs = []
        elif not isinstance(refs, list):
            refs = [refs]
        refs = [(references[pap], thm)
                for pap, thm in (ref if isinstance(ref, tuple) else (ref, None)
                                 for ref in refs)]
        if isinstance(reason, InfeasibleError):
            self.reason = reason.reason
            self.refs = reason.refs + refs
            self.part = reason.part + part
        elif isinstance(reason, Exception):
            self.reason = ", ".join(str(x) for x in reason.args)
            self.refs = refs
            self.part = part
        else:
            self.reason = reason
            self.refs = refs
            self.part = part
        msg = []
        if len(self.part) > 0:
            msg.append(" of ".join(self.part))
        if self.reason is not None:
            msg.append(self.reason)
        if len(self.refs) > 0:
            msg.append("nonexistence by %s" %
                       "; ".join(self.formatRef(ref) for ref in self.refs))
        self.args = (": ".join(msg), )

    @staticmethod
    def formatRef(ref):
        """
        Format reason for nonexistence.
        """
        pap, thm = ref
        if thm is None:
            return pap.name
        else:
            return f"{pap.name}, {thm}"


class Parameters:
    """
    An auxiliary class for storing the computed parameters.
    """

    d = None

    def __init__(self, p):
        """
        Object constructor.
        """
        self._parameters = p
        self.fusion_schemes = {}
        self.subschemes = {}
        self.triple = {}
        self.triple_solution = {}
        self.triple_solution_generator = {}
        self.quadruple = {}

    def __repr__(self):
        """
        String representation.
        """
        return "Parameter storage of <%s>" % repr(self._parameters)
