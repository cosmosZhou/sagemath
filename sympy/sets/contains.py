from __future__ import print_function, division

from sympy.core import S
from sympy.core.relational import Eq, Ne, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan
from sympy.logic.boolalg import BooleanFunction
from sympy.utilities.misc import func_name


class Contains(BooleanFunction):
    """
    Asserts that x is an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Contains
    >>> Contains(Integer(2), S.Integers)
    True
    >>> Contains(Integer(-2), S.Naturals)
    False
    >>> i = Symbol('i', integer=True)
    >>> Contains(i, S.Naturals)
    Contains(i, Naturals)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """

    @classmethod
    def eval(cls, x, s):
        from sympy.sets.sets import Set

        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if not isinstance(ret, Contains) and (
                ret in (S.true, S.false) or ret.is_set):
            return ret

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)
#         return set().union(*[i.binary_symbols
#             for i in self.args[1].args
#             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = StrictGreaterThan(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterThan(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = StrictLessThan(self.element, self.set.end, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.end, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self if self.plausible else None, **self.clauses())

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self if self.plausible else None, **self.clauses())

    def simplifier(self):
        forall = self.forall
        if forall is not None:
            if len(forall) == 1 and isinstance(forall, dict):
                (e, s), *_ = forall.items()
                image_set = s.image_set()
                if image_set is not None:
                    expr, sym, base_set = image_set
                    element = base_set.element_symbol

                    _e, S = self.args
                    return self.func(_e.subs(e, expr.subs(sym, element)), S, forall={element : base_set}, equivalent=self)

        return self

    @property
    def definition(self):
        e, S = self.args
        from sympy.core.symbol import Symbol
        if isinstance(S, Symbol):
            assertion = S.assertion()

            for k, v in assertion.forall.items():
                if v == S:
                    b = k
                    break

            del assertion.forall[b]
            assertion = assertion._subs(b, e)

            assertion.forall = assertion.combine_clause(assertion.forall, self.forall)
            assertion.exists = assertion.combine_clause(assertion.exists, self.exists)
            assertion.equivalent = self
            return assertion

        return self


class Subset(BooleanFunction):
    """
    Asserts that A is a subset of the set S

    """

    def _latex(self, printer):
        return r'%s \subset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
#         from sympy.sets.sets import Set

        assert x.is_set and s.is_set, 'expecting Set, not %s' % func_name(s)
        if x == s:
            return S.true

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)
#         return set().union(*[i.binary_symbols
#             for i in self.args[1].args
#             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    @property
    def definition(self):
        A, B = self.args

#         for e in A:
#             assert e in B
        from sympy import Symbol
        e = Symbol('e')
        return Contains(e, B, forall={e:A}, equivalent=self if self.plausible else None)

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = StrictGreaterThan(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterThan(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = StrictLessThan(self.element, self.set.end, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.end, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self if self.plausible else None, **self.clauses())

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self if self.plausible else None, **self.clauses())


class Supset(BooleanFunction):
    """
    Asserts that A is a super set of the set S

    """

    def _latex(self, printer):
        return r'%s\supset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        from sympy.sets.sets import Set

        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)
#         return set().union(*[i.binary_symbols
#             for i in self.args[1].args
#             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = StrictGreaterThan(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterThan(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = StrictLessThan(self.element, self.set.end, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.end, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self if self.plausible else None, **self.clauses())

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self if self.plausible else None, **self.clauses())

    @property
    def definition(self):
        A, B = self.args

#         for e in B:
#             assert e in A
        from sympy import Symbol
        e = Symbol('e')
        return Contains(e, A, forall={e:B}, equivalent=self if self.plausible else None)
