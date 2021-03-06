from sympy.core import S
from sympy.core.relational import Eq, Ne, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan, Equality, Unequality
from sympy.logic.boolalg import And, Or, BinaryCondition
from sympy.utilities.misc import func_name
from sympy.core.sympify import _sympify, sympify


class Contains(BinaryCondition):
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
    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify(), equivalent=[self, eq]).simplify()
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
            return self
        old, new = args
        new = _sympify(new)

        if self.plausible:

            lhs, rhs = self.lhs._subs(old, new), self.rhs._subs(old, new)
            if hasattr(new, 'has') and new.has(old):
                eq = self.func(lhs, rhs, substituent=self)
            else:
                eq = self.func(lhs, rhs, given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        
        if old.is_symbol:
            if new in old.domain:
                lhs = self.lhs._subs(old, new)
                rhs = self.rhs._subs(old, new)            
                return self.func(lhs, rhs, given=self)
            if old.domain_assumed is not None:
                return self.forall((old,)).subs(old.unbounded, new)
        return self

    def _latex(self, p):
        return r"%s \in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return r"%s ∈ %s" % tuple(p._print(a) for a in self.args)

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
            return ret

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)

    def split(self):
        if self.rhs.is_Union:
            return [self.func(self.lhs, rhs, imply=self) for rhs in self.rhs.args]
        if self.rhs.is_Intersection:
            args = [self.func(self.lhs, rhs, given=self) for rhs in self.rhs.args]
            if self.plausible:
                self.derivative = args
            return args
        
        if self.rhs.is_Interval:
            if self.rhs.left_open:
                lower_bound = self.lhs > self.rhs.start
            else:
                lower_bound = self.lhs >= self.rhs.start
            if self.rhs.right_open:
                upper_bound = self.lhs < self.rhs.stop
            else:
                upper_bound = self.lhs <= self.rhs.stop
            upper_bound.given = lower_bound.given = self
            return [lower_bound, upper_bound]
        return self

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
            res[1] = StrictLessThan(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.stop, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    def simplify(self, *_, **__):
        e, s = self.args
        if s.is_FiniteSet:
            if len(s) == 1:
                y, *_ = s
                from sympy import Symbol
                if not e._has(Symbol) and y._has(Symbol):
                    return Equality(y, e, equivalent=self)
                return Equality(e, y, equivalent=self)
#             return Or(*(Equality(e, y) for y in s), equivalent=self)

        if s.is_ConditionSet:
            if e == s.variable:
                return s.condition.copy(equivalent=self)
            condition = s.condition._subs(s.variable, e)
            condition.equivalent = self
            return condition

        if s.is_Interval:
            if s.is_integer and e.is_Add:
                if not s.left_open or s.right_open:
                    if S.NegativeOne in e.args:
                        s += S.One
                        e += S.One
                        return self.func(e, s, evaluate=False, equivalent=self)
                        
                if s.left_open or not s.right_open:
                    if S.One in e.args:
                        s -= S.One
                        e -= S.One
                        return self.func(e, s, evaluate=False, equivalent=self)
                    
            if e.is_integer == s.is_integer:
                if s.start is S.NegativeInfinity:
                    func = StrictLessThan if s.right_open else LessThan
                    return func(e, s.stop, equivalent=self)
                if s.stop is S.Infinity:
                    func = StrictGreaterThan if s.left_open else GreaterThan
                    return func(e, s.start, equivalent=self)
                complement = e.domain - s
                if complement.is_FiniteSet:
                    return self.invert_type(e, complement, equivalent=self).simplify()                
            
        if s.is_Complement and s.args[1].is_FiniteSet and len(s.args[1]) == 1:
            domain_assumed = e.domain_assumed
            if domain_assumed and domain_assumed == s.args[0]:
                _e, *_ = s.args[1].args
                return Unequality(e, _e, equivalent=self)
            
        return self

# this assertion is useless!
    def assertion(self):
        from sympy.concrete.expr_with_limits import Exists
        e, S = self.args
        x = S.element_symbol(self.free_symbols)
        assert x.dtype == e.dtype
        return Exists(Equality(x, e), (x, S), equivalent=self)

    @property
    def definition(self):
        e, S = self.args

        from sympy.concrete.expr_with_limits import Exists

        condition_set = S.condition_set()
        if condition_set:
            condition = condition_set.condition
            if condition_set.variable != e:
                condition = condition._subs(condition_set.variable, e)
            return And(condition, self.func(e, condition_set.base_set), equivalent=self)

        image_set = S.image_set()
        if image_set is not None:
            expr, variables, base_set = image_set
            from sympy import Wild
            variables_ = Wild(variables.name, **variables.dtype.dict)
            assert variables_.shape == variables.shape
            e = e.subs_limits_with_epitome(expr)
            dic = e.match(expr.subs(variables, variables_))
            if dic:
                variables_ = dic[variables_]
                if variables.dtype != variables_.dtype:
                    assert len(variables.shape) == 1
                    variables_ = variables_[:variables.shape[-1]]
                return Contains(variables_, base_set, equivalent=self)

            if e._has(variables):
                _variables = base_set.element_symbol(e.free_symbols)
                assert _variables.dtype == variables.dtype
                expr = expr._subs(variables, _variables)
                variables = _variables
            assert not e._has(variables)
            return Exists(Equality(e, expr, evaluate=False), (variables, base_set), equivalent=self)

        if S.is_UNION:
            for v in S.variables:
                if self.lhs._has(v):
                    _v = v.generate_free_symbol(self.free_symbols, **v.dtype.dict)
                    S = S.limits_subs(v, _v)

            contains = Contains(self.lhs, S.function).simplify()
            contains.equivalent = None
            return Exists(contains, *S.limits, equivalent=self).simplify()

        return self

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_NotContains:
            if self.element == other.element:
                s = self.set - other.set
                return self.func(self.element, s, equivalent=[self, other])
        elif other.is_Contains:
            if self.element == other.element:
                s = self.set & other.set
                return self.func(self.element, s, equivalent=[self, other])
            elif self.rhs == other.rhs:                
                return Subset(self.lhs.set | other.lhs.set, self.rhs, equivalent=[self, other])
        elif other.is_Subset:
            if self.rhs == other.lhs:
                return self.func(self.lhs, other.rhs, equivalent=[self, other])

        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        if other.is_Contains:
            x, X = self.args
            y, Y = other.args
            if x == y:                
                return self.func(x, X | Y, given=[self, other]).simplify()
            
        return BinaryCondition.__or__(self, other)

    def as_KroneckerDelta(self):
        x, domain = self.args 
        if domain.is_FiniteSet:
            return domain.as_KroneckerDelta(x)
    
        domain = x.domain - domain
        if domain.is_FiniteSet:             
            return 1 - domain.as_KroneckerDelta(x)
            
    def inverse(self):
        rhs = self.rhs.inverse()
        if rhs is not None:
            return self.func(1 / self.lhs, rhs, equivalent=self)
        return self

    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs.T, self.rhs, equivalent=self)
      
    def domain_conditioned(self, x):
        domain = x.domain & self.domain_defined(x)
        if x == self.lhs:
            return self.rhs
        interval = self.rhs
        if interval.is_Interval:                
            poly = self.lhs.as_poly(self)
            if poly is not None and poly.degree() == 1:
                c1 = poly.nth(1)
                c0 = poly.nth(0)
                if interval.is_integer:
                    if c1 == 1:
                        interval = interval.copy(start=interval.start - c0, stop=interval.stop - c0)
                        return domain & interval
                    elif c1 == -1:
                        interval = interval.copy(start=c0 - interval.stop, stop=c0 - interval.start, left_open=interval.right_open, right_open=interval.left_open)
                        return domain & interval                            
                else:
                    if c1 > 0:
                        interval.func(start=(interval.start - c0) / c1, stop=(interval.stop - c0) / c1)
                        return domain & interval
                    elif c1 < 0:
                        interval.func(start=(interval.stop - c0) / c1, stop=(interval.start - c0) / c1, left_open=interval.right_open, right_open=interval.left_open)
                        return domain & interval             
      
    def simplify_forall(self, forall):
        function, self = self, forall
        if function.is_Contains:
            x = function.lhs
            limits_dict = self.limits_dict            
            if x in limits_dict:
                domain = limits_dict[x]
                if domain in function.rhs:
                    return S.BooleanTrue.copy(equivalent=self)
                        
class NotContains(BinaryCondition):
    """
    Asserts that x is not an element of the set S

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
    invert_type = Contains
    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
            return self

        old, new = args
        new = sympify(new)
        if self.plausible:

            lhs, rhs = self.lhs._subs(old, new), self.rhs._subs(old, new)
            if hasattr(new, 'has') and new.has(old):
                eq = self.func(lhs, rhs, substituent=self)
            else:
                eq = self.func(lhs, rhs, given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        if old.domain_assumed is not None:
            if new in old.domain_assumed:
                ...
            else:
                return self.forall((old,)).subs(old.unbounded, new)

        return self.func(self.lhs.subs(*args, **kwargs).simplify(), self.rhs.subs(*args, **kwargs).simplify())

    def _latex(self, p):
        return r"%s \not\in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return r"%s ∉ %s" % tuple(p._print(a) for a in self.args)

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        from sympy.core.sympify import sympify
        if not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
            return sympify(not ret)

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def simplify(self, deep=False):
        e, s = self.args
        if s.is_FiniteSet:
            if len(s) == 1:
                y, *_ = s
                return Unequality(e, y, equivalent=self)
            return And(*(Unequality(e, y) for y in s), equivalent=self)

        if s.is_Interval and s.is_integer and e.is_Add:
            if S.NegativeOne in e.args:
                s += S.One
                e += S.One
                return self.func(e, s, evaluate=False, equivalent=self).simplify()
                    
            if S.One in e.args:                
                s -= S.One
                e -= S.One
                return self.func(e, s, evaluate=False, equivalent=self).simplify()
            
        domain = e.domain - s
        if domain.is_FiniteSet:
            return self.invert_type(e, domain).simplify()
        
        return self

    @property
    def definition(self):
        e, S = self.args

        from sympy.concrete.expr_with_limits import ForAll

        image_set = S.image_set()
        if image_set is not None:
            expr, variables, base_set = image_set
            from sympy import Wild
            variables_ = Wild(variables.name, **variables.dtype.dict)

            e = e.subs_limits_with_epitome(expr)
            dic = e.match(expr.subs(variables, variables_))
            if dic:
                variables_ = dic[variables_]
                if variables.dtype != variables_.dtype:
                    assert len(variables.shape) == 1
                    variables_ = variables_[:variables.shape[-1]]
                return self.func(variables_, base_set, equivalent=self)

            if e.has(variables):
                _variables = base_set.element_symbol(e.free_symbols)
                assert _variables.dtype == variables.dtype
                expr = expr._subs(variables, _variables)
                variables = _variables
            assert not e.has(variables)
            return ForAll(Unequality(e, expr, evaluate=False), (variables, base_set), equivalent=self)

        condition_set = S.condition_set()
        if condition_set:
            return Or(~condition_set.condition._subs(condition_set.variable, e), ~self.func(e, condition_set.base_set), equivalent=self)

        if S.is_UNION:
            contains = self.func(self.lhs, S.function).simplify()
            contains.equivalent = None
            return ForAll(contains, *S.limits, equivalent=self).simplify()

        return self

    def __and__(self, other):
        if other.is_NotContains:
            if self.element == other.element:
                s = self.set | other.set
                return self.func(self.element, s, equivalent=[self, other])
        elif other.is_Contains:
            if self.element == other.element:
                s = other.set - self.set
                return other.func(self.element, s, equivalent=[self, other])
        
        elif other.is_Unequality:
            x, X = self.args
            if x == other.rhs:
                X |= {other.lhs}
            elif x == other.lhs:
                X |= {other.rhs}
            else:
                X = None
            if X is not None:
                return self.func(x, X, equivalent=[self, other])      
            
        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        if other.is_NotContains:
            x, X = self.args
            y, Y = other.args
            if x == y:                
                return self.func(x, X & Y, given=[self, other])
            
        return BinaryCondition.__or__(self, other)

    def as_KroneckerDelta(self):
        x, domain = self.args 
        if domain.is_FiniteSet:
            return 1 - domain.as_KroneckerDelta(x)
        domain = x.domain - domain
        if domain.is_FiniteSet:
            return domain.as_KroneckerDelta(x)
            
    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs.T, self.rhs, equivalent=self)

    def split(self):
        if self.rhs.is_Union:
            args = [self.func(self.lhs, rhs, given=self) for rhs in self.rhs.args]
            if self.plausible:
                self.derivative = args
            return args
        if self.rhs.is_Intersection:
            return [self.func(self.lhs, rhs, imply=self) for rhs in self.rhs.args]
        
        if self.rhs.is_Interval:
            if self.rhs.left_open:
                lower_bound = self.lhs <= self.rhs.start
            else:
                lower_bound = self.lhs < self.rhs.start
            if self.rhs.right_open:
                upper_bound = self.lhs >= self.rhs.stop
            else:
                upper_bound = self.lhs > self.rhs.stop
            upper_bound.imply = lower_bound.imply = self
            return [lower_bound, upper_bound]
        return self

    def domain_conditioned(self, x):        
        if self.lhs == x:
            domain = x.domain & self.domain_defined(x)
            return x.domain_conditioned(self.invert_type(x, domain - self.rhs))
        
    def simplify_forall(self, forall):
        function, self = self, forall
        if function.is_NotContains:
            element = function.lhs
            container = function.rhs
            forall = self.limits_dict
            if element in forall:
                if forall[element] == container:
#                     assert S.BooleanFalse.equivalent is None
                    return S.BooleanFalse.copy(equivalent=self)

        
Contains.invert_type = NotContains


class Subset(BinaryCondition):
    """
    Asserts that A is a subset of the set S

    """
    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def simplify(self, deep=False):
        from sympy.concrete.expr_with_limits import ForAll
        if self.lhs.is_UNION:
            return ForAll(self.func(self.lhs.function, self.rhs).simplify(), *self.lhs.limits, equivalent=self).simplify()
        if self.lhs.is_FiniteSet:
            eqs = []
            for e in self.lhs.args:
                eqs.append(Contains(e, self.rhs))
            return And(*eqs, equivalent=self)

        return self

    def union(self, exp):
        if isinstance(exp, Subset):
            return self.func(self.lhs | exp.lhs, self.rhs | exp.rhs, given=[self, exp])
        else:
            return self.func(self.lhs | exp, self.rhs | exp, given=self)

    def intersect(self, exp):
        if isinstance(exp, Subset):
            return self.func(self.lhs & exp.lhs, self.rhs & exp.rhs, given=[self, exp])
        else:
            return self.func(self.lhs & exp, self.rhs & exp, given=self)
            
    def _sympystr(self, p):
#                 ⊂
        return '%s ⊆ %s' % tuple(p._print(x) for x in self.args)
    
    def _latex(self, printer):
        return r'%s \subset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        assert x.is_set and s.is_set, 'expecting Set, not %s' % func_name(s)
        if x.is_symbol and x.definition is not None:
            x = x.definition
        if s.is_symbol and s.definition is not None:
            s = s.definition

        if x == s:
            return S.true
        if s.is_Union:
            if x in s._argset:
                return S.true
        if x.is_Intersection:
            for e in x._argset:
                if e in s:
                    return S.true
        if x == S.EmptySet:
            return S.true

        if x.is_ConditionSet:
            sym, condition, base_set = x.variable, x.condition, x.base_set
            if s.is_ConditionSet:                
                _sym, _condition, _base_set = s.variable, s.condition, s.base_set
                if sym.dtype == _sym.dtype and (base_set == _base_set or base_set in _base_set):
                    if sym != _sym:
                        _condition = _condition._subs(_sym, sym)
                    if condition == _condition:
                        return S.true
                    if condition.is_And:
                        if _condition.is_And and all(eq in condition._argset for eq in _condition.args) or _condition in condition._argset:
                            return S.true
            base_set &= sym.domain
            if base_set in s:
                return S.true
            
        if x.is_Piecewise and not s.is_Piecewise:
            return x.func(*((cls(e, s), c) for e, c in x.args))
        
        if s.is_CartesianSpace:
            if x.is_Symbol:
                if x.element_type.as_Set() in s:
                    return S.true
                
    @property
    def definition(self):
        A, B = self.args
        from sympy.concrete.expr_with_limits import ForAll
        e = B.element_symbol(A.free_symbols)
        return ForAll(Contains(e, B), (e, A), equivalent=self).simplify()

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
            res[1] = StrictLessThan(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.stop, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            elif isinstance(eq, Subset):
                A, B = self.args
                _B, _A = eq.args
                if _B == B:
                    if A == _A: 
                        return Equality(A, B, equivalent=[self, eq])
                    else:
                        return self.func(A, _A, given=[self, eq])
            elif isinstance(eq, Supset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _A == A:
                    return Equality(A, B, equivalent=[self, eq])
            elif eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
            return self

        old, new = args
        new = _sympify(new)

        if self.plausible:

            lhs, rhs = self.lhs._subs(old, new), self.rhs._subs(old, new)
            if hasattr(new, 'has') and new.has(old):
                eq = self.func(lhs, rhs, substituent=self)
            else:
                eq = self.func(lhs, rhs, given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        
        if old.is_symbol and new in old.domain:
            lhs = self.lhs._subs(old, new)
            rhs = self.rhs._subs(old, new)            
            return self.func(lhs, rhs, given=self)

        return self

    def __and__(self, other):
        if other.is_Supset:
            if self.args == other.args:
                return Equality(*self.args, equivalent=[self, other])
        elif other.is_Subset:
            lhs, rhs = self.args
            if (rhs, lhs) == other.args:
                return Equality(*self.args, equivalent=[self, other])
            elif rhs == other.rhs:
                return self.func(lhs | other.lhs, rhs, equivalent=[self, other])
            elif rhs == other.lhs:
                return self.func(lhs, other.rhs, equivalent=[self, other]).simplify()
        elif other.is_Contains:
            if other.rhs == self.lhs:
                return other.func(other.lhs, self.rhs, equivalent=[self, other]).simplify()
        return BinaryCondition.__and__(self, other)

    def domain_conditioned(self, x):
        if self.lhs.is_FiniteSet:
            if x.dtype in self.lhs.element_type:
                if x in self.lhs:
                    return Contains(x, self.rhs).domain_conditioned(x)

    def simplify_forall(self, forall):
        function, self = self, forall
        if function.lhs.is_FiniteSet:
            function, S = function.lhs, function.rhs
            res = forall.simplify_int_limits(function)
            if res:
                function, limits = res            
                function = Subset(function, S).simplify()
                return self.func(function, *limits, equivalent=self).simplify()


class NotSubset(BinaryCondition):
    """
    Asserts that A is a subset of the set S

    """
    invert_type = Subset
    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def simplify(self, deep=False):
        if self.lhs.is_UNION:
            from sympy.concrete.expr_with_limits import Exists
            return Exists(self.func(self.lhs.function, self.rhs), *self.lhs.limits, equivalent=self)

        if self.lhs.is_FiniteSet and len(self.lhs) == 1:
            return NotContains(self.lhs.arg, self.rhs, equivalent=self).simplify()            
             
        return self

    def union(self, exp):
        return self

    def intersect(self, exp):
        if isinstance(exp, Subset):
            return self.func(self.lhs & exp.lhs, self.rhs & exp.rhs, given=[self, exp])
        else:
            return self.func(self.lhs & exp, self.rhs & exp, given=self)

    def _sympystr(self, p):
#         ⊊        
        return r'%s ⊄ %s' % tuple(p._print(x) for x in self.args)

    def _latex(self, printer):
        return r'%s \not\subset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        assert x.is_set and s.is_set, 'expecting Set, not %s' % func_name(s)
        if x.is_Symbol and x.definition is not None:
            x = x.definition
        if s.is_Symbol and s.definition is not None:
            s = s.definition
        b = cls.invert_type.eval(x, s)
        if b is not None:
            return b.invert()

    @property
    def definition(self):
        A, B = self.args
        from sympy.concrete.expr_with_limits import Exists
        e = B.element_symbol(A.free_symbols)
        return Exists(NotContains(e, B), (e, A), equivalent=self).simplify()

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
            res[1] = StrictLessThan(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.stop, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, Subset):
                A, B = self.args
                _B, _A = eq.args
                if A == _A and _A == A:
                    return Equality(A, B, equivalent=[self, eq])
            if isinstance(eq, Supset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _A == A:
                    return Equality(A, B, equivalent=[self, eq])

        return self


Subset.invert_type = NotSubset


class Supset(BinaryCondition):
    """
    Asserts that A is a super set of the set S

    """
    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)
    
    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, Subset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])
            if isinstance(eq, Supset):
                A, B = self.args
                _B, _A = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])

            return self
        old, new = args
        new = _sympify(new)

        if self.plausible:

            lhs, rhs = self.lhs._subs(old, new), self.rhs._subs(old, new)
            if hasattr(new, 'has') and new.has(old):
                eq = self.func(lhs, rhs, substituent=self)
            else:
                eq = self.func(lhs, rhs, given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        
        if old.is_symbol and new in old.domain:
            lhs = self.lhs._subs(old, new)
            rhs = self.rhs._subs(old, new)            
            return self.func(lhs, rhs, given=self)

        return self
    
    def __and__(self, other):
        if other.is_Subset:
            if self.args == other.args:
                return Equality(*self.args, equivalent=[self, other])
        elif other.is_Supset:
            lhs, rhs = self.args
            if (rhs, lhs) == other.args:
                return Equality(*self.args, equivalent=[self, other])
            elif lhs == other.lhs:
                return self.func(lhs, rhs | other.rhs, equivalent=[self, other])
            
        return BinaryCondition.__and__(self, other)
    
    def simplify(self, deep=False):
        from sympy.concrete.expr_with_limits import ForAll
        if self.rhs.is_UNION:
            return ForAll(self.func(self.lhs, self.rhs.function).simplify(), *self.rhs.limits, equivalent=self).simplify()
        if self.rhs.is_FiniteSet:
            eqs = []
            for e in self.rhs.args:
                eqs.append(Contains(e, self.lhs))
            return And(*eqs, equivalent=self)
        return self

    def _sympystr(self, p):
#         ⊃        
        return '%s ⊇ %s' % tuple(p._print(x) for x in self.args)

    def _latex(self, printer):
        return r'%s\supset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        return Subset.eval(s, x)
#     @property
#     def binary_symbols(self):
#         binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
#         return set().union(*binary_symbols)
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
            res[1] = StrictLessThan(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.stop, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    @property
    def definition(self):
        A, B = self.args
        e = A.element_symbol(B.free_symbols)
        from sympy.concrete.expr_with_limits import ForAll
        return ForAll(Contains(e, A), (e, B), equivalent=self).simplify()

class NotSupset(BinaryCondition):
    """
    Asserts that A is a super set of the set S

    """
    invert_type = Supset

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, Subset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])
            if isinstance(eq, Supset):
                A, B = self.args
                _B, _A = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])

        return self

    def simplify(self, deep=False):
        from sympy.concrete.expr_with_limits import Exists
        if self.rhs.is_UNION:
            return Exists(self.func(self.lhs, self.rhs.function), *self.rhs.limits, equivalent=self).simplify()
        return self

    def _sympystr(self, p):
#         ⊋
        return r'%s ⊅ %s' % tuple(p._print(x) for x in self.args)

    def _latex(self, printer):
        return r'%s\not\supset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        return NotSubset.eval(s, x)

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
            res[1] = StrictLessThan(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.stop, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    @property
    def definition(self):
        A, B = self.args
        e = A.element_symbol(B.free_symbols)
        from sympy.concrete.expr_with_limits import Exists
        return Exists(NotContains(e, A), (e, B), equivalent=self)


Supset.invert_type = NotSupset

Supset.reversed_type = Subset
Subset.reversed_type = Supset
NotSubset.reversed_type = NotSupset
NotSupset.reversed_type = NotSubset

