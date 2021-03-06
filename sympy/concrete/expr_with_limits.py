from sympy.core.add import Add
from sympy.core.compatibility import is_sequence
from sympy.core.containers import Tuple
from sympy.core.expr import Expr
from sympy.core.mul import Mul
from sympy.core.relational import Relational
from sympy.core.singleton import S
from sympy.core.symbol import Symbol, Dummy
from sympy.core.sympify import sympify
from sympy.functions.elementary.piecewise import (piecewise_fold,
    Piecewise)
from sympy.logic.boolalg import BooleanFunction, Boolean, And, Or, relationship
from sympy.matrices import Matrix
from sympy.tensor.indexed import Idx, Indexed, Slice
from sympy.sets.sets import Interval, Set, FiniteSet, Union, Complement, Intersection
from sympy.sets.fancysets import Range
from sympy.utilities import flatten
from sympy.utilities.iterables import sift, postorder_traversal
from sympy.functions.elementary.miscellaneous import Min, Max
from sympy.core.function import Derivative
from _functools import reduce
from sympy.matrices.expressions.matexpr import Concatenate
from sympy.core.logic import fuzzy_and


def _common_new(cls, function, *symbols, **assumptions):
    """Return either a special return value or the tuple,
    (function, limits, orientation). This code is common to
    both ExprWithLimits and AddWithLimits."""
    function = sympify(function)

    if function is S.NaN:
        return S.NaN

    if symbols:
        limits, orientation = _process_limits(*symbols)
        for i, li in enumerate(limits):
            if len(li) == 4:
                function = function.subs(li[0], li[-1])
                limits[i] = tuple(li[:-1])
                
            if len(li) == 3:
                oldsymbol = li[0] 
# added here to remove the domain of this variable!
                if isinstance(oldsymbol, Symbol) and oldsymbol.is_bounded:
                    newsymbol = oldsymbol.unbounded
                    function = function._subs(oldsymbol, newsymbol)
                    limits[i] = Tuple(newsymbol, *li[1:])
 
    else:
        # symbol not provided -- we can still try to compute a general form
#         free = function.free_symbols
#         if len(free) != 1:
#             raise ValueError(
#                 "specify dummy variables for %s" % function)
#         limits, orientation = [Tuple(s) for s in free], 1
        limits, orientation = [], 1

    # denest any nested calls
    while cls == type(function):
        limits = list(function.limits) + limits
        function = function.function

    # Any embedded piecewise functions need to be brought out to the
    # top level. We only fold Piecewise that contain the integration
    # variable.
    reps = {}
    symbols_of_integration = set([i[0] for i in limits])
    for p in function.atoms(Piecewise):
        if not p.has(*symbols_of_integration):
            reps[p] = Dummy()
    # mask off those that don't
    function = function.xreplace(reps)
    # do the fold
    function = piecewise_fold(function)
    # remove the masking
    function = function.xreplace({v: k for k, v in reps.items()})

    return function, limits, orientation


def _process_limits(*symbols):
    """Process the list of symbols and convert them to canonical limits,
    storing them as Tuple(symbol, lower, upper). The orientation of
    the function is also returned when the upper limit is missing
    so (x, 1, None) becomes (x, None, 1) and the orientation is changed.
    """
    limits = []
    orientation = 1
    for V in symbols:
        if isinstance(V, (Relational, BooleanFunction)):
            variable = V.atoms(Symbol).pop()
            V = (variable, V.as_set())

        if isinstance(V, Symbol) or getattr(V, '_diff_wrt', False):
            if isinstance(V, Idx):
                if V.lower is None or V.upper is None:
                    limits.append(Tuple(V))
                else:
                    limits.append(Tuple(V, V.lower, V.upper))
            else:
                limits.append(Tuple(V))
            continue
        elif is_sequence(V, Tuple):
            if len(V) == 2:
                if isinstance(V[1], Range):
                    lo = V[1].inf
                    hi = V[1].sup
                    dx = abs(V[1].step)
                    V = [V[0]] + [0, (hi - lo) // dx, dx * V[0] + lo]
                elif isinstance(V[1], set):
                    V = V[0], FiniteSet(*V[1])
            V = sympify(flatten(V))  # a list of sympified elements
            if isinstance(V[0], (Symbol, Idx)) or getattr(V[0], '_diff_wrt', False):
                newsymbol = V[0]
                if len(V) == 2 and isinstance(V[1], Interval):  # 2 -> 3
                    # Interval
                    V[1:] = [V[1].min(), V[1].max()]
                elif len(V) == 3:
                    # general case
                    if V[2] is None and not V[1] is None:
                        orientation *= -1
                        
                    V = [newsymbol] + [i for i in V[1:] if i is not None]

                if not isinstance(newsymbol, Idx) or len(V) == 3:
                    if len(V) == 4:
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 3:
                        if isinstance(newsymbol, Idx):
                            # Idx represents an integer which may have
                            # specified values it can take on; if it is
                            # given such a value, an error is raised here
                            # if the summation would try to give it a larger
                            # or smaller value than permitted. None and Symbolic
                            # values will not raise an error.
                            lo, hi = newsymbol.lower, newsymbol.upper
                            try:
                                if lo is not None and not bool(V[1] >= lo):
                                    raise ValueError("Summation will set Idx value too low.")
                            except TypeError:
                                pass
                            try:
                                if hi is not None and not bool(V[2] <= hi):
                                    raise ValueError("Summation will set Idx value too high.")
                            except TypeError:
                                pass
                            
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 1 or (len(V) == 2 and V[1] is None):
                        limits.append(Tuple(newsymbol))
                        continue
                    elif len(V) == 2:
                        limits.append(Tuple(newsymbol, V[1]))
                        continue

        raise ValueError('Invalid limits given: %s' % str(symbols))

    return limits, orientation


class ExprWithLimits(Expr):
    __slots__ = ['is_commutative']

    def _eval_is_integer(self):
        return self.function.is_integer

    def _eval_is_random(self):
        return self.function.is_random

    def finite_aggregate(self, x, s):
        args = []
        if len(s) > 1:
            if self.operator.is_Add:
                s &= self.function.domain_nonzero(x)
            if s.is_Complement:
                return self                
            if s.is_EmptySet:
                return self.operator.identity
            if s.is_Intersection:
                finiteset = []
                for e in s.args:
                    if e.is_FiniteSet:
                        finiteset.append(e)
                if len(finiteset) == 1:
                    s = finiteset[0]
            assert s.is_FiniteSet, str(s) 
        for k in s:
            if x == k:        
                expr = self.function
            else:
                expr = self.function._subs(x, k)
            args.append(expr.simplify())
        return self.operator(*args)         

    def subs_limits_with_epitome(self, epitome):
        if epitome.func == self.func and len(epitome.limits) == len(self.limits):
            _self = self
            for _v, v in zip(epitome.variables, self.variables):
                if _v != v:
                    _self = _self.limits_subs(v, _v)
            return _self
        return self

    def limits_intersect(self, expr, clue=None):
        return limits_intersect(self.limits, expr.limits, clue=clue)

    def limits_union(self, expr):
        return limits_union(self.limits, expr.limits)

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        _self = other
        for (x, *_), (_x, *_) in zip(other.limits, self.limits):
            if x != _x:
                _self = _self.limits_subs(x, _x)
                if not _self.is_ExprWithLimits:
                    return False
        return _self.limits == self.limits and _self.function._dummy_eq(self.function)

    @property
    def limits_dict(self):
        return limits_dict(self.limits)

    @property
    def limits_condition(self):
        eqs = []
        from sympy.sets.contains import Contains

        for x, domain in self.limits_dict.items():
            if domain is None:
                continue
            if domain.is_set:
                eqs.append(Contains(x, domain))
            else:
                eqs.append(domain)
        return And(*eqs)

    def limits_assertion(self):
        return ForAll(self.limits_condition, *self.limits)

    def limits_update(self, *args):
        return limits_update(self.limits, *args)

    def limits_delete(self, dic):
        return limits_delete(self.limits, dic)

    def limits_common(self, eq, is_or=False):
        return limits_common(self.limits, eq.limits, is_or)

    @property
    def atomic_dtype(self):
        return self.function.atomic_dtype
        
    def __new__(cls, function, *symbols, **assumptions):
        function = sympify(function)
        limits = []
        symbols = [*symbols]
        for i in range(len(symbols) - 1, -1, -1):
            sym = symbols[i]
            if isinstance(sym, tuple):
                sym = Tuple(*sym)
            
            if isinstance(sym, Tuple):            
                if len(sym) == 2:
                    if sym[1].is_BooleanTrue:
                        return function.copy(**assumptions)                    
                    x, domain = sym
                    if domain.is_set:
                        assert x.dtype in domain.element_type, "domain.element_type = %s\n, x.dtype = %s" % (domain.element_type, x.dtype)
                        if x.is_Symbol and x.is_bounded:
                            domain &= x.domain_bounded
                            _x = x.unbounded
#                             assert x.dtype == _x.dtype
                            sym = _x, domain
                            function = function._subs(x, _x)                            
                        elif domain.is_Interval:
                            sym = (x, domain.min(), domain.max())
                elif len(sym) == 3: 
                    x, *ab = sym
                    if x.is_Symbol and x.is_bounded:
                        _x = x.unbounded
                        function = function._subs(x, _x)
                        sym = (_x, *ab)
                        
                    a, b = ab
                    if a == b:
                        function = function._subs(x, a)                        
                        for j in range(i - 1, -1, -1):
                            _x, *ab = symbols[j]                            
                            ab = [e._subs(x, a) for e in ab]
                            symbols[j] = (_x, *ab)
                            if _x == x:
                                break                            
                            
                        continue
                    if x.is_integer and not x.shape:                        
                        if a == b + S.One:
                            return cls.operator.identity.copy(**assumptions)
                        
                limits.append(Tuple(*sym))
            else:
                limits.append(Tuple(sym,))
                
        limits.reverse()
    # denest any nested calls
        while cls == type(function):
            limits = list(function.limits) + limits
            function = function.function

        if not limits and symbols:
            return function.copy(**assumptions)
        
        if cls.is_Boolean:
            obj = Boolean.__new__(cls, **assumptions)
        else:
            obj = Expr.__new__(cls, **assumptions)
        arglist = [function]
        
        arglist.extend(limits)
        obj._args = tuple(arglist)

        return obj

    @property
    def function(self):
        """Return the function applied across limits.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x
        >>> Integral(x**2, (x,)).function
        x**2

        See Also
        ========

        limits, variables, free_symbols
        """
        return self._args[0]

    @property
    def limits(self):
        """Return the limits of expression.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i
        >>> Integral(x**i, (i, 1, 3)).limits
        ((i, 1, 3),)

        See Also
        ========

        function, variables, free_symbols
        """
        return self._args[1:]

    @property
    def variables(self):
        """Return a list of the limit variables.

        >>> from sympy import Sum
        >>> from sympy.abc import x, i
        >>> Sum(x**i, (i, 1, 3)).variables
        [i]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits]

    @property
    def variable(self):
        return self.limits[0][0]

    @property
    def variables_set(self):
        return set(l[0] for l in self.limits)

    @property
    def bound_symbols(self):
        """Return only variables that are dummy variables.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i, j, k
        >>> Integral(x**i, (i, 1, 3), (j, 2), k).bound_symbols
        [i, j]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits if len(l) != 1]

    @property
    def free_symbols(self):
        """
        This method returns the symbols in the object, excluding those
        that take on a specific value (i.e. the dummy symbols).

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y
        >>> Sum(x, (x, y, 1)).free_symbols
        {y}
        """
        # don't test for any special values -- nominal free symbols
        # should be returned, e.g. don't return set() if the
        # function is zero -- treat it like an unevaluated expression.
        function, limits = self.function, self.limits
        isyms = function.free_symbols
        for xab in limits:
#             if len(xab) == 1:
#                 isyms.add(xab[0])
#                 continue
            # take out the target symbol
            x, *ab = xab
            if x in isyms:
                isyms.remove(x)
            # add in the new symbols
            isyms -= {var for var in isyms if var._has(x)}
            
            for i in ab:
                isyms.update(i.free_symbols)            
        return isyms

    @property
    def is_number(self):
        """Return True if the Sum has no free symbols, else False."""
        return not self.free_symbols

    def _eval_interval(self, x, a, b):
        limits = [(i if i[0] != x else (x, a, b)) for i in self.limits]
        integrand = self.function
        return self.func(integrand, *limits)

    def _eval_subs(self, old, new):
        """
        Perform substitutions over non-dummy variables
        of an expression with limits.  Also, can be used
        to specify point-evaluation of an abstract antiderivative.

        Examples
        ========

        >>> from sympy import Sum, oo
        >>> from sympy.abc import s, n
        >>> Sum(1/n**s, (n, 1, oo)).subs(s, 2)
        Sum(n**(-2), (n, 1, oo))

        >>> from sympy import Integral
        >>> from sympy.abc import x, a
        >>> Integral(a*x**2, x).subs(x, 4)
        Integral(a*x**2, (x, 4))

        See Also
        ========

        variables : Lists the integration variables
        transform : Perform mapping on the dummy variable for integrals
        change_index : Perform mapping on the sum and product dummy variables

        """
        from sympy.core.function import AppliedUndef, UndefinedFunction
        func, limits = self.function, list(self.limits)

        # If one of the expressions we are replacing is used as a func index
        # one of two things happens.
        #   - the old variable first appears as a free variable
        #     so we perform all free substitutions before it becomes
        #     a func index.
        #   - the old variable first appears as a func index, in
        #     which case we ignore.  See change_index.

        # Reorder limits to match standard mathematical practice for scoping
        limits.reverse()

        if not isinstance(old, Symbol) or \
                old.free_symbols.intersection(self.free_symbols):
            sub_into_func = True
            for i, xab in enumerate(limits):
                if 1 == len(xab) and old == xab[0]:
                    if new._diff_wrt:
                        xab = (new,)
                    else:
                        xab = (old, old)
                limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                if self.func.__name__ in ('Sum', 'Product', 'Integral'):
                    if len(xab[0].free_symbols.intersection(old.free_symbols)) != 0:
                        sub_into_func = False
                        break

            if isinstance(old, AppliedUndef) or isinstance(old, UndefinedFunction):
                sy2 = set(self.variables).intersection(set(new.atoms(Symbol)))
                sy1 = set(self.variables).intersection(set(old.args))
                if not sy2.issubset(sy1):
                    raise ValueError(
                        "substitution can not create dummy dependencies")
                sub_into_func = True
            if sub_into_func:
                func = func.subs(old, new)
        else:
            # old is a Symbol and a dummy variable of some limit
            for i, xab in enumerate(limits):
                if len(xab) == 3:
                    limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                    if old == xab[0]:
                        break
        # simplify redundant limits (x, x)  to (x, )
        for i, xab in enumerate(limits):
            if len(xab) == 2 and (xab[0] - xab[1]).is_zero:
                limits[i] = Tuple(xab[0],)

        # Reorder limits back to representation-form
        limits.reverse()

        return self.func(func, *limits)

    def as_multiple_terms(self, x, domain):                
        universalSat = Interval(S.NegativeInfinity, S.Infinity, integer=True)
        args = []
        union = S.EmptySet 
        assert x in self.function.scope_variables            
        for f, condition in self.function.args:
            _domain = (universalSat - union) & x.domain_conditioned(condition) & domain
            assert not _domain or _domain.is_integer
            if not condition:
                union |= _domain
                assert not union or union.is_integer

            if isinstance(_domain, FiniteSet):
                for e in _domain:
                    args.append(f.subs(x, e))
            elif _domain != S.EmptySet:
                assert _domain.is_integer
                if _domain.is_Interval:
                    args.append(self.func(f, (x, _domain.min(), _domain.max())).simplify())
                else:
                    args.append(self.func(f, (x, _domain)).simplify())

        return args
    
    def _subs_limits(self, x, domain, new, simplify=True):

        def subs(function, x, domain, new):
            _function = function._subs(x, new)
            if _function == function:
                return self
            function = _function
            
            kwargs = {}
            if self.is_Boolean:
                kwargs['equivalent'] = self
#             domain = [dom._subs(x, new) for dom in domain]
            index = self.variables.index(x)
            limits = [*self.limits]
            if 'domain' in new._assumptions:
                if len(domain) == 2:
                    dom = Interval(*domain, integer=True)
                    assert new.domain == dom
                elif domain:
                    dom = domain[0]
                    if not dom.is_set:
                        dom = new.domain_conditioned(dom)
                    assert new.domain == dom
                limits[index] = (new,)
            else:
                if len(domain) == 1:
                    domain = domain[0]
                    if domain.is_boolean:
                        domain = domain._subs(x, new)
                    limits[index] = (new, domain)
                else:
                    limits[index] = (new, *domain)
            for i in range(index):
                v, *domain = limits[i]
                domain = [dom._subs(x, new) for dom in domain]
                limits[i] = (v, *domain)

            this = self.func(function, *limits, **kwargs)
            return this.simplify() if simplify else this

        if self.function.is_ExprWithLimits and new in self.function.variables_set:
            if self.function.is_Exists:
                return self
            y = self.function.generate_free_symbol(self.function.variables_set, **new.dtype.dict)
            assert new != y
            function = self.function.limits_subs(new, y)
            if function == self.function:
                return self
            this = subs(function, x, domain, new)
 
            if this.is_ExprWithLimits:
                if this.function.is_ExprWithLimits and y in this.function.variables_set:
                    function = this.function.limits_subs(y, x)
                else:
                    function = this.function
     
                this = this.func(function, *this.limits)
                
            if this.is_Boolean:
                this.equivalent = self
            return this
        return subs(self.function, x, domain, new)

    def limits_subs(self, old, new, simplify=True):
        from sympy.solvers import solve
        if len(self.limits) == 1:
            limit = self.limits[0]
            x, *domain = limit

            if old == x:
                if self.function._has(new):
                    return self
                
                if not domain:                    
                    if new._has(x):
                        p = new.as_poly(x)
                        if p is None or p.degree() != 1:
                            return self
                        alpha = p.coeff_monomial(x)
                        if alpha == 1:
                            diff = new - x
                            a, b = x.domain.min() - diff, x.domain.max() - diff
                            self = self.func(self.function._subs(old, new), (x, a, b))
                            return self.simplify() if simplify else self
                        elif alpha == -1:
                            return self
                        else:
                            return self
                    else:
                        domain_assumed = new.domain_assumed
                        if domain_assumed:                            
                            assert domain_assumed == x.domain
                            limit = (new,)
                        else:
                            domain = x.domain
                            if domain.is_UniversalSet:
                                limit = (new,)
                            else:
                                limit = (new, domain)
                        self = self.func(self.function._subs(old, new), limit)
                        return self.simplify() if simplify else self
                if not new._has(x):
                    return self._subs_limits(x, domain, new, simplify=simplify)

            if len(domain) == 2:
                a, b = domain

            p = old.as_poly(x)

            if p is None or p.degree() != 1:
                if x.is_Slice:
                    x = x.subs(old, new)
                    self = self.func(self.function.subs(old, new), (x,))
                    return self.simplify() if simplify else self
                return self

            if new.has(x):
                diff = old - new
                if old != x:
                    if diff.has(x):
                        return self

                    alpha = p.coeff_monomial(x)
                    diff /= alpha
                    
                if diff.is_zero:
                    return self
                
                function = self.function._subs(x, x - diff)
                if len(domain) == 2:
                    self = self.func(function, (x, a + diff, b + diff))
                else:
                    self = self.func(function, (x,))
            else:
                if old != x:
                    sol = solve(old - new, x)
                    if len(sol) != 1:
                        return self
                    new = sol[0]
    
                _x = new.free_symbols - old.free_symbols
    
                if len(_x) != 1:
                    return self
                _x, *_ = _x
    
                function = self.function.subs(x, new)
    
                if domain:
                    a = solve(new - a, _x)
                    b = solve(new - b, _x)
                    if len(a) != 1 or len(b) != 1:
                        return self
                    a, b = a[0], b[0]
    
                    p = new.as_poly(_x)
                    alpha = p.coeff_monomial(_x)
                    if alpha > 0:
                        self = self.func(function, (_x, a, b))
                    elif alpha < 0:
                        self = self.func(function, (_x, b, a))
                    else:
                        return self
                else:
                    self = self.func(function, (_x))
            return self.simplify() if simplify else self

        elif len(self.limits) == 0:
            function = self.function.subs(old, new)

            return self.func(function, *self.limits)
        else:            
            
            if new in self.variables_set:
                d = Dummy(**new.dtype.dict)
                this = self.limits_subs(old, d)
                this = this.limits_subs(new, old)                
                return this.limits_subs(d, new)
            
            limits = [*self.limits]
            hit = False
            for i, limit in enumerate(limits):
                x, *domain = limit
                if old == x and not new.has(x):
                    return self._subs_limits(x, domain, new)

                if len(domain) == 2:
                    a, b = domain

                p = old.as_poly(x)
                if p is None or p.degree() == 0:
                    continue
                if p.degree() != 1:
                    return self

                if new.has(x):
                    diff = old - new
                    if old != x:
                        if diff.has(x):
                            return self

                        alpha = p.coeff_monomial(x)
                        diff /= alpha

                    function = self.function.subs(x, x - diff)
                    if domain:
                        limits[i] = (x, a + diff, b + diff)
                    for j in range(i):
                        var, *ab = limits[j]
                        if ab:
                            ab = [e._subs(x, x - diff) for e in ab]
                            limits[j] = (var, *ab)
                    hit = True
                break

            if not hit:
                return self.func(self.function.subs(old, new), *self.limits)
            
            return self.func(function, *limits)

        return self
    
#     Override this stub if you want to do anything more than
#     attempt a replacement of old with new in the arguments of self.
    def _subs_utility(self, old, new, **hints):
        if old.is_symbol and not self.function._has(old):
            if not any(limit._has(old) for limit in self.limits):
                return self
            
            hit = False
            limits = [*self.limits]
             
            for i, limit in enumerate(self.limits):
                _limit = limit._subs_limits(old, new)
                if _limit != limit:
                    limits[i] = _limit
                    hit = True
            if hit:
                self = self.func(self.function, *limits).simplify()
            return self
            
        intersect = {x for x in new.free_symbols & self.variables_set - old.free_symbols if not old._has(x)}            
        if intersect:                
            this = self
            excludes = self.variables_set | new.free_symbols
            for var in intersect:
                _var = self.generate_free_symbol(excludes, integer=True)
                this = this.limits_subs(var, _var)
                excludes.add(_var) 
            _this = this._subs(old, new)
            if _this == this:
                return self
            return _this
        
        from sympy.core.basic import _aresame
        if self == old or _aresame(self, old) or self.dummy_eq(old):        
            return new

        if old in self.variables_set:
            for i in range(len(self.limits) - 1, -1, -1):
                x = self.limits[i][0]
                if x != old:
                    continue
                
                hit = False
                limits = [*self.limits]
                for j in range(i, len(self.limits)):
                    limit = self.limits[j]
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[j] = _limit
                        hit = True                    
                if hit:
                    self = self.func(self.function, *limits)
                break
            return self
        
        if old.is_Slice:
            rule = {}
            for limit in self.limits[::-1]:
                x, *domain = limit
                if len(domain) == 2:
                    a, b = domain
                    if a.free_symbols & rule.keys():
                        a = a.subs(rule)
                    if b.free_symbols & rule.keys():
                        b = b.subs(rule)
                    rule[x] = x.copy(domain=Interval(a, b, integer=True))
            function = self.function
            if rule:
                function = self.function.subs(rule)

            _function = function._subs(old, new)
            if _function != function:
                if rule:
                    _function = _function.subs({v : k for k, v in rule.items()})

                return self.func(_function, *(limit._subs(old, new) for limit in self.limits))
            
    def _subs(self, old, new, **hints):
        this = self._subs_utility(old, new, **hints)
        if this is not None:
            return this
        from sympy.core.basic import _aresame
        hit = False
        args = list(self.args)
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new)    
            if not _aresame(arg, args[i]):
                hit = True
                args[i] = arg
        if hit:
            rv = self.func(*args)
            return rv
        return self

    def bisect(self, indices, wrt=None):
        kwargs = {'evaluate': False}
        if self.is_Boolean:
            kwargs['equivalent'] = self                
        
        if len(self.limits) > 1:
            if wrt is None:
                x, *ab = self.limits[-1]
                if len(ab) == 2: 
                    a, b = ab   
                    if x.is_integer:                 
                        mid = Symbol.process_slice(indices, a, b + 1)
                        assert mid >= a, "mid >= a => %s" % (mid >= a)        
                        assert mid <= b + 1, "mid <= b + 1 => %s" % (mid <= b + 1)
                        
                        if mid is None:
                            return self
                        if isinstance(mid, tuple):
                            ...
                            assert False                        
                        return self.func.operator(self.func(self.function, *self.limits[:-1], (x, a, mid - 1)).simplify(), self.func(self.function, *self.limits[:-1], (x, mid, b)).simplify(), **kwargs)
                    
                return self
            
            for i, limit in enumerate(self.limits):
                x, *ab = limit 
                if x != wrt:
                    continue
                if len(ab) == 2:
                    universe = Interval(*ab, integer=x.is_integer)
                else:
                    universe, *_ = ab
                    
                limits1 = [*self.limits]
                limits1[i] = (x, universe & indices)
                
                limits2 = [*self.limits]
                limits2[i] = (x, universe - indices)

                return self.func.operator(self.func(self.function, *limits1).simplify(), self.func(self.function, *limits2), **kwargs)
            return self

        (x, *ab), *_ = self.limits
        if x.is_Slice:
            x, z = x.bisect(indices).args
            return self.func(self.func(self.function, (x,)).simplify(), (z,))

        if not isinstance(indices, slice):            
            if len(ab) == 1:
                universe = ab[0]
            elif len(ab) == 2:
                universe = Interval(*ab, integer=True)
            else:
                universe = x.domain
                
            intersection = universe & indices
            if intersection:
                return self.func.operator(self.func(self.function, (x, intersection)).simplify(),
                                          self.func(self.function, (x, universe - indices)).simplify(), **kwargs)
            return self

        if len(ab) == 2:
            a, b = ab
            if x.is_integer:
                mid = Symbol.process_slice(indices, a, b + 1)
                assert mid >= a, "mid >= a => %s" % (mid >= a)        
                assert mid <= b + 1, "mid <= b + 1 => %s" % (mid <= b + 1)
    
                if mid is None:
                    return self
                if isinstance(mid, tuple):
                    ...
                    assert False                        
                    
                lhs = self.func(self.function, (x, a, mid - 1))                
                rhs = self.func(self.function, (x, mid, b))
                return self.func.operator(lhs.simplify(), rhs.simplify(), **kwargs)

        return self

    def _has(self, pattern):
        """Helper for .has()"""
#         from sympy.tensor.indexed import Indexed, Slice
        from sympy.core.assumptions import BasicMeta
        from sympy.core.function import UndefinedFunction
        if isinstance(pattern, (BasicMeta, UndefinedFunction)):
            return Expr._has(self, pattern)
        if not isinstance(pattern, (Symbol, Indexed, Slice)):
            return Expr._has(self, pattern)

        function = self.function
        limits = []

        if self.limits:
            for i, limit in enumerate(self.limits):
                x, *args = limit
                if x == pattern:
                    mapping = self.limits_dict
                    domain = mapping.pop(x)
                    if domain is not None and domain.is_set and domain._has(pattern):
                        return True
                    
                    mapping = limits_dict(self.limits[i + 1:])
                        
                    for k, domain in mapping.items():
                        if k._has(pattern) or domain is not None and domain.is_set and domain._has(pattern):
                            return True
                    return False

                if x.is_Slice and pattern.is_Slice and x.base == pattern.base:
                    if pattern in x:
                        return False
                    if x in pattern:
                        start, stop = x.indices
                        _start, _stop = pattern.indices
                        if _start < start:
                            if self._has(pattern[_start : start]):
                                return True
                        if stop < _stop:
                            if self._has(pattern[stop  : _stop]):
                                return True
                    return False
                
                if (pattern.is_Slice or pattern.is_Indexed) and len(args) == 2 and args[0].is_integer:
                    assert args[1].is_integer or args[1].is_infinite, "self = %s, args = %s" % (self, args)
                    _x = x.copy(domain=Interval(*args, integer=True))
                    function = function._subs(x, _x)
                    limits.append(Tuple(_x, *args))
                else:
                    limits.append(limit)
                        
        boolean = function._has(pattern)

        return boolean or any(arg._has(pattern) for arg in limits)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 0, cls.__name__

    @property
    def shape(self):
        return self.function.shape

    def domain_defined(self, x):
        from sympy.core.symbol import Wild
        if x.atomic_dtype.is_set:
            return S.UniversalSet            
        
        domain = x.domain
        limits_dict = self.limits_dict
        if x in limits_dict:
            return domain
                    
        for expr in limits_dict.values():
            if expr is None:
                continue
            domain &= expr.domain_defined(x)
        
        if self.function._has(x):
            domain &= self.function.domain_defined(x)
            if x not in self.function.free_symbols:
                v = self.variable
                if not v.is_Slice:
                    v_domain = self.limits_dict[v]
                    
                    for free_symbol in self.function.free_symbols:
                        if not free_symbol._has(v) or not free_symbol.is_Indexed:
                            continue
                        pattern = free_symbol.subs(v, Wild(v.name, **v.assumptions0))
                        res = x.match(pattern)
                        if res:    
                            t_, *_ = res.values()
                            if v_domain is None or t_ in v_domain:
                                function = self.function._subs(v, t_)
                                domain &= function.domain_defined(x)
                                break
            
        return domain

    def match_index(self, expr):
        if len(self.limits) != 1:
            return
        from sympy import Wild
        i, *_ = self.limits[0]
        i_ = Wild(i.name)

        dic = expr.match(self.function.subs(i, i_))
        if dic:
            return dic[i_]

    def limits_swap(self):
        if len(self.limits) == 2:
            i_limit, j_limit = self.limits
            j, *_ = j_limit
            if not i_limit._has(j):
                return self.func(self.function, j_limit, i_limit)
        return self

    def simplify(self, deep=False, **kwargs):
        limits = [*self.limits]
        dic = {x : domain for x, *domain in limits}
        updated = False
        for var, *domain in limits:
            if len(domain) == 1:
                domain = domain[0]
                if domain.is_set:
                    continue
            if not var.is_Slice:
                continue
            
            start, stop = var.indices
            if var.base[stop] in dic and not dic[var.base[stop]] and not dic[var]:
                del dic[var.base[stop]]
                del dic[var]
                dic[var.base[start : stop + 1]] = ()
                updated = True
            elif var.base[start - 1] in dic and not dic[var.base[start - 1]] and not dic[var]:
                del dic[var.base[start - 1]]
                del dic[var]
                dic[var.base[start - 1: stop]] = ()
                updated = True
            elif not self.function.has(var.base[stop - 1]):                
                del dic[var]
                _var = var.base[start : stop - 1]
                if not domain._has(_var):
                    domain = ()
                dic[_var] = domain
                updated = True
            elif not self.function.has(var.base[start]):
                if not domain._has(var.base[start]):
                    del dic[var]
                    dic[var.base[start + 1 : stop]] = domain
                    updated = True
            else:
                from sympy.core.basic import preorder_traversal
                validDomain = S.EmptySet
                for p in preorder_traversal(self.function):
                    if p.is_Slice and p.base == var.base:
                        validDomain |= Interval(*p.indices, right_open=True, integer=True)
                    elif p.is_Indexed and p.base == var.base:
                        validDomain |= p.indices[0].set
                universe = Interval(*var.indices, right_open=True, integer=True)
                if validDomain != universe and validDomain in universe:
                    if validDomain.is_Interval:
                        start, end = validDomain.min(), validDomain.max()
                        del dic[var]
                        dic[var.base[start : end + 1]] = domain
                        updated = True

        if updated:
            dic_original = {x : domain for x, *domain in limits}
            limits = [(key, *dic[key])for key in dic.keys() - dic_original.keys()] + limits
            for key in dic_original.keys() - dic.keys():
                del limits[[x for x, *_ in limits].index(key)]

            if self.is_boolean:
                kwargs = {'equivalent': self}
            else:
                kwargs = {}
            return self.func(self.function, *limits, **kwargs)
        return self


class AddWithLimits(ExprWithLimits):
    r"""Represents unevaluated oriented additions.
        Parent class for Integral and Sum.
    """

    is_complex = True
    
    def __new__(cls, function, *symbols, **assumptions):
        pre = _common_new(cls, function, *symbols, **assumptions)
        if type(pre) is tuple:
            function, limits, orientation = pre
        else:
            return pre

        obj = Expr.__new__(cls, **assumptions)
        if function.is_set:
            assert not limits
            if function.is_FiniteSet:                
                return Add(*function.args)
            if function.is_Interval:
                if function.is_integer:
                    a, b = function.min(), function.max()
                    return (a + b) * (b - a + 1) / 2
            arglist = [function]  # orientation not used in ExprWithLimits
        else:
            arglist = [orientation * function]  # orientation not used in ExprWithLimits
        arglist.extend(limits)
        obj._args = tuple(arglist)

        return obj

    def _eval_adjoint(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.adjoint(), *self.limits)
        return None

    def _eval_conjugate(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.conjugate(), *self.limits)
        return None

    def _eval_transpose(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.transpose(), *self.limits)
        return None

    def _eval_factor(self, **hints):
        if 1 == len(self.limits):
            summand = self.function.factor(**hints)
            if summand.is_Mul:
                out = sift(summand.args, lambda w: not set(self.variables) & w.free_symbols)
                return Mul(*out[True]) * self.func(Mul(*out[False]), *self.limits)
        else:
            summand = self.func(self.function, *self.limits[0:-1]).factor()
            if not summand.has(self.variables[-1]):
                return self.func(1, [self.limits[-1]]).doit() * summand
            elif isinstance(summand, Mul):
                return self.func(summand, self.limits[-1]).factor()
        return self

    def _eval_expand_basic(self, **hints):
        summand = self.function.expand(**hints)
#         if summand.is_Add and summand.is_commutative:
        if summand.is_Add:
            args = []
            for arg in summand.args:
                if arg._coeff_isneg():
                    args.append(-self.func(-arg, *self.limits))
                else:
                    args.append(self.func(arg, *self.limits))
            return Add(*args)
#             return Add(*[self.func(i, *self.limits) for i in summand.args])
        elif summand.is_DenseMatrix:
            return Matrix._new(summand.rows, summand.cols, [self.func(i, *self.limits) for i in summand._mat])
        elif summand != self.function:
            if summand._coeff_isneg():
                return -self.func(-summand, *self.limits)
            return self.func(summand, *self.limits)
        
        return self

    def as_multiple_limits(self):
        if self.function.is_Mul:
            integral = []
            function = []
            for arg in self.function:
                if isinstance(arg, self.func):
                    integral.append(arg)
                else:
                    function.append(arg)
            if integral:
                limits = self.limits[:]
                for it in integral:
                    limits += it.limits
                    if isinstance(it.function, Mul):
                        function += it.function.args
                    else:
                        function.append(it.function)
                return self.func(Mul(*function), *limits)
        return self

    def as_separate_limits(self):
        if len(self.limits) < 2:
            return self
        limit = self.limits[0]
        if len(limit) == 1:
            function = self.func(self.function, *self.limits[1:]).as_separate_limits().simplify()
            return self.func(function, limit)
        x, a, b = limit

        limits = []
        for i in range(1, len(self.limits)):
            t, *domain = self.limits[i]
            if domain:
                domain = Interval(*domain, integer=True)
            else:
                domain = Interval(-S.oo, S.oo, integer=True)

            if a.has(t):
                domain &= t.domain_conditioned(a <= x)
                a = MIN(a, self.limits[i]).doit()
            if b.has(t):
                domain &= t.domain_conditioned(x <= b)
                b = MAX(b, self.limits[i]).doit()

            limits.append((t, domain.start, domain.stop))

        function = self.func(self.function, *limits).as_separate_limits().simplify()
        return self.func(function, (x, a, b))

    def _eval_is_extended_real(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                
        return function.is_extended_real
    
    def _eval_is_extended_positive(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                    
        return function.is_extended_negative


class MINMAXBase(ExprWithLimits):
    
    is_extended_real = True
    
    @property
    def shape(self):
        if self.limits:
            return self.function.shape
        return self.function.shape[:-1]
    
    def _eval_is_finite(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite
    
    def simplify(self, deep=False, **kwargs):
        if not self.limits:
            if self.function.is_LAMBDA:
                if len(self.function.limits) == 1 and not self.function.variable.shape:
                    function = self.function.function
                    self = self.func(function, *self.function.limits).simplify(**kwargs)
            elif self.function.is_Piecewise:
                self = self.function.func(*((self.func(e).simplify(), c) for e, c in self.function.args)).simplify()            
            return self
        (x, *_), *_ = self.limits
        independent, dependent = self.function.as_independent(x, as_Add=True)
        if not independent.is_zero:            
            return self.func(dependent, *self.limits) + independent
        
        independent, dependent = self.function.as_independent(x, as_Add=False)
        if independent != S.One:            
            if independent.is_extended_negative:
                return self.reversed_type(dependent, *self.limits) * independent
            if independent.is_extended_positive:
                return self.func(dependent, *self.limits) * independent
            if independent._coeff_isneg():
                return -self.func.reversed_type(-self.function, *self.limits)
            
        if self.function.is_Log:
            return self.function.func(self.func(self.function.arg, *self.limits))
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def bounds(self, x, domain):
        function = self.function        
        from sympy import limit
        maxi = domain.max()
        if maxi.is_infinite:
            if self.function.is_infinitesimal is not None:
                function = function.clear_infinitesimal()
            maxi = limit(function, x, maxi)
            if self.function.is_infinitesimal is not None:
                maxi += self.function.args[-1]    
        else:
            maxi = function._subs(x, maxi, symbol=False)
    
        mini = domain.min()
        if mini.is_infinite:
            if self.function.is_infinitesimal is not None:
                function = function.clear_infinitesimal()
            mini = limit(function, x, mini)
            if self.function.is_infinitesimal is not None:
                maxi += self.function.args[-1]    
        else:      
            mini = function._subs(x, mini, symbol=False)
        return maxi, mini
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.function))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.function))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[:3]

        if len(self.limits) == 1:            
            tex = r"\%s\limits_{%s} " % (name, self.limits[0]._format_ineq(p))
        elif len(self.limits) == 0:
            tex = r"\%s " % name
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"\%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"\%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.function, Add):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex

    def astype(self, cls):
        if cls.is_LAMBDA:
            *limits, limit = self.limits
            if limits:
                return self.func(cls(self.func(self.function, *limits), limit).simplify())
            return self.func(cls(self.function, limit).simplify())
            
        return ExprWithLimits.astype(self, cls)

    def as_Exp(self):
        func = self.function.func
        function = self.function.arg
        return func(self.func(function, *self.limits).simplify())

    @property
    def atomic_dtype(self):
        if not self.limits:
            if self.function.is_set:
                return self.function.element_type
        return self.function.atomic_dtype


class Minimize(MINMAXBase):
    r"""Represents unevaluated MIN operator.
    Minimize[f,x]
    minimizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Min

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if domain:
            domain = Interval(*domain)
        else:
            domain = x.domain        
            if domain.is_CartesianSpace:
                return self
            
        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_positive:
                    return self.function.subs(x, domain.min())
                elif a.is_negative:
                    return self.function.subs(x, domain.max())
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_negative:
                    return Min(*self.bounds(x, domain))
                elif a.is_positive:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.coeff_monomial(x)
                        return (4 * a * c - b * b) / (4 * a)
                    return Min(*self.bounds(x, domain))
            elif p.degree() <= 0:
                return self.function
        elif self.function.is_MinMaxBase:
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))

        return self
    
    def _eval_summation(self, f, x):
        return None
        
    def assertion(self):
        from sympy.core.relational import LessThan
        return ForAll(LessThan(self, self.function), *self.limits)

    def _eval_is_extended_negative(self):
        if not self.limits and self.function.is_set:
            if self.function.infimum().is_extended_negative:
                return True

    def _eval_is_extended_positive(self):
        if not self.limits and self.function.is_set:
            if self.function.infimum().is_extended_positive:
                return True
            
    # infimum returns the value which is bound to be below (<=) the minimum!
    def infimum(self):
        if not self.limits and self.function.is_set:
            return self.function.infimum()
        return self

            
MIN = Minimize

                
class Maximize(MINMAXBase):
    r"""Represents unevaluated MAX operator.
    Maximize[f,x]
    maximizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Max

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]

        if domain:
            domain = Interval(*domain)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self

        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_positive:
                    return self.function.subs(x, domain.max())
                elif a.is_negative:
                    return self.function.subs(x, domain.min())
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_positive:
                    return Max(*self.bounds(x, domain))
                elif a.is_negative:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.coeff_monomial(x)
                        return (4 * a * c - b * b) / (4 * a)
                    return Max(*self.bounds(x, domain))
            elif p.degree() <= 0:
                return self.function
        elif self.function.is_MinMaxBase:
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))
                
        return self
    
    def separate(self):
        (x, *_), *_ = self.limits
        if x.is_Slice:
            z, x = x.pop()
            return self.func(self.func(self.function, (x,)).simplify(), (z,))
        return self

    def assertion(self):
        from sympy.core.relational import GreaterThan
        return ForAll(GreaterThan(self, self.function), *self.limits)

    # supremum returns the value which is bound to be above (>=) the minimum!
    def supremum(self):
        if not self.limits and self.function.is_set:
            return self.function.supremum()
        return self

    def _eval_is_extended_positive(self):
        if not self.limits and self.function.is_set:
            if self.function.supremum().is_extended_positive:
                return True

    def _eval_is_extended_negative(self):
        if not self.limits and self.function.is_set:
            if self.function.supremum().is_extended_negative:
                return True


MAX = Maximize

MAX.reversed_type = MIN
MIN.reversed_type = MAX


class ArgMinMaxBase(ExprWithLimits):

    @property
    def shape(self):
        shape = None
        for x, *_ in self.limits:
            x_shape = x.shape
            if shape is None:
                shape = x_shape
                continue
            if x_shape == shape:
                shape = (2, *shape)                
                continue            
            assert x_shape == shape[1:], 'illegal shape %s' % x_shape
            shape = (shape[0] + 1, *x_shape)
                
        return shape
    
    def _eval_is_complex(self):
        return fuzzy_and(x.is_complex for x, *_ in self.limits)
    
    def simplify(self, deep=False, **kwargs):
        if not self.limits:
            if self.function.is_LAMBDA:
                if len(self.function.limits) == 1 and not self.function.variable.shape:
                    function = self.function.function                    
                    return self.func(function, *self.function.limits).simplify(**kwargs)
            return self
        * _, (x, *_) = self.limits
        independent, dependent = self.function.as_independent(x, as_Add=True)
        if not independent.is_zero:            
            return self.func(dependent, *self.limits)
        
        independent, dependent = self.function.as_independent(x, as_Add=False)
        if independent != S.One:
            if independent.is_extended_positive:            
                return self.func(dependent, *self.limits)
            if independent.is_extended_negative:            
                return self.reversed_type(dependent, *self.limits)            

        if self.function._coeff_isneg():
            return self.func.reversed_type(-self.function, *self.limits)
        if self.function.is_Log:
            return self.func(self.function.arg, *self.limits)
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.function))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.function))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[3:6]
        name = r'\mathop{{\rm %s}^{-1}}' % name
        if len(self.limits) == 1:
            tex = r"%s\limits_{\substack{%s}} " % (name, self.limits[0]._format_ineq(p))
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.function, Add):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex

    def bounds(self, x, domain):
        function = self.function        
        from sympy import limit
        maxi = domain.max()
        if maxi.is_infinite:
            if self.function.is_infinitesimal is not None:
                function = function.clear_infinitesimal()
            maxi = limit(function, x, maxi)
            if self.function.is_infinitesimal is not None:
                maxi += self.function.args[-1]    
        else:
            maxi = function.subs(x, maxi)
    
        mini = domain.min()
        if mini.is_infinite:
            if self.function.is_infinitesimal is not None:
                function = function.clear_infinitesimal()
            mini = limit(function, x, mini)
            if self.function.is_infinitesimal is not None:
                maxi += self.function.args[-1]    
        else:            
            mini = function.subs(x, mini)
        return maxi, mini


class ArgMin(ArgMinMaxBase):
    r"""Represents unevaluated argmin operator.
    Minimize[f,x]
    minimizes f with respect to x.
    """

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        ...
        
    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if domain:
            domain = Interval(*domain)
        else:
            domain = x.domain        
            if domain.is_CartesianSpace:
                return self
            
        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_positive:
                    return domain.min()
                elif a.is_negative:
                    return domain.max()
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_negative:
                    return Min(*self.bounds(x, domain))
                elif a.is_positive:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.coeff_monomial(x)
                        delta = 4 * a * c - b * b
                        from sympy import sqrt
                        return (-b + sqrt(delta)) / (2 * a)
                    return Min(*self.bounds(x, domain))
            elif p.degree() <= 0:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
        elif self.function.is_MinMaxBase:
            print('warning, unreliable implementation')
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))

        return self
    
    def _eval_is_extended_negative(self):
        ...

    def _eval_is_extended_positive(self):
        ...
            
            
class ArgMax(ArgMinMaxBase):
    r"""Represents unevaluated argmax operator.
    Maximize[f,x]
    maximizes f with respect to x.
    """

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        ...

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]

        if domain:
            domain = Interval(*domain)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self

        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_positive:
                    return domain.max()
                elif a.is_negative:
                    return domain.min()
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_positive:
                    return Max(*self.bounds(x, domain))
                elif a.is_negative:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.coeff_monomial(x)
                        delta = 4 * a * c - b * b
                        from sympy import sqrt
                        return (-b + sqrt(delta)) / (2 * a)
                    return Max(*self.bounds(x, domain))
            elif p.degree() <= 0:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
        elif self.function.is_MinMaxBase:
            print('error, unreliable implementation')
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))
                
        return self
    
    def _eval_is_extended_positive(self):
        ...

    def _eval_is_extended_negative(self):
        ...


ArgMax.reversed_type = ArgMin
ArgMin.reversed_type = ArgMax


class LAMBDA(ExprWithLimits):
    r"""Represents unevaluated LAMBDA operator.
    """
    
    operator = Concatenate
    
    def __new__(cls, function, *symbols, **assumptions):
        symbols = list(symbols)

        for i, limit in enumerate(symbols):
            if isinstance(limit, tuple) and len(limit) > 1:
                x, *domain = limit
                if 'domain' in x._assumptions:
#                     local variable
                    if len(domain) == 2:
                        if x.domain == Interval(*domain, integer=x.is_integer):
                            symbols[i] = (x,)
                            continue
                    _x = Symbol(x.name, integer=True)
                    symbols[i] = (_x, *domain)

                    function = function.subs(x, _x)
                if len(domain) == 1:
                    domain, *_ = domain
                    assert domain.is_Interval and domain.is_integer
                    mini = domain.min()
                    symbols[i] = (x, 0, domain.max() - mini)
                    if mini != S.Zero:
                        function = function._subs(x, x + mini)

        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        limit = self.limits[-1]
        x, a, b = limit
        diff = b - a
        if not diff.is_Number:
            return self
        
        limits = self.limits[:-1]
        if limits:
            function = self.func(self.function, *limits).doit(**hints)
        else:
            function = self.function
                    
        array = []
        for i in range(diff + 1):
            array.append(function._subs(x, sympify(i)))
        return Concatenate(*array)

    def as_coeff_mmul(self):
        return 1, self

    def squeeze(self):
        if not self.function._has(self.variables[-1]):
            limits = self.limits[:-1]
            if limits:
                return self.func(self.function, *limits).squeeze()
            return self.function            
        return self
    
    def as_two_terms(self):
        if self.function.is_Add or self.function.is_Mul:
            first, second = self.function.as_two_terms()
            first = self.func(first, *self.limits).simplify(squeeze=True)
            second = self.func(second, *self.limits).simplify(squeeze=True)
            
            function = self.function.func(first, second)
            max_len = max(len(first.shape), len(second.shape))
            if max_len < len(self.shape):
                return self.func(function, *self.limits[:len(self.shape) - max_len])
            
            return function
        return self

    def simplify(self, deep=False, squeeze=False, **kwargs):
        from sympy import Contains
        limits_dict = self.limits_dict
        if deep:
            function = self.function
            reps = {}
            for x, domain in limits_dict.items():
                if domain.is_set and domain.is_integer:
                    _x = x.copy(domain=domain)
                    function = function._subs(x, _x)                  
                    if 'wrt' in kwargs:
                        function = function.simplify(deep=True, **kwargs)                        
                    else:
                        function = function.simplify(deep=True, wrt=_x, **kwargs)
                    
                    reps[_x] = x
            if reps:
                for _x, x in reps.items():
                    function = function._subs(_x, x)
                if function != self.function:
                    return self.func(function, *self.limits).simplify(squeeze=squeeze)
            
        if self.function.is_LAMBDA:
            return self.func(self.function.function, *self.limits + self.function.limits).simplify(squeeze=squeeze)
        
        if self.function.is_Piecewise:
            if len(limits_dict) > 1:
                function = self.func(self.function, self.limits[0]).simplify(squeeze=squeeze)
                if not function.is_LAMBDA:
                    return self.func(function, *self.limits[1:]).simplify(squeeze=squeeze)
            else:
                if len(self.function.args) == 2:
                    e0, c0 = self.function.args[0]
                    if c0.is_Contains:
                        e, s = c0.args
                        if e in limits_dict.keys():
                            if s.is_Complement:
                                U, A = s.args
                                domain, *_ = limits_dict.values()
                                if domain in U:
                                    e1, _ = self.function.args[1]
                                    function = self.function.func((e1, Contains(e, A)), (e0, True)).simplify()
                                    return self.func(function, *self.limits).simplify(squeeze=squeeze)
                            elif s.is_Interval:
                                if limits_dict[e] in s:
                                    return self.func(e0, *self.limits).simplify(squeeze=squeeze)
                if self.function.is_set:
                    return self
                
                constant = None
                args = []
                for e, c in self.function.args:
                    if not e._has(self.variable):
                        return self
                    
                    first, second = self.simplify_add(e)
                    if first is None:
                        return self
                    if constant is None:
                        constant = second
                    else:
                        if constant != second:
                            return self
                    args.append((first, c))
                this = self.function.func(*args)
                if second is not None:
                    this += self.func(second, *self.limits).simplify(squeeze=squeeze)
                return this
                    
        from sympy import Transpose
        from sympy.matrices.expressions.matmul import MatMul
        
        if self.function.is_set:
            independent, dependent = self.simplify_set(self.function)
            if independent is not None:
                return independent
            return self
        from sympy.concrete import summations
#         from sympy.matrices.expressions.hadamard import HadamardProduct
        if isinstance(self.function, summations.Sum) and not self.function.limits and isinstance(self.function.function, Mul):
            (x, *_), *_ = self.limits
            independent, dependent = [], []
            for arg in self.function.function.args:
                if arg.has(x):
                    dependent.append(arg)
                else:
                    independent.append(arg)

            if not dependent:
                return Mul(*independent)
            if not independent:
                return self

            dependent = Mul(*dependent)
            dependent = self.func(dependent, *self.limits)
            dependent = dependent.simplify()
            dependent = Transpose(dependent)
            dependent = dependent.simplify()

            independent = Mul(*independent)
            return MatMul(independent, dependent)

        if isinstance(self.function, Derivative):
            x, n = self.function.variable_count[0]
            order = 0
            for i, (_i, *_) in zip(x.indices[::-1], self.limits[::-1]):
                if i == _i:
                    order += 1
                    continue
                else:
                    break
            
            x = x.base[x.indices[:-order]]            
            function = Expr.__new__(self.function.func, self.function.expr, (x, n))
            limits = self.limits[:-order]
            if limits:
                return self.func(function, *limits)
            return function
        
        first, second = self.simplify_add(self.function)
        if first is None:
            first, second = self.simplify_mul(self.function)
            if first is None:
                from sympy import exp
                if isinstance(self.function, exp):
                    simplified = self.func(self.function.args[0], *self.limits).simplify()
                    if not isinstance(simplified, LAMBDA):
                        return exp(simplified)
                    
                if second.is_KroneckerDelta:
                    if set(second.args) == self.variables_set:
                        (x, _, len_x), (x, _, len_y) = self.limits
                        if len_x == len_y:
                            from sympy import Identity
                            return Identity(len_y + 1)
                        
                dependent, independent = self.simplify_matmul(self.function)
                if dependent is None:                    
                    return independent
                
                if independent is None:
                    if squeeze:
                        return self.squeeze()
                    
                    * limits, (x, *ab) = self.limits
                    if ab:
                        a, b = ab
                        if a == b:
                            function = self.function._subs(x, a)
                            if limits:
                                return self.func(function, *limits).simplify()
                            return function
                    
                    return self
                
                return MatMul(self.func(dependent, *self.limits).simplify(), independent)
            
            if second is None:
                return first

            return Mul(first, self.func(second, *self.limits).simplify(squeeze=squeeze))

        if second is None:
            if squeeze or first.shape == self.shape:
                return first
            if first.is_zero:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
            return self
        return first + self.func(second, *self.limits).simplify(squeeze=squeeze)

    def simplify_add(self, exp):
        from sympy.core.basic import Atom
        variables = tuple(x for x, *_ in self.limits[::-1])
        if isinstance(exp, Atom):
            if exp in variables:
                return None, exp
            return exp, None

        if isinstance(exp, Indexed):
            if exp.args[-len(variables):] == variables:
                if len(variables) == 1 and len(exp.indices) == 1:
                    _, *ab = self.limits[0]
                    if ab:
                        zero, b = ab
                        assert zero.is_zero
                        shape = b + 1
                        if exp.base.shape[0] != shape:
                            return exp.base[:shape], None
                    
                return exp.base[exp.indices[:-len(variables)]], None

            return None, exp

        if isinstance(exp, Add):
            argsNonSimplified = []
            argsSimplified = []
            for arg in exp.args:
                simplified, nonSimplified = self.simplify_add(arg)
                if simplified is not None:
                    argsSimplified.append(simplified)
                if nonSimplified is not None:
                    argsNonSimplified.append(nonSimplified)

            if not argsSimplified:
                argsSimplified = None
            elif len(argsSimplified) == 1:
                argsSimplified = argsSimplified[0]
            else:
                argsSimplified = Add(*argsSimplified)

            if not argsNonSimplified:
                argsNonSimplified = None
            elif len(argsNonSimplified) == 1:
                argsNonSimplified = argsNonSimplified[0]
            else:
                argsNonSimplified = Add(*argsNonSimplified)

            return argsSimplified, argsNonSimplified

        independent, dependent = exp.as_independent(*variables, as_Add=True)
        if independent == S.Zero:
            return None, dependent
        if dependent == S.Zero:
            dependent = None
        return independent, dependent

    def simplify_set(self, exp):
        from sympy.core.basic import Atom
        from sympy.tensor.indexed import Indexed
        x = tuple(x for x, *_ in self.limits)
        if isinstance(exp, Atom):
            return exp, None

        if isinstance(exp, Indexed):
            if exp.args[-len(x):] == tuple(x for x, *_ in self.limits):
                base = exp.base[exp.indices[:-len(x)]]
                for x, *ab in self.limits:
                    if len(ab) == 1:
                        return None, exp
                    if len(ab) == 2:
                        a, b = ab
                        base = base[a:b + 1]
                    else:
                        return None, exp
                return base, None

        return None, exp

    def simplify_mul(self, exp):
        x, *ab = self.limits[-1]

        from sympy.core.basic import Atom
        if isinstance(exp, Atom):
            if exp in self.variables_set:
                return None, exp
            return exp, None

        if isinstance(exp, Indexed):
            if exp.args[-1] == x:
                if not ab:
                    return exp.base[exp.indices[:-1]], None
                else:
                    a, b = ab
                    return exp.base[exp.indices[:-1]][:b + 1], None

            return None, exp
        
        if exp.is_Mul:
            argsNonSimplified = []
            argsSimplified = []
            for arg in exp.args:
                simplified, nonSimplified = self.simplify_mul(arg)
                if simplified is not None:
                    argsSimplified.append(simplified)
                if nonSimplified is not None:
                    argsNonSimplified.append(nonSimplified)

            if not argsSimplified:
                argsSimplified = None
            elif len(argsSimplified) == 1:
                argsSimplified = argsSimplified[0]
            else:
                argsSimplified = exp.func(*argsSimplified)

            if not argsNonSimplified:
                argsNonSimplified = None
            elif len(argsNonSimplified) == 1:
                argsNonSimplified = argsNonSimplified[0]
            else:
                argsNonSimplified = exp.func(*argsNonSimplified)

            return argsSimplified, argsNonSimplified

        independent, dependent = exp.as_independent(x, as_Add=False)
        if independent == S.One:
            return None, dependent
        if dependent == S.One:
            dependent = None
        return independent, dependent

    def simplify_matmul(self, exp):
        if exp.is_MatMul:
            last = self.func(exp.args[-1], self.limits[0])
            _last = last.simplify()
            if last != _last:
                independent = exp.func(*exp.args[:-1], _last).simplify()
                limits = self.limits[1:]
                if limits:
                    independent = self.func(independent, *limits)
                return None, independent
            
            first = self.func(exp.args[0], self.limits[-1])
            _first = first.simplify()
            if first != _first:
                independent = exp.func(_first, *exp.args[1:]).simplify()
                limits = self.limits[:-1]
                if limits:
                    independent = self.func(independent, *limits)
                return None, independent

            index_simplified = None
            for i, arg in enumerate(exp.args):
                _, simplified = self.simplify_matmul(arg)                
                if simplified is not None:
                    index_simplified = i 
                    break

            if index_simplified is None:
                return exp, None
            if index_simplified == 0:
                return None, exp
            
            return exp.func(*exp.args[:index_simplified]), exp.func(*exp.args[index_simplified:])
        
        independent, dependent = exp.as_independent(*self.variables, as_Add=False)
        if independent == S.One:
            return dependent, None 
        if dependent == S.One:
            dependent = None
        return dependent, independent 

    def as_Min(self):
        if isinstance(self.function, MIN) and len(self.function.limits) == 0:
            minimum = self.function
            function = minimum.function
            return minimum.func(self.func(function, *self.limits).simplify())
        return self

    def as_Sum(self):
        if self.function.is_Sum:
            sigmar = self.function
            function = sigmar.function
            return sigmar.func(self.func(function, *self.limits).simplify(), *sigmar.limits)
        return self
    
    def __getitem__(self, indices, **_):
        function = self.function
        if isinstance(indices, (tuple, list)):
            variables_set = self.variables_set
            reps = {}            
            for (x, *domain), index in zip(self.limits[::-1], indices):
                index = sympify(index)
                variables_set.remove(x)
                if x == index:
                    continue

                for v in variables_set:
                    if not index._has(v):
                        continue
                    _v = Dummy(domain=v.domain_assumed, **v.dtype.dict)
                    _index = index._subs(v, _v)
                    if _index == index:
# if the substitution fails, it means that index has v only in its domain, not in its definition or explicit expression, 
# like i = Symbol.i(domain = Interval(j, oo)), where i has j, but only in its domain, not in its definition                        
                        continue
                    index = _index
                    reps[_v] = v
                    assert not index._has(v)
                    
                function = function._subs(x, index)  # .simplify() will result in prolonged process
                if not index._has(x):                        
                    if function._has(x):
                        for var in postorder_traversal(function):
                            if var._has(x):
                                break
                        function = function._subs(var, var.definition)
                        function = function._subs(x, index)
                    assert not function._has(x)

            for k, v in reps.items():
                function = function._subs(k, v)
                    
            if len(indices) > len(self.limits):
                function = function[indices[len(self.limits):]]
            elif len(indices) < len(self.limits):
                function = self.func(function, *self.limits[:-len(indices)])
                
            return function  # .simplify() will result in prolonged process
        if isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            x, *domain = self.limits[-1]
            if len(domain) == 2:
                n = domain[1] + 1
            else:
                n = S.Infinity

            if start > 0:
                function = function.subs(x, x + start)
                stop -= start

                if stop >= n:
                    stop = n
                limits = [*self.limits]
                limits[-1] = x, 0, stop - 1
                return self.func(function, *limits)

            else:
                if stop >= n:
                    return self
                limits = [*self.limits]
                limits[-1] = x, 0, stop - 1
                return self.func(function, *limits)

        * limits, (x, *_) = self.limits
        if x != indices:
            function = function._subs(x, indices)
            if function._has(x):
                for var in postorder_traversal(function):
                    if var._has(x):
                        break
                function = function._subs(var, var.definition)
                function = function._subs(x, indices)
                assert not function._has(x)
        if limits:
            return self.func(function, *limits)
        return function

    @property
    def atomic_dtype(self):
        return self.function.atomic_dtype
    
    def limit_shape(self):
        shape = []
        for x, *ab in self.limits:
            if not ab:
                domain = self.function.domain_defined(x)
                shape.append(domain.size)
            else:
                a, b = ab
                shape.append(b - a + 1)
        shape.reverse()
        return tuple(shape)
        
    @property
    def shape(self):
        return self.limit_shape() + self.function.shape

    @property
    def cols(self):
        return self.shape[-1]

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        return self.shape[-2]

    @property
    def is_Matrix(self):
        return len(self.shape) == 2

    @property
    def is_square(self):
        return self.rows == self.cols

    def inverse(self):
        from sympy.matrices.expressions.inverse import Inverse
        return Inverse(self)

    def _eval_determinant(self):
        from sympy.concrete.products import Product
        if not self.is_square:
            return
        if self.is_upper or self.is_lower:
            i, *domain = self.limits[0]
            if len(domain) == 2:
                a, b = domain
            else:
                if not domain:
                    domain = i.domain
                elif len(domain) == 1:
                    domain = domain[0]
                assert domain.is_Interval and domain.is_integer
                a, b = domain.min(), domain.max()                

            return Product[i:a:b](self[i, i]).doit()

    @property
    def is_lower(self):
        """Check if matrix is a lower triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_lower
        True

        >>> m = Matrix(4, 3, [0, 0, 0, 2, 0, 0, 1, 4 , 0, 6, 6, 5])
        >>> m
        Matrix([
        [0, 0, 0],
        [2, 0, 0],
        [1, 4, 0],
        [6, 6, 5]])
        >>> m.is_lower
        True

        >>> from sympy.abc import x, y
        >>> m = Matrix(2, 2, [x**2 + y, y**2 + x, 0, x + y])
        >>> m
        Matrix([
        [x**2 + y, x + y**2],
        [       0,    x + y]])
        >>> m.is_lower
        False

        See Also
        ========

        is_upper
        is_diagonal
        is_lower_hessenberg
        """
        j = self.generate_free_symbol(domain=Interval(0, self.cols, right_open=True, integer=True))
        i = j.generate_free_symbol(domain=Interval(0, j, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True

        i = self.generate_free_symbol(domain=Interval(0, self.rows, right_open=True, integer=True))
        j = i.generate_free_symbol(domain=Interval(i, self.cols, left_open=True, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True

    @property
    def is_upper(self):
        """Check if matrix is an upper triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_upper
        True

        >>> m = Matrix(4, 3, [5, 1, 9, 0, 4 , 6, 0, 0, 5, 0, 0, 0])
        >>> m
        Matrix([
        [5, 1, 9],
        [0, 4, 6],
        [0, 0, 5],
        [0, 0, 0]])
        >>> m.is_upper
        True

        >>> m = Matrix(2, 3, [4, 2, 5, 6, 1, 1])
        >>> m
        Matrix([
        [4, 2, 5],
        [6, 1, 1]])
        >>> m.is_upper
        False

        See Also
        ========

        is_lower
        is_diagonal
        is_upper_hessenberg
        """
        
        j = self.generate_free_symbol(domain=Interval(0, self.cols, right_open=True, integer=True))
        i = j.generate_free_symbol(domain=Interval(j + 1, self.rows, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True
        
        i = self.generate_free_symbol(domain=Interval(0, self.rows, right_open=True, integer=True))
        j = i.generate_free_symbol(domain=Interval(0, i, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True

    def _latex(self, p):
        args = []
        for limit in self.limits:
            if len(limit) == 1:
                args.append(p._print(limit[0]))
#             elif len(limit) == 2:
#                 args.append(r"%s:%s" % (p._print(limit[0]), p._print(limit[1])))
            elif len(limit) == 3:
                if limit[1] == 0:
                    args.append(r"%s:%s" % (p._print(limit[0]), p._print(limit[2] + 1)))
                else:
                    args.append(r"%s:%s:%s" % (p._print(limit[1]), p._print(limit[0]), p._print(limit[2])))

        tex = r"[%s]" % ','.join(args)

        if isinstance(self.function, (Add, Mul)):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return '[%s](%s)' % (limits, p._print(self.function))

    def _eval_is_finite(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite

    def _eval_is_extended_real(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_real

    def _eval_is_complex(self):
        return self.function.is_complex

    def _eval_is_extended_positive(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_negative
    
    def _eval_transpose(self):
        if len(self.shape) < 2:
            return self
        if len(self.function.shape) >= 2:
            return self.func(self.function.T, *self.limits)
        if len(self.function.shape) == 1:
            return 
        limits = [*self.limits]
        limits[-1], limits[-2] = limits[-2], limits[-1]
        return self.func(self.function, *limits)

    def generate_int_limit(self, index, excludes=None, generator=None, free_symbol=None):
        if self.function.shape:
            len_shape = len(self.function.shape)
            if index < len_shape:
                return self.function.generate_int_limit(index, excludes=excludes, generator=generator, free_symbol=free_symbol)
            index -= len_shape
        limit = self.limits[index]
        if excludes:
            x, *ab = limit
            if x in excludes:
                kwargs = x.dtype.dict
                if not ab:
                    ab = x.domain.min(), x.domain.max()
                if free_symbol is not None and free_symbol not in excludes:
                    x = free_symbol
                else:
                    x = generator.generate_free_symbol(excludes, **kwargs)
                return (x, *ab)
        return limit
        
    def limits_swap(self):
        return self

    def as_Piecewise(self):
        if self.function.is_Piecewise:
            self = self.function.func(*[(self.func(e, *self.limits), c) for e, c in self.function.args])
        return self          


class UNION(Set, ExprWithLimits):
    """
    Represents a union of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Union, Interval
    >>> Union(Interval(1, 2), Interval(3, 4))
    Union(Interval(1, 2), Interval(3, 4))

    The Union constructor will always try to merge overlapping intervals,
    if possible. For example:

    >>> Union(Interval(1, 2), Interval(2, 3))
    Interval(1, 3)

    See Also
    ========

    Intersection

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Union_%28set_theory%29
    """
    
    operator = Union

    def as_image_set(self):
        try:
            if self.is_ConditionSet:
                expr, variable, base_set = self.base_set.image_set()
                from sympy import sets, Contains
                from sympy.sets.conditionset import conditionset
                condition = Contains(variable, base_set).simplify() & self.condition._subs(self.variable, expr)
                return sets.image_set(expr, variable, conditionset(variable, condition))
        except:
            ...

    @property
    def is_ConditionSet(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        x, *_ = limit
        if not isinstance(x, (Symbol, Indexed, Slice)):
            return False
        if not isinstance(self.function, FiniteSet) or len(self.function) != 1:
            return False
        element, *_ = self.function
        if element != x:
            return False
        return len(limit) > 1

    def handle_finite_sets(self, unk):
        if self.is_ConditionSet:
            from sympy.sets.conditionset import conditionset                    
            return conditionset(self.variable, self.condition, self.base_set & unk)            
        else:
            match_index = self.match_index(unk)
            if match_index is not None:
                if match_index in self.limits_dict[self.variable]:
                    return unk            
            
    def intersection_sets(self, b):
        if self.is_ConditionSet:
            from sympy.sets.conditionset import conditionset
            if b.is_ConditionSet and self.variable == b.variable:
                return conditionset(self.variable, self.condition & b.condition, self.base_set & b.base_set)
            base_set = self.variable.domain & self.base_set
            if base_set in b:
                return self                
            return conditionset(self.variable, self.condition, self.base_set & b)
    
    @property
    def condition(self):
        if self.is_ConditionSet:
            return self.limits[0][1]
        
    def condition_set(self):
        if self.is_ConditionSet:
            return self
        
    @property
    def base_set(self):
        if self.is_ConditionSet:
            limit = self.limits[0]
            if len(limit) > 2:
                return limit[2]
            return S.UniversalSet

    def doit(self, **hints):
        *limits, limit = self.limits
        i, a, b = limit
        dif = b - a
        if not dif.is_Integer:
            return self
        
        if limits:
            function = self.func(self.function, *limits)
        else:
            function = self.function
        
        return Union(*[function._subs(i, index + a) for index in range(dif + 1)])

    def as_two_terms(self):
        first, second = self.function.as_two_terms()

        if isinstance(self.function, (Intersection, Union)):
            return self.function.func(self.func(first, *self.limits), self.func(second, *self.limits))

        return self

    def swap(self):
        if not self.function.is_UNION:
            return self
        U = self.function

        return U.func(self.func(U.function, *self.limits).simplify(), *U.limits)

    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def assertion(self, given=None):
        if given is None:
            from sympy.sets.conditionset import image_set_definition
            return image_set_definition(self)
        else:
#             from sympy.sets.contains import Contains
            if len(self.limits) > 1:
                return
            limit = self.limits[0]
            if len(limit) > 2:
                return
            x, condition_set = limit
            if not condition_set.is_ConditionSet:
                return
            assert given.is_Equality
            assert given.lhs.is_Abs and given.lhs.arg == self
            n = given.rhs
            assert n.is_integer and n > 0
            assert x == condition_set.variable
            return Exists(condition_set.condition, (condition_set.variable, condition_set.base_set), given=given)

    def simplify(self, deep=False):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        if self.function.is_Intersection:
            independent = set()
            for arg in self.function.args:
                if not arg.has(*self.variables):
                    independent.add(arg)
            if independent:
                dependent = self.function._argset - independent
                function = self.function.func(*dependent)
                independent = self.function.func(*independent)
                return self.func(function, *self.limits) & independent

        if len(self.limits) != 1:
            return self
        
        if self.function.is_EmptySet:
            return self.function
        
        limit = self.limits[0]

        if len(limit) == 2:
            from sympy.core.relational import Unequality
            x, domain = limit

            if not self.function.has(x):
                return Piecewise((self.function, Unequality(Intersection(*self.limits_dict.values()), S.EmptySet).simplify()), (S.EmptySet, True)).simplify()
#                 return self.function
            
            if domain.is_FiniteSet:
                return self.finite_aggregate(x, domain)

            if domain.is_EmptySet:
                return S.EmptySet

            if domain.is_Union:
                args = []
                success = False
                for dom in domain.args:
                    arg = self.func(self.function, (x, dom)).simplify()
                    args.append(arg)
                    if not arg.is_UNION or arg.function != self.function:
                        success = True
                if success:
                    return Union(*args)

            if domain.is_Interval and domain.is_integer:
                return self.func(self.function, (x, domain.min(), domain.max()))

            if self.function.is_Complement:
                A, B = self.function.args
                if not B.has(*self.variables):
                    return self.func(A, *self.limits) - B

            if domain.is_Piecewise:
                tuples = []
                for e, c in domain.args:                    
                    tuples.append((self.func(self.function, (x, e)).simplify(), c))    
                return domain.func(*tuples)
            if domain.is_Equal:
                if domain.lhs == x:
                    return self.function._subs(x, domain.rhs)
                elif domain.rhs == x:
                    return self.function._subs(x, domain.lhs)
            if self.is_ConditionSet:
                domain = self.limits[0][1]
                if domain.is_set:                    
                    return domain
            return self

        if len(limit) > 1:
            x, a, b = limit
            if not b.is_set:
                if a == b:
                    return self.function._subs(x, a)
                domain = Interval(a, b, integer=True)
                if isinstance(self.function, Piecewise):
                    arr = self.as_multiple_terms(x, domain)
                    arr = [arr[-1]] + arr[0:-1]
                    return reduce(lambda x, y: x | y, arr).simplify()                
#                     return Union(*self.as_multiple_terms(x, domain)).simplify()

        if len(limit) == 1:
            x = limit[0]
            if self.function.is_FiniteSet:
                if len(self.function) == 1:
                    element, *_ = self.function.args
                    if element == x:
                        return x.domain

        return self

    def union_sets(self, expr):
        if expr.is_Complement:
            A, B = expr.args
            if B in self:
                return self | A
        
        from sympy import Wild
        if expr.func == self.func:
            if self.function == expr.function:
                if self.is_ConditionSet and expr.is_ConditionSet:
                    from sympy.sets.conditionset import conditionset
                    if self.variable == expr.variable :
                        if self.base_set == expr.base_set:                            
                            return conditionset(self.variable, self.condition | expr.condition, self.base_set)
                        if self.condition == expr.condition:
                            return conditionset(self.variable, self.condition, self.base_set | expr.base_set)
                else:
                    limits = self.limits_union(expr)
                    return self.func(self.function, *limits)
            else:
                finite_set = self.finite_set()
                if finite_set and finite_set.is_Slice:
                    _finite_set = expr.finite_set()
                    if _finite_set and _finite_set.is_Slice:
                        if finite_set.base == _finite_set.base:
                            start, stop = finite_set.indices
                            _start, _stop = _finite_set.indices
                            if _start == stop:
                                return UNION.construct_finite_set(finite_set.base, start, _stop, self.limits[0][0])
                            if stop == _start - 1:
                                return UNION.construct_finite_set(finite_set.base, start, _stop, self.limits[0][0]) - finite_set.base[stop].set

        if self.is_ConditionSet:
            return
        
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b + 1) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.function.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self

            elif len(args) == 1:
                domain = args[0]
                if isinstance(domain, Complement):
                    A, B = domain.args
                    if isinstance(B, FiniteSet):
                        deletes = set()
                        expr_set = S.EmptySet
                        for b in B:
                            s = self.function.subs(i, b)
                            if s in expr:
                                deletes.add(b)
                                expr_set |= s
                        if deletes:
                            deletes = FiniteSet(*deletes)
                            B -= deletes
                            expr -= expr_set
                            if B:
                                A -= B
                            this = self.func(self.function, (i, A)).simplify()
                            if expr.is_EmptySet:
                                return this
                            return this | expr
                    elif B.is_Complement:
# apply: A \ (B \ C) = (A \ B) | (A & B & C)
                        b, c = B.args
                        domain = A - b                        
#                         print(A & b & c)
                        assert A - (b - c) == (A - b) | (A & b & c)
                        expr |= self.func(self.function, (i, A & b & c)).simplify()
                        return expr | self.func(self.function, (i, domain))

    def _sympystr(self, p):
        if self.is_ConditionSet: 
            return 'ConditionSet(%s)' % ', '.join(p.doprint(arg) for arg in self.limits[0])
        
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '∪[%s](%s)' % (limits, p.doprint(self.function))
        return '∪(%s)' % p.doprint(self.function)

    def int_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 3:
                return limit

    def condition_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 2:
                return limit

    def image_set(self):
        function = self.function
        if isinstance(function, FiniteSet) and len(function) == 1:
            condition_limit = self.condition_limit()
            if condition_limit is not None:
                x, condition = condition_limit
                expr, *_ = function
                return expr, x, condition

    @classmethod
    def construct_finite_set(cls, base, start=None, stop=None, x=None):
        if start is None:
            start = S.Zero

        if stop is None:
            stop = base.shape[-1]

        if x is None:
            x = base.generate_free_symbol(start.free_symbols | stop.free_symbols, integer=True)
        return cls(base[x].set, (x, start, stop - 1))

    def finite_set(self):
        function = self.function
        limit = self.int_limit()
        if limit is None:
            return

        x, a, b = limit
        if isinstance(function, FiniteSet):
            if len(function) == 1:
                expr, *_ = function
                if isinstance(expr, Indexed):
                    if len(expr.indices) == 1:
                        base = expr.base
                    else:
                        base = expr.base[expr.indices[:-1]]
                    diff = expr.indices[-1] - x
                    if diff.has(x):
                        return
                    return base[a + diff: b + diff + 1]

    def _latex(self, p):
        finite_set = self.finite_set()
        if finite_set is not None:
            return r"\left\{*%s\right\} " % p._print(finite_set)

        image_set = self.image_set()
        if image_set is not None:
            lamda_expr, lamda_variables, base_set = image_set
            from sympy.sets.conditionset import ConditionSet
            if isinstance(base_set, ConditionSet) and lamda_variables == base_set.variable:
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition))

#             from sympy.core.containers import Tuple
            if isinstance(lamda_variables, Tuple):
                varsets = [r"%s \in %s" % (p._print(var), p._print(setv)) for var, setv in zip(lamda_variables, base_set)]
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), ', '.join(varsets))

            if base_set.is_Boolean:
                varsets = p._print(base_set)
            else:
                varsets = r"%s \in %s" % (p._print(lamda_variables), p._print(base_set))
            return r"\left\{\left. %s \right| %s \right\}" % (p._print(lamda_expr), varsets)

        if self.is_ConditionSet:
            vars_print = p._print(self.variable)
            if self.base_set is S.UniversalSet:
                return r"\left\{%s \mid %s \right\}" % (vars_print, p._print(self.condition.as_expr()))
    
            return r"\left\{%s \in %s \mid %s \right\}" % (vars_print, p._print(self.base_set), p._print(self.condition))
            
        function = self.function
        limits = self.limits

        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex = r"\bigcup_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                tex = r"\bigcup\limits_{%s \in %s} " % tuple([p._print(i) for i in limit])
            else:
                tex = r"\bigcup\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in limit])
        else:

            tex = r"\bigcup\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

        if isinstance(function, Add):
            tex += r"\left(%s\right)" % p._print(function)
        else:
            tex += p._print(function)

        return tex
    
    identity = S.EmptySet

    def _complement(self, universe):
        # DeMorgan's Law
        if self.is_ConditionSet:
            if self.base_set == universe:
                return ~self            

#         else:
#             return Intersection(s.complement(universe) for s in self.args)
    def __invert__(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        from sympy.sets.conditionset import conditionset
        return conditionset(self.variable, condition, self.base_set)

    def invert(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        from sympy.sets.conditionset import conditionset
        return conditionset(self.variable, condition, self.base_set)

    @property
    def _inf(self):
        # We use Min so that sup is meaningful in combination with symbolic
        # interval end points.
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*[set.inf for set in self.args])

    @property
    def _sup(self):
        # We use Max so that sup is meaningful in combination with symbolic
        # end points.
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*[s.sup for s in self.args])

    def _contains(self, other):
        from sympy.sets.contains import Contains
        if other.has(*self.variables):
            return
        return Exists(Contains(other, self.function), *self.limits)

    @property
    def _measure(self):
        # Measure of a union is the sum of the measures of the sets minus
        # the sum of their pairwise intersections plus the sum of their
        # triple-wise intersections minus ... etc...

        # Sets is a collection of intersections and a set of elementary
        # sets which made up those intersections (called "sos" for set of sets)
        # An example element might of this list might be:
        #    ( {A,B,C}, A.intersect(B).intersect(C) )

        # Start with just elementary sets (  ({A}, A), ({B}, B), ... )
        # Then get and subtract (  ({A,B}, (A int B), ... ) while non-zero
        sets = [(FiniteSet(s), s) for s in self.args]
        measure = 0
        parity = 1
        while sets:
            # Add up the measure of these sets and add or subtract it to total
            measure += parity * sum(inter.measure for sos, inter in sets)

            # For each intersection in sets, compute the intersection with every
            # other set not already part of the intersection.
            sets = ((sos + FiniteSet(newset), newset.intersect(intersection))
                    for sos, intersection in sets for newset in self.args
                    if newset not in sos)

            # Clear out sets with no measure
            sets = [(sos, inter) for sos, inter in sets if inter.measure != 0]

            # Clear out duplicates
            sos_list = []
            sets_list = []
            for set in sets:
                if set[0] in sos_list:
                    continue
                else:
                    sos_list.append(set[0])
                    sets_list.append(set)
            sets = sets_list

            # Flip Parity - next time subtract/add if we added/subtracted here
            parity *= -1
        return measure

    @property
    def _boundary(self):

        def boundary_of_set(i):
            """ The boundary of set i minus interior of all other sets """
            b = self.args[i].boundary
            for j, a in enumerate(self.args):
                if j != i:
                    b = b - a.interior
            return b

        return Union(*map(boundary_of_set, range(len(self.args))))

    def as_relational(self, symbol):
        """Rewrite a Union in terms of equalities and logic operators. """
        if len(self.args) == 2:
            a, b = self.args
            if (a.sup == b.inf and a.inf is S.NegativeInfinity
                    and b.sup is S.Infinity):
                return And(Ne(symbol, a.sup), symbol < b.sup, symbol > a.inf)
        return Or(*[set.as_relational(symbol) for set in self.args])

    @property
    def is_iterable(self):
        return all(arg.is_iterable for arg in self.args)

    def _eval_evalf(self, prec):
        try:
            return Union(*(set._eval_evalf(prec) for set in self.args))
        except (TypeError, ValueError, NotImplementedError):
            import sys
            raise (TypeError("Not all sets are evalf-able"),
                   None,
                   sys.exc_info()[2])

    def __iter__(self):
        import itertools

        # roundrobin recipe taken from itertools documentation:
        # https://docs.python.org/2/library/itertools.html#recipes
        def roundrobin(*iterables):
            "roundrobin('ABC', 'D', 'EF') --> A D E B F C"
            # Recipe credited to George Sakkis
            pending = len(iterables)
            if PY3:
                nexts = itertools.cycle(iter(it).__next__ for it in iterables)
            else:
                nexts = itertools.cycle(iter(it).next for it in iterables)
            while pending:
                try:
                    for next in nexts:
                        yield next()
                except StopIteration:
                    pending -= 1
                    nexts = itertools.cycle(itertools.islice(nexts, pending))

        if all(s.is_iterable for s in self.args):
            return roundrobin(*(iter(arg) for arg in self.args))
        else:
            raise TypeError("Not all constituent sets are iterable")

    @property
    def element_type(self):
        return self.function.element_type

    def _eval_Abs(self):
        if self.is_ConditionSet:
            ...

    def min(self):                        
        return MIN(self.function.min(), *self.limits)        

    def max(self):
        return MAX(self.function.max(), *self.limits)

    def _eval_is_extended_real(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_real
    
    def _eval_is_finite(self):
        if self.function.is_finite is not None:
            return self.function.is_finite

        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain, **x.assumptions0)
                assert _x.dtype == x.dtype
                function = function._subs(x, _x)
        return function.is_finite

    
class INTERSECTION(Set, ExprWithLimits):
    """
    Represents an intersection of sets as a :class:`Set`.

    """
    identity = S.UniversalSet
    operator = Intersection

    def _latex(self, p):
        function = self.function
        limits = self.limits

        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex = r"\bigcap_{%s} " % p._print(limit[0])
            else:
                tex = r"\bigcap\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in limit])
        else:

            tex = r"\bigcap\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

        if isinstance(function, Add):
            tex += r"\left(%s\right)" % p._print(function)
        else:
            tex += p._print(function)

        return tex

    @property
    def is_iterable(self):
        return any(arg.is_iterable for arg in self.args)

    def _contains(self, other):
        from sympy.sets.contains import Contains
        if other.has(*self.variables):
            return
        return ForAll(Contains(other, self.function), *self.limits)

    def __iter__(self):
        no_iter = True
        for s in self.args:
            if s.is_iterable:
                no_iter = False
                other_sets = set(self.args) - set((s,))
                other = Intersection(*other_sets, evaluate=False)
                for x in s:
                    c = sympify(other.contains(x))
                    if c is S.true:
                        yield x
                    elif c is S.false:
                        pass
                    else:
                        yield c

        if no_iter:
            raise ValueError("None of the constituent sets are iterable")

    @staticmethod
    def _handle_finite_sets(args):
        from sympy.core.logic import fuzzy_and, fuzzy_bool
        from sympy.core.compatibility import zip_longest

        fs_args, other = sift(args, lambda x: x.is_FiniteSet,
            binary=True)
        if not fs_args:
            return
        fs_args.sort(key=len)
        s = fs_args[0]
        fs_args = fs_args[1:]

        res = []
        unk = []
        for x in s:
            c = fuzzy_and(fuzzy_bool(o.contains(x))
                for o in fs_args + other)
            if c:
                res.append(x)
            elif c is None:
                unk.append(x)
            else:
                pass  # drop arg

        res = FiniteSet(
            *res, evaluate=False) if res else S.EmptySet
        if unk:
            symbolic_s_list = [x for x in s if x.has(Symbol)]
            non_symbolic_s = s - FiniteSet(
                *symbolic_s_list, evaluate=False)
            while fs_args:
                v = fs_args.pop()
                if all(i == j for i, j in zip_longest(
                        symbolic_s_list,
                        (x for x in v if x.has(Symbol)))):
                    # all the symbolic elements of `v` are the same
                    # as in `s` so remove the non-symbol containing
                    # expressions from `unk`, since they cannot be
                    # contained
                    for x in non_symbolic_s:
                        if x in unk:
                            unk.remove(x)
                else:
                    # if only a subset of elements in `s` are
                    # contained in `v` then remove them from `v`
                    # and add this as a new arg
                    contained = [x for x in symbolic_s_list
                        if sympify(v.contains(x)) is S.true]
                    if contained != symbolic_s_list:
                        other.append(
                            v - FiniteSet(
                            *contained, evaluate=False))
                    else:
                        pass  # for coverage

            other_sets = Intersection(*other)
            if not other_sets:
                return S.EmptySet  # b/c we use evaluate=False below
            elif other_sets == S.UniversalSet:
                res += FiniteSet(*unk)
            else:
                res += Intersection(
                    FiniteSet(*unk),
                    other_sets, evaluate=False)
        return res

    def as_relational(self, symbol):
        """Rewrite an Intersection in terms of equalities and logic operators"""
        return And(*[s.as_relational(symbol) for s in self.args])

    """
    precondition: this set should not be empty!
    """

    def min(self):                        
        return MAX(self.function.min(), *self.limits)        

    """
    precondition: this set should not be empty!
    """

    def max(self):
        return MIN(self.function.max(), *self.limits)

    # finiteness of intersection set is hard to evaluate
    def _eval_is_finite(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if domain is not None:
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite

    def simplify(self, deep=False):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        return self
        if self.function.is_Intersection:
            independent = set()
            for arg in self.function.args:
                if not arg.has(*self.variables):
                    independent.add(arg)
            if independent:
                dependent = self.function._argset - independent
                function = self.function.func(*dependent)
                independent = self.function.func(*independent)
                return self.func(function, *self.limits) & independent

        if len(self.limits) != 1:
            return self
        
        if self.function.is_EmptySet:
            return self.function
        
        limit = self.limits[0]

        if len(limit) == 2:
            from sympy.core.relational import Unequality
            x, domain = limit

            if not self.function.has(x):
                return Piecewise((self.function, Unequality(Intersection(*self.limits_dict.values()), S.EmptySet).simplify()), (S.EmptySet, True)).simplify()
#                 return self.function
            
            if domain.is_FiniteSet:
                return self.finite_aggregate(x, domain)

            if domain.is_EmptySet:
                return S.EmptySet

            if domain.is_Union:
                args = []
                success = False
                for dom in domain.args:
                    arg = self.func(self.function, (x, dom)).simplify()
                    args.append(arg)
                    if not arg.is_UNION or arg.function != self.function:
                        success = True
                if success:
                    return Union(*args)

            if domain.is_Interval and domain.is_integer:
                return self.func(self.function, (x, domain.min(), domain.max()))

            if self.function.is_Complement:
                A, B = self.function.args
                if not B.has(*self.variables):
                    return self.func(A, *self.limits) - B

            if domain.is_Piecewise:
                tuples = []
                for e, c in domain.args:                    
                    tuples.append((self.func(self.function, (x, e)).simplify(), c))    
                return domain.func(*tuples)
            if domain.is_Equal:
                if domain.lhs == x:
                    return self.function._subs(x, domain.rhs)
                elif domain.rhs == x:
                    return self.function._subs(x, domain.lhs)
            return self

        if len(limit) > 1:
            x, a, b = limit
            if not b.is_set:
                if a == b:
                    return self.function._subs(x, a)
                domain = Interval(a, b, integer=True)
                if isinstance(self.function, Piecewise):
                    arr = self.as_multiple_terms(x, domain)
                    arr = [arr[-1]] + arr[0:-1]
                    return reduce(lambda x, y: x | y, arr).simplify()                
#                     return Union(*self.as_multiple_terms(x, domain)).simplify()

        if len(limit) == 1:
            x = limit[0]
            if self.function.is_FiniteSet:
                if len(self.function) == 1:
                    element, *_ = self.function.args
                    if element == x:
                        return x.domain

        return self

    def intersection_sets(self, expr):
#         if expr.is_Complement:
#             A, B = expr.args
#             if B in self:
#                 return self | A
        
        from sympy import Wild
        if expr.func == self.func:
            if self.function == expr.function:
                limits = self.limits_union(expr)
                return self.func(self.function, *limits)
            else:
                return
                finite_set = self.finite_set()
                if finite_set and finite_set.is_Slice:
                    _finite_set = expr.finite_set()
                    if _finite_set and _finite_set.is_Slice:
                        if finite_set.base == _finite_set.base:
                            start, stop = finite_set.indices
                            _start, _stop = _finite_set.indices
                            if _start == stop:
                                return UNION.construct_finite_set(finite_set.base, start, _stop, self.limits[0][0])
                            if stop == _start - 1:
                                return UNION.construct_finite_set(finite_set.base, start, _stop, self.limits[0][0]) - finite_set.base[stop].set

        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b + 1) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.function.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self


class ConditionalBoolean(Boolean, ExprWithLimits):
    """A boolean object is an object for which logic operations make sense."""
    
    __slots__ = []

    _op_priority = 12.1  # higher than Relational

    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        if function.is_BooleanAtom or len(symbols) == 0:
            return function.copy(**assumptions)
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def __getitem__(self, rhs):
        return self.this.function.__getitem__(rhs)

    def __mul__(self, rhs):
        return self.this.function.__mul__(rhs)
        
    def __matmul__(self, rhs):
        return self.this.function.__matmul__(rhs)
    
    def __rmatmul__(self, rhs):
        return self.this.function.__rmatmul__(rhs)
    
    @property
    def T(self):
        return self.this.function.T
    
    def inverse(self):
        return self.this.function.inverse()

    def strip(self):
        return self.this.function.strip()

    def assertion(self):
        return self.this.function.assertion()

    def comprehension(self, operator, *limits):
        func, function = self.funcs()
        if any(op.is_Exists for op, _ in func):
            return self

        from sympy.core.relational import _Greater, _Less
        from sympy import Integral, Sum
        
        if function.is_Equality or \
        isinstance(function, (_Less, _Greater)) and operator in (Integral, Sum):
            return function.comprehension(operator, *limits, func=func)
        
        return self

    @staticmethod
    def merge_func(funcs, _funcs):
        array = []
        i = len(funcs) - 1
        j = len(_funcs) - 1
        while i >= 0 and j >= 0:
            func, limits = funcs[i]
            _func, _limits = _funcs[j]
            if func.is_Exists:
                if _func.is_ForAll:
                    array.append(funcs[i])
                else:
                    array.append((func, limits + _limits))
                    j -= 1
                i -= 1
            else:
                if _func.is_ForAll:
                    array.append(funcs[i])
                    array.append(_funcs[j])
                    i -= 1
                else:
                    array.append(_funcs[j])
                j -= 1

        array = array[::-1]
        if i >= 0:
            array = funcs[0:i + 1] + array
        elif j >= 0:
            array = _funcs[0:j + 1] + array
        return array

    def funcs(self):
        funcs = [(self.func, self.limits)]
        function = self.function
        if function.is_ConditionalBoolean:
            sub_funcs, function = function.funcs()
            funcs = sub_funcs + funcs

        return funcs, function

    def combine_clauses(self, rhs):
        func = []
        func.append([self.func, self.limits])
        return None, func, self.function, rhs

    def apply(self, axiom, *args, **kwargs):
        given = self
        if 'join' in kwargs:
            join = kwargs['join']
            del kwargs['join']
        else:
            join = True
            
        if join:
            if args and all(eq.is_Boolean for eq in args):
                for eq in args:
                    given &= eq
                return given.apply(axiom, **kwargs)
        return self.this.function.apply(axiom, *args, **kwargs)

    @property
    def reversed(self):
        return self.this.function.reversed

    @property
    def definition(self):
        return self.this.function.definition

    def as_two_terms(self):
        return self.this.function.as_two_terms()

    def limits_include(self, eq):
        variables = self.variables_set
        _variables = eq.variables_set
        for v in variables:
            if v in _variables:
                _variables.remove(v)
            elif v.is_Slice:
                for _v in _variables:
                    if _v in v:
                        _variables.remove(_v)
                        break

            else:
                continue
        return not _variables

    def __invert__(self):
        function = self.function.invert()
        return self.invert_type(function, *self.limits, counterpart=self)

    def invert(self):
        function = self.function.invert()
        return self.invert_type(function, *self.limits)

    def __and__(self, eq):
        """Overloading for & operator"""
        clue, funcs, lhs, rhs = self.combine_clauses(eq)
        function = lhs & rhs
        if not clue:
            clue = function.clue

        for func, limits in funcs[:-1]:
            function = func(function, *limits).simplify()
        func, limits = funcs[-1]

        if not clue:
            if function.equivalent is not None:
                clue = 'equivalent'
            elif function.given is not None:
                clue = 'given'

        kwargs = {}
        if clue:
            kwargs[clue] = [self, eq]

        return func(function, *limits, **kwargs).simplify()

    def bfn(self, bfn, eq):
        if self.is_Exists:
            func = self.func
            if eq.is_Exists:
                if self.limits == eq.limits:
                    limits = self.limits
                else:
                    limits = self.limits + eq.limits

                result = getattr(self.function, bfn)(eq.function)
            else:
                limits = self.limits
                result = getattr(self.function, bfn)(eq)
        else:
            if eq.is_Exists:
                if self.function.is_Exists and self.function.limits == eq.limits:
                    func = self.func
                    limits = self.limits
                    result = getattr(self.function, bfn)(eq)
                else:
                    limits = eq.limits
                    func = eq.func

                    dic = eq.limits_common(self)
                    if dic:
                        _self = self.func(self.function, *self.limits_delete(dic))

                        result = getattr(_self, bfn)(eq.function)
                        result.given = True
                    else:
                        result = self.bfn(bfn, eq.function)
            elif eq.is_ForAll:
                func = self.func
                if self.limits == eq.limits:
                    limits = self.limits
                else:
                    limits = self.limits + eq.limits
                result = getattr(self.function, bfn)(eq.function)
            else:
                func = self.func
                limits = self.limits
                result = getattr(self.function, bfn)(eq)

        equivalent = [self, eq] if eq.is_Boolean else self
        kwargs = {}
        if result.equivalent is not None:
            kwargs['equivalent'] = equivalent
        elif result.given is not None:
            kwargs['given'] = equivalent

        return func(result, *limits, **kwargs).simplify()

    @property
    def element_type(self):
        return self.function.element_type

    @property
    def lhs(self):
        return self.function.lhs

    @property
    def rhs(self):
        return self.function.rhs

    def union(self, eq):
        eq = sympify(eq)
        return self.bfn('union', eq)

    def intersect(self, eq):
        eq = sympify(eq)
        return self.bfn('intersect', eq)

    def __add__(self, eq):
        eq = sympify(eq)
        return self.bfn('__add__', eq)

    def __sub__(self, eq):
        eq = sympify(eq)
        return self.bfn('__sub__', eq)

    def __bool__(self):
        return False

    def subs(self, *args, **kwargs):
        args = tuple(map(sympify, args))
        
        def _subs_with_Equality(limits, old, new):
            _limits = []
            for limit in limits:
                x, *domain = limit
                if not domain:
                    ...
                elif len(domain) == 1:
                    domain, *_ = domain
                    if domain.is_set or not old._has(x):
                        limit = (x, domain._subs(old, new))
                else:                
                    _domain = []
                    for expr in domain:
                        _domain.append(expr._subs(old, new))
                    limit = (x, *_domain)
                _limits.append(limit)
            return _limits

        clue = None
        if len(args) == 1:
            clue, funcs, lhs, rhs = self.combine_clauses(args[0])
            function = lhs.subs(rhs).simplify()
            if not clue:
                clue = function.clue
                if not clue and function == lhs:
                    clue = 'equivalent'

            for func, limits in funcs[:-1]:
                if rhs.is_Equality:
                    limits = _subs_with_Equality(limits, *rhs.args)
                function = func(function, *limits).simplify()
            func, limits = funcs[-1]
            if rhs.is_Equality:
                limits = _subs_with_Equality(limits, *rhs.args)
        else:
            func = self.func
#             limits = self.limits
            limits = []          
            for x, *ab in self.limits:
                if x.is_Indexed or x.is_Slice:
                    indices = tuple(index._subs(*args, **kwargs) for index in x.indices)
                    if x.indices != indices:
                        x = x.func(x.base, *indices)                
                limits.append((x, *(e._subs(*args, **kwargs) for e in ab)))   
            
            if all(arg.is_Boolean for arg in args):
                function = self.function.subs(*args, **kwargs)
                clue = function.clue
            else:
                n, n0 = args
                if self.plausible:        
                    function = self.function._subs(n, n0, **kwargs)
                    if hasattr(n0, 'has') and n0.has(n):
                        eq = self.func(function, *limits, substituent=self)
                    else:
                        eq = self.func(function, *limits, given=self).simplify()
                    derivative = self.derivative
                    if derivative is None:
                        derivative = {}
                        self.derivative = derivative
        
                    if n not in derivative:
                        derivative[n] = {}
        
                    derivative[n][n0] = eq
                    return eq
                else:
                    if n.is_symbol and n0 in n.domain:
                        function = self.function._subs(n, n0, **kwargs)
                        clue = 'given'
                    else:
                        function = self.function.subs(n, n0, **kwargs)
                        if function.clue is None:
                            return self
                        clue = function.clue

        kwargs = {}

        if clue:
            if isinstance(clue, dict):
                kwargs = clue
            else:
                kwargs[clue] = [self, *args] if all(isinstance(arg, Boolean) for arg in args) else self
        if function.is_BooleanAtom:
            return function.copy(**kwargs)

        return func(function, *limits, **kwargs).simplify()

    def split(self, *args, **kwargs):
        arr = self.function.split(*args, **kwargs)
        if isinstance(arr, list):
            clue = None
            for eq in arr:
                if eq.given is None:
                    if eq.equivalent is None:
                        assert eq.imply is not None
                        if clue is None:
                            clue = 'imply'
                            self.function.derivative = None 
                        eq.imply = None
                        continue
                    if eq.equivalent.given is None:
                        print('eq.equivalent.given is None')
                    else:
                        eq.equivalent.given = None
                        eq.equivalent = None
                else:
                    eq.given = None
                    if clue is None:
                        clue = 'given'
                assert eq.equivalent is None
            kwargs = {clue: self}
            eqs = [self.func(eq, *self.limits, **kwargs).simplify() for eq in arr]
#             if self.plausible is not None:
#                 assert all(eq.plausible for eq in eqs)
            self.derivative = eqs
            return eqs
        elif isinstance(arr, tuple):
            for eq in arr:
                assert eq.parent is not None
                eq.parent = None

            return [self.func(eq, *self.limits, parent=self).simplify() for eq in arr]
        return self

    @property
    def set(self):
        return self.func(self.function.set, *self.limits, equivalent=self)

    def abs(self):
        return self.func(self.function.abs(), *self.limits, equivalent=self)

    def simplify(self, deep=False):
        if self.function.equivalent is not None:
            self.function.equivalent = None

        if self.function.given is not None:
            self.function.given = None

        if self.function.imply is not None:
            self.function.imply = None

        if self.function.func == self.func:
            exists = self.function
            return self.func(exists.function, *exists.limits + self.limits, equivalent=self).simplify()

        limits_dict = self.limits_dict
        variables = self.variables

        deletes = set()
        function = self.function
        for i, x in enumerate(variables):
            if not function.has(x):
                needsToDelete = True
                for j in range(i):
                    dependent = variables[j]
                    domain = limits_dict[dependent]
                    if domain is not None and domain.has(x) and dependent not in deletes:
                        needsToDelete = False
                        break

                if needsToDelete:
                    deletes.add(x)
            
            domain = limits_dict[x]
            if domain is not None and domain.is_FiniteSet and len(domain) == 1:
                needsToDelete = True
                deletes.add(x)
                _x, *_ = limits_dict[x].args
                function = function._subs(x, _x)
                    
        if deletes:
            limits = self.limits_delete(deletes)
            if limits:
                return self.func(function, *limits, equivalent=self).simplify()

            return function.copy(equivalent=self)

        if function.is_And or function.is_Or:
            for t in range(len(self.limits)):
                x, *domain = self.limits[t]            
                index = []
                for i, eq in enumerate(function.args):
                    if eq.has(x):
                        index.append(i)
                if len(index) == 1:
                    
                    if any(limit._has(x) for limit in self.limits[:t]):
                        continue
                    
                    index = index[0]
                    eqs = [*function.args]

                    eqs[index] = self.func(eqs[index], (x, *domain)).simplify()
                    function = function.func(*eqs)
                    limits = self.limits_delete(x)
                    return self.func(function, *limits, equivalent=self).simplify()
            limits_condition = self.limits_condition
            for i, eq in enumerate(self.function.args):
                eq &= limits_condition
                copy = False
                shrink = False
                if eq:
                    if self.function.is_Or:
                        copy = True
                    else:
                        shrink = True
                elif eq.is_BooleanFalse:
                    if self.function.is_And:
                        copy = True
                    else:
                        shrink = True

                if copy:
                    return eq.copy(equivalent=self)
                if shrink:
                    args = [*self.function.args]
                    del args[i]
                    function = self.function.func(*args)
                    return self.func(function, *self.limits, equivalent=self).simplify()

        if deep:
            function = self.function
            reps = {}
            for x, domain in limits_dict.items():
                if domain.is_set and domain.is_integer:
                    _x = x.copy(domain=domain)
                    function = function._subs(x, _x).simplify(deep=deep)
                    reps[_x] = x
            if reps:
                for _x, x in reps.items():
                    function = function._subs(_x, x)
                if function != self.function:
                    return self.func(function, *self.limits, equivalent=self).simplify()

        for x, *domain in self.limits:
            if len(domain) == 1:
                domain = domain[0]
                if domain.is_FiniteSet: 
                    return self.func(self.finite_aggregate(x, domain), *self.limits_delete(x), equivalent=self).simplify()

        for i, limit in enumerate(self.limits):
            if len(limit) != 2:
                continue
            
            e, s = limit
            if s.is_set:
                if s.is_Symbol or s.is_Indexed:
                    continue
                
                if s.is_Piecewise:
                    if s.args[-1][0].is_EmptySet:
                        s = s.func(*s.args[:-2], (s.args[-2][0], True))                            
                    
                        limits = [*self.limits]
                        limits[i] = (e, s)
                        return self.func(self.function, *limits, equivalent=self).simplify()
                    continue
                
                image_set = s.image_set()
                if image_set is not None:
                    expr, sym, base_set = image_set
                    if self.function.is_ExprWithLimits:
                        if sym in self.function.bound_symbols:
                            _sym = base_set.element_symbol(self.function.variables_set)
                            assert sym.shape == _sym.shape
                            _expr = expr.subs(sym, _sym)
                            if _expr == expr:
                                for var in postorder_traversal(expr):
                                    if var._has(sym):
                                        break
                                expr = expr._subs(var, var.definition)
                                _expr = expr._subs(sym, _sym)

                            expr = _expr
                            sym = _sym
                        assert sym not in self.function.bound_symbols
                    
                    function = self.function
                    if e != expr:
                        if sym.dtype == e.dtype:
                            _expr = expr._subs(sym, e)                        
                            if _expr != e:
                                _function = function._subs(e, expr)
                                if _function == function:
                                    return self
                                limits = self.limits_update({e : (sym, base_set)})
                                function = _function          
                            else:
                                base_set = base_set._subs(sym, e)
                                limits = self.limits_update(e, base_set)
                        else:
                            _function = function._subs(e, expr)
                            if _function == function:
                                return self
                            limits = self.limits_update({e : (sym, base_set)})
                            function = _function          
                    else:
                        limits = self.limits_update({e : (sym, base_set)})                            
                    return self.func(function, *limits, equivalent=self).simplify()
            else:  # s.dtype.is_condition: 
                if s.is_Equality:
                    if e == s.lhs:
                        y = s.rhs
                    elif e == s.rhs:
                        y = s.lhs
                    else:
                        y = None
                    if y is not None and not y.has(e):
                        function = function._subs(e, y)
                        if function.is_BooleanTrue:
                            return S.true.copy(equivalent=self) 
                        limits = self.limits_delete(e)
                        if limits:
                            return self.func(function, equivalent=self)
                        function.equivalent = self
                        return function
                if s == self.function or s.dummy_eq(self.function):  # s.invert() | self.function
                    return S.true.copy(equivalent=self)

        if self.function.is_Equality:
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                y = self.function.rhs
            elif self.function.rhs in limits_dict:
                x = self.function.rhs
                y = self.function.lhs

            if x is not None and not y.has(x):
                domain = limits_dict[x]
                if isinstance(domain, Boolean):
                    function = domain._subs(x, y)
                    limits = self.limits_delete(x)
                    if limits:
                        return self.func(function, *limits, equivalent=self)
                    function.equivalent = self
                    return function
                
        return ExprWithLimits.simplify(self, deep=deep)

    def limits_swap(self):
        this = ExprWithLimits.limits_swap(self)
        if this != self:
            this.equivalent = self
            return this
        return self

    def doit(self, **hints):
        function = self.function.doit(**hints)
        limits = []
        for limit in self.limits:
            limit = limit.doit()
            x, *ab = limit
            if x.is_Matrix:
                if ab:
                    limit = (Tuple(*x._mat), *ab)
                else:
                    for arg in x._mat:                    
                        limits.append((arg,))
                    continue
            
            limits.append(limit)
        kwargs = {}
        if self.plausible is not None:
            kwargs['equivalent'] = self
        return self.func(function, *limits, **kwargs)


class ForAll(ConditionalBoolean):
    """
    ForAll[p] q <=> !p | q
    """
    
    operator = And

    def forall(self, *limits):
        limits_dict = self.limits_dict
        if len(limits) == 1:
            x, *args = limits[0]
            if x in self.variables_set:
                x_domain = limits_dict[x]
        
                if len(args) == 2:
                    domain = Interval(*args, integer=x.is_integer)
                else:
                    domain = args[0]
                    if not domain.is_set:
                        domain = x.domain_conditioned(domain)
        
                if x_domain is None and domain is not None or domain in x_domain and x_domain not in domain:
                    limits = self.limits_update({x : domain})
                    function = self.function
                    _x = x.copy(domain=domain)
                    function = function._subs(x, _x)
                    function = function._subs(_x, x)
                    return self.func(function, *limits, given=self).simplify()
        
                return self
                
        return ConditionalBoolean.forall(self, *limits)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            return ConditionalBoolean.subs(self, *args, **kwargs)
        if len(args) != 2:
            return Expr.subs(self, *args, **kwargs)
        old, new = args
        new = sympify(new)
        forall = self.limits_dict
        if old in forall:
            domain = forall[old]
            eqs = []
            if not domain.is_set:
                domain = old.domain_conditioned(domain)

            from sympy.sets.contains import Contains
            eqs.append(Contains(new, domain).simplify().invert().simplify())

            if self.function.is_Or:
                for equation in self.function.args:
                    eqs.append(equation._subs(old, new))
            else:
                eqs.append(self.function._subs(old, new))

            limits = self.limits_delete(old)
            if limits:
                for i, (x, *ab) in enumerate(limits):
                    if ab:
                        limits[i] = (x, *(expr._subs(old, new) for expr in ab))  
                            
                return self.func(Or(*eqs), *limits, given=self)
            else:
                return Or(*eqs, given=self).simplify()

        if self.function.is_Exists:
            exists = self.function.limits_dict
            hit = False
            if old in exists:
                function = self.function.subs(old, new)
                hit = True                
            elif old.is_Slice:
                old = old.as_Matrix()
                if old.is_DenseMatrix:
                    old = Tuple(*old._mat)                    
                    if old in exists or all(sym in exists for sym in old):
                        hit = True
            if hit:
                function = self.function.subs(old, new)
                if function.clue == 'imply':                                        
                    return self.func(function, *self.limits, imply=self)
                
        return ConditionalBoolean.subs(self, *args, **kwargs)

    def as_Or(self):
        limits_dict = self.limits_dict
        from sympy.sets.contains import Contains
        eqs = []
        for var, domain in limits_dict.items():
            if domain.is_set:
                cond = Contains(var, domain).simplify()
            else:
                assert domain.is_boolean
                cond = domain
            eqs.append(cond.invert().simplify())

        if self.function.is_Or:
            eqs += self.function.args
        else:
            eqs.append(self.function)

        return Or(*eqs, equivalent=self)
        
    def simplify(self, **kwargs):
        forall = self.limits_dict

        deletes = []
        for x, domain in forall.items():
            if domain is None:
                deletes.append(x)
                continue
            
            if self.function._has(x) and domain.is_set:
                domain_defined = self.function.domain_defined(x)
                if domain_defined in domain:
                    deletes.append(x)
                domain &= domain_defined
                if domain.is_FiniteSet:
                    if len(domain) == 1:
                        x0, *_ = domain
                        function = self.function._subs(x, x0)
                        if function.is_BooleanAtom:
                            return function.copy(equivalent=self)
                        function.equivalent = self
                        return function.simplify()

        if deletes:
            limits = self.limits_delete(deletes)
            if limits:
                return self.func(self.function, *limits, equivalent=self)

            return self.function.copy(equivalent=self)

        this = self.function.simplify_forall(self)
        if this is not None:
            return this

        return ConditionalBoolean.simplify(self, **kwargs)
        
    def simplify_int_limits(self, function):
        for i, domain in self.limits_dict.items():
            if not i.is_integer or i.shape:
                continue

            i_expr = []
            patterns = []
            non_i_expr = set()
            from sympy import Wild
            _i = Wild('_i', **i.dtype.dict)
            for eq in function.args:
                if eq._has(i):
                    i_expr.append(eq)
                    patterns.append(eq._subs(i, _i))
                else:
                    non_i_expr.add(eq)

            matched_dic = {}
            for eq in non_i_expr:
                for pattern in patterns:
                    res = eq.match(pattern)
                    if not res:
                        continue

                    t, *_ = res.values()
                    if t in matched_dic:
                        matched_dic[t].add(eq)
                    else:
                        matched_dic[t] = {eq}
                    break

            new_set = set()
            for t, eqs in matched_dic.items():
                if len(eqs) != len(non_i_expr):
                    continue
                non_i_expr -= eqs
                new_set.add(t)

            if not new_set:
                continue

            eqs = i_expr + [*non_i_expr]

            limits = self.limits_update(i, domain | new_set)                
            
            function = function.func(*eqs)
            return function, limits
    
    def union_sets(self, expr):
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b + 1) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))
            elif len(args) == 1:
                domain = args[0]
                if isinstance(domain, Complement):
                    A, B = domain.args
                    if isinstance(B, FiniteSet):
                        deletes = set()
                        for b in B:
                            if self.function.subs(i, b) == expr:
                                deletes.add(b)
                        if deletes:
                            B -= FiniteSet(*deletes)
                            if B:
                                domain = Complement(A, B, evaluate=False)
                                return self.func(self.function, (i, domain))
                            domain = A
                            if isinstance(domain, Interval) and domain.is_integer:
                                return self.func(self.function, (i, domain.min(), domain.max()))
                            return self.func(self.function, (i, domain))

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])        
        return '∀［%s］(%s)' % (limits, p.doprint(self.function))

    def int_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 3:
            return limit

    def condition_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 2:
            return limit

    def _latex(self, p):
        latex = p._print(self.function)

        if all(len(limit) == 1 for limit in self.limits):
            limit = ', '.join(var.latex for var, *_ in self.limits)
        else:
            limits = []
            for limit in self.limits:
                var, *args = limit
                if len(args) == 0:
                    limit = var.latex
                elif len(args) == 1:
                    limit = var.domain_latex(args[0])
                else:
                    limit = var.domain_latex(Interval(*args, integer=True))

                limits.append(limit)

            limit = r'\substack{%s}' % '\\\\'.join(limits)

        latex = r"\forall_{%s}{%s}" % (limit, latex)
        return latex

    identity = S.BooleanTrue

    def combine_clauses(self, rhs):
        if rhs.is_Exists:
            func = []
            if self.function.is_Exists:
                dic = self.function.limits_common(rhs)
                if dic:
                    limits = self.limits_intersect(rhs)
                    limits = limits_intersect(limits, self.function.limits)
                    func.append([Exists, limits])
                    return 'given', func, self.function.function, rhs.function

            dic = self.limits_common(rhs)
            if dic:
                limits = self.limits_delete(dic)
                if limits:
                    func.append([ForAll, limits])
                func.append([Exists, rhs.limits_update(dic)])
                return 'given', func, self.function, rhs.function

            func.append([ForAll, self.limits])
            func.append([Exists, rhs.limits])
            return None, func, self.function, rhs.function

        if rhs.is_ForAll:
            func = []

            if self.function.is_Exists:
                dic = self.function.limits_common(rhs)
                if dic:
                    func.append([Exists, self.function.limits])
                    func.append([ForAll, limits_intersect(self.limits, rhs.limits_delete(dic))])
                    return None, func, self.function.function, rhs.function
                dic = self.limits_common(rhs)
                if dic:
                    rhs_limits = rhs.limits_delete(dic)
                    if rhs_limits:
                        func.append([ForAll, rhs_limits])
                    else:
                        if rhs.function.is_Exists:
                            if self.function.limits_include(rhs.function):                                 
                                clue = relationship(self, rhs)                                
                                if clue:                       
                                    func.append([Exists, self.function.limits])                                        
                                    func.append([ForAll, self.limits])
                                    return None, func, self.function.function, rhs.function.function
                            elif rhs.function.limits_include(self.function):
                                clue = relationship(self, rhs)                                
                                if clue:                       
                                    func.append([Exists, rhs.function.limits])
                                    func.append([ForAll, self.limits])
                                    return None, func, self.function.function, rhs.function.function
                                
                            return ConditionalBoolean.combine_clauses(self, rhs)                                
                        else:
                            func.append([ForAll, self.limits])
                            return None, func, self.function, rhs.function
                    func.append([Exists, self.function.limits])
                    func.append([ForAll, self.limits])
                    return None, func, self.function.function, rhs.function

            if rhs.function.is_Exists:
                dic = self.limits_common(rhs.function)
                if dic:
                    func.append([Exists, rhs.function.limits])
                    func.append([ForAll, limits_intersect(self.limits_delete(dic), rhs.limits)])
                    return 'given', func, self.function, rhs.function.function
                else:
                    if self.limits_include(rhs):                        
                        if any([limit.has(*rhs.function.variables) for limit in self.limits]):
                            dic = self.limits_common(rhs)                            
                            self_limits = self.limits_delete(dic)
                            if self_limits:
                                func.append([ForAll, self_limits])
                            func.append([Exists, rhs.function.limits])                        
                            func.append([ForAll, rhs.limits])                        
                            return 'given', func, self.function, rhs.function.function
                        else:
                            func.append([Exists, rhs.function.limits])
                            func.append([ForAll, self.limits])
                            return None, func, self.function, rhs.function.function                            
                    elif rhs.limits_include(self):
                        dic = self.limits_common(rhs)
                        self_limits = rhs.limits_delete(dic)
                        if self_limits:
                            func.append([ForAll, self_limits])
                        func.append([Exists, rhs.function.limits])
                        func.append([ForAll, limits_intersect(self.limits, rhs.limits)])
                        return 'given', func, self.function, rhs.function.function
                    else:
                        ...
            clue = {}
            limits = self.limits_intersect(rhs, clue=clue)
            func.append([ForAll, limits])
            if 'given' in clue:
                clue = 'given'
            else:
                clue = None
            return clue, func, self.function, rhs.function

        return ConditionalBoolean.combine_clauses(self, rhs)

    def as_Equal(self):
        if self.function.is_Equality:
            dic = self.limits_dict
            if len(dic) == 1:
                (x, domain), *_ = dic.items()
                if domain.is_integer and domain.is_Interval:
                    return self.function.reference((x, domain))
        return self
            
    def __and__(self, eq):
        """Overloading for & operator"""
        if eq.is_ForAll: 
            if self.function == eq.function:
                limits = self.limits_union(eq)
                return self.func(self.function, *limits, equivalent=[self, eq]).simplify()
            
            if self.limits == eq.limits:
                if self.function.is_Exists and eq.function.is_Exists:
                    if self.function.limits == eq.function.limits:
                        if self.coexist_with(eq) is not False:
                            return ForAll(Exists(self.function.function & eq.function.function, *self.function.limits), *self.limits, equivalent=[self, eq]).simplify()
                                                    
        for i, (x, *ab) in enumerate(self.limits):
            if len(ab) == 1:
                cond, *_ = ab
                if cond.is_Unequality:
                    invert = cond.invert()
                    if self.function._subs(*invert.args) == eq:
                        limits = [self.limits]
                        del limits[i]                        
                        return self.func(self.function, *limits, equivalent=[self, eq]).simplify()                        
                    
        return ConditionalBoolean.__and__(self, eq)

            
class Exists(ConditionalBoolean, ExprWithLimits):
    """
    Exists[x:A] q(x) <=> conditionset(x, q(x), A) != Ø
    """
    
    invert_type = ForAll
    operator = Or

    def exists(self, *limits):
        limits_dict = self.limits_dict
        if len(limits) == 1:
            x, *args = limits[0]
            if x in self.variables_set:
                x_domain = limits_dict[x]
        
                if len(args) == 2:
                    domain = Interval(*args, integer=x.is_integer)
                elif not args:
                    domain = None
                else:
                    domain = args[0]
                    if not domain.is_set:
                        domain = x.domain_conditioned(domain)
        
                if x_domain is not None and domain is None or x_domain in domain and domain not in x_domain:
                    limits = self.limits_update({x : domain})
                    function = self.function
                    if domain is not None:
                        _x = x.copy(domain=domain)
                        function = function._subs(x, _x)
                        function = function._subs(_x, x)
#                     else:#expand the domain to None yield a given condition!
                    return self.func(function, *limits, given=self).simplify()
        
                return self
                
        return self

    def combine_clauses(self, rhs):
        if rhs.is_Exists:
            func = []
            if rhs.function.is_ForAll:
                if rhs.function.function.is_Exists:
                    dic = self.limits_common(rhs.function.function)
                    if dic:
                        limits = self.limits_delete(dic)
                        limits = limits_intersect(rhs.limits, limits)
                        func.append([Exists, rhs.function.function.limits])
                        func.append([ForAll, rhs.function.limits])
                        func.append([Exists, limits])

                        return None, func, self.function, rhs.function.function.function
                dic = self.limits_common(rhs.function)
                if dic:
                    func.append([ForAll, rhs.function.limits])
                    limits = self.limits_delete(dic)
                    func.append([Exists, rhs.limits_intersect(limits)])
                    return 'given', func, self.function, rhs.function.function
            limits = self.limits_intersect(rhs)
            if self.variables_set == rhs.variables_set:
                clue = 'equivalent'
            else:
                clue = None
            func.append([Exists, limits])
            return clue, func, self.function, rhs.function

        if rhs.is_ForAll:
            func = []
            if rhs.function.is_Exists:
                dic = self.limits_common(rhs.function)
                if dic:
                    clue = None
                    func.append([Exists, rhs.function.limits])
                    limits = self.limits_delete(dic)

                    dic = self.limits_common(rhs)
                    if dic:
                        clue = 'given'
                        rhs_limits = rhs.limits_delete(dic)
                        if rhs_limits:
                            func.append([ForAll, rhs_limits])
                    else:
                        func.append([ForAll, rhs.limits])

                    if limits:
                        func.append([Exists, limits])

                    return clue, func, self.function, rhs.function.function

            dic = self.limits_common(rhs)
            if dic:
                rhs_limits = rhs.limits_delete(dic)
                if rhs_limits:
                    func.append([ForAll, rhs_limits])
                func.append([Exists, self.limits])
                return 'given', func, self.function, rhs.function

            func.append([ForAll, rhs.limits])
            func.append([Exists, self.limits])
            return None, func, self.function, rhs.function

        return ConditionalBoolean.combine_clauses(self, rhs)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            if 'var' in kwargs:
                assert len(args) == 0
                args = [self.limits_dict[kwargs.pop('var')]]

            if len(args) == 1:
                eq, *_ = args
                if self.function.is_And:
                    if eq in self.function.args:
                        function = self.function.subs(eq)
                        clue = function.clue
                        
                        kwargs.clear()
                        kwargs[clue] = self
                        return self.func(function, *self.limits, **kwargs).simplify()
                    
                if eq.is_Exists and eq.limits == self.limits:                    
                    if eq.is_given_by(self):
                        function = self.function.subs(eq.function)
                        return self.func(function, *self.limits, given=self).simplify()
                
            return ConditionalBoolean.subs(self, *args, **kwargs)

        if len(args) != 2:
            return Expr.subs(self, *args, **kwargs)
        
        from sympy.sets.contains import Contains
        
        old, new = args
        exists = self.limits_dict        
        if old in exists:
            domain = exists[old]
            eqs = []

            if domain is not None:
                if not domain.is_set:
                    domain = old.domain_conditioned(domain)
                if new.is_symbol:
                    domain_defined = self.function.domain_defined(new)
                    if domain_defined in domain:
                        ...
                    else:
                        eqs.append(Contains(new, domain))
                else:
                    eqs.append(Contains(new, domain))

            if self.function.is_And:
                for equation in self.function.args:
                    eqs.append(equation._subs(old, new))
            else:
                eqs.append(self.function._subs(old, new))
            limits = self.limits_delete(old)
            if new.is_symbol:
                limits = limits_intersect(limits, [(new,)])
                        
            if limits:
                return self.func(And(*eqs), *limits, imply=self).simplify()
            else:
                return And(*eqs, imply=self)
            
        if old.is_Tuple and all(sym in exists for sym in old):            
            domains = [exists[sym] for sym in old]
            eqs = []

            for domain in domains:
                if domain is not None:
                    if not domain.is_set:
                        domain = old.domain_conditioned(domain)                    
                    eqs.append(Contains(new, domain))

            if self.function.is_And:
                for equation in self.function.args:
                    eqs.append(equation._subs(old, new))
            else:
                if old.is_Tuple:
                    function = self.function
                    for i in range(len(old)):
                        function = function._subs(old[i], new[i])
                    eqs.append(function)
                else:
                    eqs.append(self.function._subs(old, new))
            limits = self.limits_delete(old)
            if new.is_symbol:
                limits = limits_intersect(limits, [(new,)])
            
            if limits:
                return self.func(And(*eqs), *limits, imply=self).simplify()
            else:
                return And(*eqs, imply=self)

        return ConditionalBoolean.subs(self, *args, **kwargs)

    def swap(self):
        if not self.function.is_ForAll:
            return self
        forall = self.function

        return forall.func(self.func(forall.function, *self.limits).simplify(), *forall.limits, given=self)

    def simplify(self, **kwargs):
        from sympy.sets.contains import Contains
        if self.function.is_Equality:
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                y = self.function.rhs
            elif self.function.rhs in limits_dict:
                x = self.function.rhs
                y = self.function.lhs

            if x is not None and not y.has(x):
                domain = limits_dict[x]
                if domain is None:
                    if len(self.limits) == 1:
#                         ...
                        return S.true.copy(equivalent=self)
                elif domain.is_set:
                    t = self.variables.index(x)
                    if not any(limit._has(x) for limit in self.limits[:t]):
                        function = Contains(y, domain)
                        if function.is_BooleanTrue:
                            return function.copy(equivalent=self)
                        limits = self.limits_delete(x)
                        if limits:
                            return self.func(function, *limits, equivalent=self)
                        function.equivalent = self
                        return function
        if self.function.is_And:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.function.args):
                if eq.is_Contains and eq.lhs in limits_dict and limits_dict[eq.lhs] is None:
                    eqs = [*self.function.args]
                    del eqs[i]                    
                    return self.func(And(*eqs), *self.limits_update(eq.lhs, eq.rhs), equivalent=self)

                if eq.is_Equality:
                    if eq.lhs in limits_dict:
                        old, new = eq.args
                    elif eq.rhs in limits_dict:
                        new, old = eq.args
                    else:
                        continue
                    
                    limits = self.limits_delete(old)
                    if any(limit._has(old) for limit in limits):
                        continue
                    
                    eqs = [*self.function.args] 
                    del eqs[i]
                    eqs = [eq._subs(old, new) for eq in eqs]
                    
                    domain = limits_dict[old]
                    if domain is None:
                        limit = (old,)
                    else:
                        limit = (old, domain)
                    eq = self.func(eq, limit).simplify()                    
                    eqs.append(eq)
                     
                    return self.func(And(*eqs), *limits, equivalent=self).simplify()
                
        return ConditionalBoolean.simplify(self, **kwargs)

    def union_sets(self, expr):
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b + 1) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))
            elif len(args) == 1:
                domain = args[0]
                if isinstance(domain, Complement):
                    A, B = domain.args
                    if isinstance(B, FiniteSet):
                        deletes = set()
                        for b in B:
                            if self.function.subs(i, b) == expr:
                                deletes.add(b)
                        if deletes:
                            B -= FiniteSet(*deletes)
                            if B:
                                domain = Complement(A, B, evaluate=False)
                                return self.func(self.function, (i, domain))
                            domain = A
                            if isinstance(domain, Interval) and domain.is_integer:
                                return self.func(self.function, (i, domain.min(), domain.max()))
                            return self.func(self.function, (i, domain))

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return '∃［%s］(%s)' % (limits, p.doprint(self.function))

    def int_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 3:
            return limit

    def condition_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 2:
            return limit

    def expr_iterable(self):
        function = self.function

        if isinstance(function, FiniteSet):
            if len(function) == 1:
                expr, *_ = function
                if expr.is_Indexed:
                    if len(expr.indices) == 1:
                        return expr.base
                    return expr.base[expr.indices[:-1]]

    def _latex(self, p):
        latex = p._print(self.function)

        if all(len(limit) == 1 for limit in self.limits):
            limit = ', '.join(var.latex for var, *_ in self.limits)
        else:
            limits = []
            for limit in self.limits:
                var, *args = limit
                if len(args) == 0:
                    limit = var.latex
                elif len(args) == 1:
                    limit = var.domain_latex(args[0])
                else:
                    limit = var.domain_latex(Interval(*args, integer=True))

                limits.append(limit)

            limit = r'\substack{%s}' % '\\\\'.join(limits)

        latex = r"\exists_{%s}{%s}" % (limit, latex)
        return latex

    identity = S.BooleanFalse

    def __and__(self, eq):
        """Overloading for & operator"""
        if eq.is_Exists:
            if self.limits == eq.limits:
                if self.coexist_with(eq) is not False:
                    return ConditionalBoolean.__and__(self, eq)
            return And(self, eq, equivalent=[self, eq])
        
        return ConditionalBoolean.__and__(self, eq)

    def as_ForAll(self):
        return ForAll(self.function, *self.limits, imply=self).simplify()

    def as_And(self):
        limits_dict = self.limits_dict
        from sympy.sets.contains import Contains
        eqs = []
        for var, domain in limits_dict.items():
            if domain.is_set:
                cond = Contains(var, domain).simplify()
            else:
                assert domain.is_boolean
                cond = domain
            eqs.append(cond)

        if self.function.is_And:
            eqs += self.function.args
        else:
            eqs.append(self.function)

        return And(*eqs, equivalent=self)

    def simplify_forall(self, forall):
        exists, self = self, forall
        if exists.function.is_ForAll:
            forall = exists.function
            dic = self.limits_common(forall)
            if dic:
                forall = forall.func(forall.function, *forall.limits_update(dic))
                exists = exists.func(forall, *exists.limits)

                return self.func(exists, *self.limits_delete(dic), equivalent=self)
        
        
ForAll.invert_type = Exists


def limits_dict(limits):
#     from sympy.sets.conditionset import conditionset
    dic = {}
    for x, *domain in limits:
        if len(domain) == 0:
            dic[x] = None
        elif len(domain) == 1:
            dic[x] = domain[0]
        else:
            if domain[1].is_set:
                dic[x] = None
            else:
                dic[x] = Interval(*domain, integer=x.is_integer)
    return dic


def limits_update(limits, *args):
    variables = [x for x, *_ in limits]

    if isinstance(limits, tuple):
        limits = [*limits]

    def assign(old, domain):
        if isinstance(domain, (tuple, list)):
            new, *domain = domain
            if len(domain) == 1:
                domain = domain[0]
        else:
            new = old

        if isinstance(domain, Interval) and (not new.is_integer) == (not domain.is_integer):
            limit = (new, domain.min(), domain.max())
        elif isinstance(domain, (tuple, list)):
            limit = (new, *domain)
        elif domain is None:
            limit = (new,)
        else:
            limit = (new, domain)

        limits[variables.index(old)] = limit

    if len(args) == 1:
        dic = args[0]
        for args in dic.items():
            assign(*args)
    else:
        assign(*args)
    return limits


def limits_delete(limits, dic):
    variables = [x for x, *_ in limits]

    if isinstance(limits, tuple):
        limits = [*limits]

    if hasattr(dic, '__len__'):
        deletes = []
        for i, x in enumerate(variables):
            if x in dic:
                deletes.append(i)
        deletes.sort(reverse=True)

        for i in deletes:
            del limits[i]
    else:
        del limits[variables.index(dic)]
    return limits


def limits_common(limits, _limits, is_or=False, clue=None):
    self_dict = limits_dict(limits)
    eq_dict = limits_dict(_limits)
    keys = eq_dict.keys() & self_dict.keys()
    dic = {}
    if keys:        
        for x in keys:
            domain = self_dict[x]
            _domain = eq_dict[x]

            if _domain is None:
                dic[x] = domain
                continue
            if _domain.is_set:
                if not domain.is_set:
                    domain = x.domain_conditioned(domain)
            else:
                if domain.is_set:
                    _domain = x.domain_conditioned(_domain)

            if is_or:
                dic[x] = domain | _domain
            else:
                if domain != _domain:
                    if clue is not None:
                        clue['given'] = True
#                     print(domain, _domain, 'not same!')
                dic[x] = domain & _domain
        return dic
    for key in self_dict:
        if not key.is_Slice:
            continue
        for _key in eq_dict:
            if not key._has(_key):
                continue
            dic[_key] = eq_dict[_key]
    return dic


def limits_intersect(limits, _limits, clue=None):
    dic = limits_common(limits, _limits, clue=clue)
    if dic:
        return limits_update(limits, dic) + limits_delete(_limits, dic)
    else:
        if type(_limits) != type(limits):
            _limits = type(limits)(_limits)
        return limits + _limits


def limits_empty(limits):
    for _, *ab in limits:
        if len(ab) != 1:
            return False
        domain, *_ = ab
        if not domain.is_EmptySet:
            return False
    return True


def limits_union(limits, _limits):
    dic = limits_common(limits, _limits, True)
    if dic:
        return limits_update(limits, dic) + limits_delete(_limits, dic)
    else:
        if type(_limits) != type(limits):
            _limits = type(limits)(_limits)
        return limits + _limits


# perform topological_sort on limits
def limits_sort(limits):
    forall = limits_dict(limits)
    G = {x: {*()} for x, *_ in limits}

    for kinder in G:
        if forall[kinder] is None:
            continue

        for parent in forall[kinder].free_symbols:
            if parent in G:
                G[parent].add(kinder)
    from sympy.utilities.iterables import topological_sort_depth_first, strongly_connected_components
    g = topological_sort_depth_first(G)

    if g is None:
        g = strongly_connected_components(G)
        for components in g:
            limit = And(*(forall[v] for v in components)).latex
            latex = r"\%s_{%s}{%s}" % (clause, limit, latex)

        return latex

    limits = []
    for x in g:
        domain = forall[x]
        if domain.is_Interval and domain.is_integer:
            limit = (x, domain.min(), domain.max())
        else:
            limit = (x, domain)
        limits.append(limit)

    return limits

'''
fundamental theory of logic:
axiom:
1:
x & x = x
2:
x | x = x
3:
x & y = y & x
4:
x | y = y | x
5:
x & y | z = (x | z) & y | z
6:
x & (y | z) = x & y | x & z
7:
x & y => x
8:
if x => y, then y | x = y
9:
!(x & y) = !x | !y
10:
x = !!x

11:
Exists[p] f = p & f
12:
ForAll[p] f = !q | f
13:
x & !x = false  
14:
true = !false 

lemma:
1:
x => x | y
from x = x | x & y = (x | y) & x
2:
if x => y, then y & x = x

prove:

if x => y, then y | x = y

(y | x) & x = y & x
y & x | x = y & x
but x  = y & x | x
hence:
x = y & x

3:
!(Exists[p] f) = ForAll[p] !f
from definition
4:
!(ForAll[p] f) = Exists[p] !f
from definition
5:
Exists[p] ForAll[q] f => ForAll[q] Exists[p] f

prove:
Exists[p] ForAll[q] f = (!q | f) & p = = !q & p | f & p = (!q | f & p) & (p | f & p)
ForAll[q] Exists[p] f = !q | (f & p)
and 
(!q | f & p) & (p | f & p) => !q | (f & p)

6:
x => x
x = x & x => x

7:
!(x | y) = !x & !y
!!(x | y) = !(!x & !y)
!!(x | y) = !!x | !!y


8:
y = x & y | !x & y
prove:
x & y | !x & y = (x | !x) & y = true & y = y
'''
