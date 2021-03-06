from sympy.core.assumptions import StdFactKB, ManagedProperties
from sympy.core.compatibility import (string_types, range, is_sequence,
    ordered, NotIterable)
from .basic import Basic, Atom
from .sympify import sympify
from .singleton import S
from .expr import Expr, AtomicExpr
from .cache import cacheit
from .function import FunctionClass
from sympy.core.logic import fuzzy_bool
from sympy.utilities.iterables import cartes
from sympy.core.containers import Tuple

import string
import re as _re
import random
from sympy.logic.boolalg import BooleanAtom

class Str(Atom):
    """
    Represents string in SymPy.

    Explanation
    ===========

    Previously, ``Symbol`` was used where string is needed in ``args`` of SymPy
    objects, e.g. denoting the name of the instance. However, since ``Symbol``
    represents mathematical scalar, this class should be used instead.

    """
    __slots__ = ('name',)

    def __new__(cls, name, **kwargs):
        if not isinstance(name, str):
            raise TypeError("name should be a string, not %s" % repr(type(name)))
        obj = Expr.__new__(cls, **kwargs)
        obj.name = name
        return obj

    def __getnewargs__(self):
        return (self.name,)

    def _hashable_content(self):
        return (self.name,)


def _filter_assumptions(kwargs):
    """Split the given dict into assumptions and non-assumptions.
    Keys are taken as assumptions if they correspond to an
    entry in ``_assume_defined``.
    """
    assumptions, nonassumptions = map(dict, sift(kwargs.items(),
        lambda i: i[0] in _assume_defined,
        binary=True))
    Symbol._sanitize(assumptions)
    return assumptions, nonassumptions


def _symbol(s, matching_symbol=None, **assumptions):
    """Return s if s is a Symbol, else if s is a string, return either
    the matching_symbol if the names are the same or else a new symbol
    with the same assumptions as the matching symbol (or the
    assumptions as provided).

    Examples
    ========

    >>> from sympy import Symbol
    >>> from sympy.core.symbol import _symbol
    >>> _symbol('y')
    y
    >>> _.is_real is None
    True
    >>> _symbol('y', real=True).is_real
    True

    >>> x = Symbol('x')
    >>> _symbol(x, real=True)
    x
    >>> _.is_real is None  # ignore attribute if s is a Symbol
    True

    Below, the variable sym has the name 'foo':

    >>> sym = Symbol('foo', real=True)

    Since 'x' is not the same as sym's name, a new symbol is created:

    >>> _symbol('x', sym).name
    'x'

    It will acquire any assumptions give:

    >>> _symbol('x', sym, real=False).is_real
    False

    Since 'foo' is the same as sym's name, sym is returned

    >>> _symbol('foo', sym)
    foo

    Any assumptions given are ignored:

    >>> _symbol('foo', sym, real=False).is_real
    True

    NB: the symbol here may not be the same as a symbol with the same
    name defined elsewhere as a result of different assumptions.

    See Also
    ========

    sympy.core.symbol.Symbol

    """
    if isinstance(s, string_types):
        if matching_symbol and matching_symbol.name == s:
            return matching_symbol
        return Symbol(s, **assumptions)
    elif isinstance(s, Symbol):
        return s
    else:
        raise ValueError('symbol must be string for symbol name or Symbol')


def _uniquely_named_symbol(xname, exprs=(), compare=str, modify=None, **assumptions):
    """Return a symbol which, when printed, will have a name unique
    from any other already in the expressions given. The name is made
    unique by prepending underscores (default) but this can be
    customized with the keyword 'modify'.

    Parameters
    ==========

        xname : a string or a Symbol (when symbol xname <- str(xname))
        compare : a single arg function that takes a symbol and returns
            a string to be compared with xname (the default is the str
            function which indicates how the name will look when it
            is printed, e.g. this includes underscores that appear on
            Dummy symbols)
        modify : a single arg function that changes its string argument
            in some way (the default is to preppend underscores)

    Examples
    ========

    >>> from sympy.core.symbol import _uniquely_named_symbol as usym, Dummy
    >>> from sympy.abc import x
    >>> usym('x', x)
    _x
    """
    default = None
    if is_sequence(xname):
        xname, default = xname
    x = str(xname)
    if not exprs:
        return _symbol(x, default, **assumptions)
    if not is_sequence(exprs):
        exprs = [exprs]
    syms = set().union(*[e.free_symbols for e in exprs])
    if modify is None:
        modify = lambda s: '_' + s
    while any(x == compare(s) for s in syms):
        x = modify(x)
    return _symbol(x, default, **assumptions)


class Symbol(ManagedProperties):

    def __getattr__(self, attr):        
        if attr.startswith('_'):             
#             println('skipping attr', attr, color=Foreground.RED)
            return
#         from sympy import println, Foreground
#         println('generating attr:', attr, color=Foreground.RED)

# replacement regex:        
# \bvar\((([^()]+(?:\([^()]*(?:\([^()]*(?:\([^()]*(?:\([^()]*\)[^()]*)*\)[^()]*)*\)[^()]*)*\)))+[^()]*)\).(\w+)
# Symbol.\3(\1)
        def __new__(**kwargs):
            return Symbol(attr, **kwargs)

        return __new__


class Symbol(AtomicExpr, NotIterable, metaclass=Symbol):  # @DuplicatedSignature
# class Symbol(AtomicExpr, Boolean):
    """
    Assumptions:
       commutative = True

    You can override the default assumptions in the constructor:

    >>> from sympy import symbols
    >>> A,B = symbols('A,B', commutative = False)
    >>> bool(A*B != B*A)
    True
    >>> bool(A*B*2 == 2*A*B) == True # multiplication by scalars is commutative
    True

    """

    is_comparable = False

    __slots__ = ['name']

    is_symbol = True
    _explicit_class_assumptions = {}
    
    def intersection_sets(self, b):
        if b.is_ConditionSet:
            from sympy.sets.conditionset import conditionset
            return conditionset(b.variable, b.condition, b.base_set & self)

    @staticmethod
    def process_slice(index, self_start, self_stop):
        start, stop = index.start, index.stop
        if start is None:
            start = self_start            
        if stop is None:
            stop = self_stop

        if stop == self_stop:
            if start == self_start:
                return
            if start < 0:
                start = self_stop + start
            mid = start            
        elif start == self_start:
            if stop < 0:
                stop = self_stop + stop
            mid = stop 
        else:
            return start, stop
        
        return mid        

    def slice(self, index, self_start, self_stop):
        from sympy import Concatenate
        mid = Symbol.process_slice(index, self_start, self_stop)
        if mid is None:
            return self
        assert mid > self_start, "mid > self_start => %s" % (mid > self_start) 
        assert mid < self_stop, "mid < self_stop => %s" % (mid < self_stop)
        
        if isinstance(mid, tuple):
            start, stop = mid
            assert start < stop, "start < stop => %s" % (start < stop)
            return Concatenate(self[self_start: start], self[start: stop], self[stop:self_stop])
        
        return Concatenate(self[self_start:mid], self[mid:self_stop])
        
    def bisect(self, indices):
        from sympy import Union
        if self.is_set:
            return Union(self & indices, self - indices, evaluate=False)
        if self.shape:            
            return self.slice(indices, 0, self.shape[0])
            
        return self

    # performing other in self
    def __contains__(self, other):        
        contains = self.contains_with_subset(other)
        if contains is not None:
            return contains
        
        if self.definition is not None:
            return other in self.definition

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        return self == other

    def structure_eq(self, other):
        from sympy.tensor.indexed import Slice, Indexed
        if isinstance(other, (Symbol, Indexed, Slice)):
            return self.shape == other.shape
        return False

    @staticmethod
    def process_assumptions(assumptions, integer):
        domain = assumptions.get('domain')
        if domain is not None:
            from sympy import Interval
            if isinstance(domain, list):
                domain = Interval(*domain, integer=integer)
               
            if isinstance(domain, set):
                assumptions['domain'] = sympify(domain) 
            elif domain.is_Interval:
                if domain.start is S.NegativeInfinity:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        assumptions['real'] = True
                    elif domain.stop is S.Zero:
                        assumptions.pop('domain')
                        if domain.right_open:
                            assumptions['negative'] = True
                        else:
                            assumptions['nonpositive'] = True
                elif domain.start is S.Zero:
                    if domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        if domain.left_open:
                            assumptions['positive'] = True
                        else:
                            assumptions['nonnegative'] = True
                elif domain.start is S.One:
                    if integer and not domain.left_open and domain.stop is S.Infinity:
                        assumptions.pop('domain')
                        assumptions['positive'] = True
                elif domain.stop is S.NegativeOne:
                    if integer and not domain.right_open and domain.start is S.NegativeInfinity:
                        assumptions.pop('domain')
                        assumptions['negative'] = True
            
            if 'domain' not in assumptions:
                assumptions['integer'] = integer            
        
    def copy(self, **kwargs):
        if not kwargs:
            return self
        integer, rational, real, shape, dtype = self.is_integer, self.is_rational, self.is_real, self.shape, self.element_type
        kwargs['integer'] = integer
        kwargs['rational'] = rational
        kwargs['real'] = real
        kwargs['shape'] = shape if shape else None
        kwargs['dtype'] = dtype
        
        self.process_assumptions(kwargs, integer)
        return self.func(self.name, **kwargs)
    
    @property
    def unbounded(self):
        if self.is_bounded:
            return self.copy(domain=None)
        return self

    @property
    def _diff_wrt(self):
        """Allow derivatives wrt Symbols.

        Examples
        ========

            >>> from sympy import Symbol
            >>> x = Symbol('x')
            >>> x._diff_wrt
            True
        """
        return True

    def image_set(self):
        definition = self.definition
        if definition is None:
            return None
        return definition.image_set()

    def condition_set(self):
        definition = self.definition
        if definition is None:
            return
        return definition.condition_set()

    @staticmethod
    def _sanitize(assumptions, obj=None):
        """Remove None, covert values to bool, check commutativity *in place*.
        """

        # be strict about commutativity: cannot be None
        is_commutative = fuzzy_bool(assumptions.get('commutative', True))
        if is_commutative is None:
            whose = '%s ' % obj.__name__ if obj else ''
            raise ValueError(
                '%scommutativity must be True or False.' % whose)

        # sanitize other assumptions so 1 -> True and 0 -> False
        for key in list(assumptions.keys()):
            from collections import defaultdict
            from sympy.utilities.exceptions import SymPyDeprecationWarning
            keymap = defaultdict(lambda: None)
            keymap.update({'bounded': 'finite', 'unbounded': 'infinite', 'infinitesimal': 'zero'})
            if keymap[key]:
                SymPyDeprecationWarning(
                    feature="%s assumption" % key,
                    useinstead="%s" % keymap[key],
                    issue=8071,
                    deprecated_since_version="0.7.6").warn()
                assumptions[keymap[key]] = assumptions[key]
                assumptions.pop(key)
                key = keymap[key]

            v = assumptions[key]
            if v is None:
                assumptions.pop(key)
                continue

            if key not in ('domain', 'definition', 'dtype', 'shape', 'distribution'):
                assumptions[key] = bool(v)
        integer = assumptions.get('integer')
        if integer is None:
            domain = assumptions.get('domain')
            if domain is None:
                return
            else:
                integer = domain.is_integer
                         
        Symbol.process_assumptions(assumptions, integer)
        
    def __new__(cls, name, **assumptions):
        """Symbols are identified by name and assumptions::

        >>> from sympy import Symbol
        >>> Symbol("x") == Symbol("x")
        True
        >>> Symbol("x", real=True) == Symbol("x", real=False)
        False

        """
        cls._sanitize(assumptions, cls)
        return Symbol.__xnew__(cls, name, **assumptions)
#         return Symbol.__xnew_cached_(cls, name, **assumptions)

    def __new_stage2__(cls, name, **assumptions):
        if not isinstance(name, string_types):
            raise TypeError("name should be a string, not %s" % repr(type(name)))

        obj = Expr.__new__(cls)
        obj.name = name
        # TODO: Issue #8873: Forcing the commutative assumption here means
        # later code such as ``srepr()`` cannot tell whether the user
        # specified ``commutative=True`` or omitted it.  To workaround this,
        # we keep a copy of the assumptions dict, then create the StdFactKB,
        # and finally overwrite its ``._generator`` with the dict copy.  This
        # is a bit of a hack because we assume StdFactKB merely copies the
        # given dict as ``._generator``, but future modification might, e.g.,
        # compute a minimal equivalent assumption set.
        tmp_asm_copy = assumptions.copy()

        # be strict about commutativity
        is_commutative = fuzzy_bool(assumptions.get('commutative', True))
        if 'domain' in assumptions:
            domain = assumptions['domain']
            if isinstance(domain, list):
                from sympy import Interval
                assumptions['domain'] = Interval(*domain, integer=assumptions.get('integer'))
                
        assumptions['commutative'] = is_commutative
        obj._assumptions = StdFactKB(assumptions)
        obj._assumptions._generator = tmp_asm_copy  # Issue #8873
        return obj

    __xnew__ = staticmethod(
        __new_stage2__)  # never cached (e.g. dummy)
    __xnew_cached_ = staticmethod(
        cacheit(__new_stage2__))  # symbols are always cached

    def __getnewargs__(self):
        return (self.name,)

    def __getstate__(self):
        return {'_assumptions': self._assumptions}

    def _hashable_content(self):
        # Note: user-specified assumptions not hashed, just derived ones
        hashable_content = [*self.assumptions_hashable().items()]
        hashable_content.sort()
        return (self.name,) + tuple(hashable_content)

    def _ask(self, fact):
        a = Expr._ask(self, fact)
        if a is True:
            self._assumptions[fact] = S.true
        elif a is False:
            self._assumptions[fact] = S.false
        return a

    def _eval_subs(self, old, new):
        from sympy.core.power import Pow
        if old.is_Power:
            return Pow(self, S.One, evaluate=False)._eval_subs(old, new)

    @property
    def assumptions0(self):
        return dict((key, value) for key, value in self._assumptions.items() if value is not None)

    def assumptions_hashable(self):
        return {k : v for k, v in self._assumptions.items() if v is not None and not isinstance(v, BooleanAtom) }

    @cacheit
    def sort_key(self, order=None):
        if self.domain_assumed:
            # to distinguish symbols with the same literals but different domains
            args = (str(self), True)
        else:
            args = (str(self),)
        return self.class_key(), (1, args), S.One.sort_key(), S.One

    def as_dummy(self):
        return Dummy(self.name)

    def as_real_imag(self, deep=True, **hints):
        from sympy import im, re
        if hints.get('ignore') == self:
            return None
        else:
            return (re(self), im(self))

    def _sage_(self):
        import sage.all as sage
        return sage.var(self.name)

    def is_constant(self, *wrt, **flags):
        if not wrt:
            return False
        return not self in wrt

    @property
    def free_symbols(self):
        return {self}

    binary_symbols = free_symbols  # in this case, not always

    def as_set(self):
        return S.UniversalSet

    @property
    def is_unbounded(self):
        return not self.is_bounded
        
    @property
    def is_bounded(self):
        if 'domain' in self._assumptions:
            return True
        if 'shape' in self._assumptions:
            return False
        if  'positive' in self._assumptions and self.is_positive is not None:
            return True
        if  'negative' in self._assumptions and self.is_negative is not None:
            return True
        if  'nonpositive' in self._assumptions and self.is_nonpositive is not None:
            return True
        if  'nonnegative' in self._assumptions and self.is_nonnegative is not None:
            return True

    @property
    def domain_assumed(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain']
        if 'distribution' in self._assumptions:
            return self._assumptions['distribution'].domain
        
    @property
    def domain_bounded(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain']
        from sympy import Interval, oo
        if self.is_positive:
            return Interval(0, oo, left_open=True, integer=self.is_integer)
        if self.is_negative:
            return Interval(-oo, 0, right_open=True, integer=self.is_integer)
        if self.is_nonpositive:
            return Interval(-oo, 0, integer=self.is_integer)
        if self.is_nonnegative:
            return Interval(0, oo, integer=self.is_integer)
        
    @property
    def domain(self):
        from sympy.sets.sets import Interval

        if 'domain' in self._assumptions:
            domain = self._assumptions['domain']
            if self.is_integer and domain.is_Interval and not domain.is_integer:
                return domain.copy(integer=True)
            return domain
         
        if self.is_set:
            return S.UniversalSet
        
        if 'distribution' in self._assumptions:
            return self._assumptions['distribution'].domain
                         
        domain = Interval(**self.assumptions0) if self.is_extended_real else S.Complexes
        shape = self.shape
        if not shape:
            return domain
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(domain, *shape)        

    @property
    def definition(self):
        if 'definition' in self._assumptions:
            return self._assumptions['definition']        

    def domain_nonzero(self, x):
        if self == x:
            return x.domain - {0}
        return Expr.domain_nonzero(self, x)

    @property
    def is_set(self):
        if self.shape:
            return False
        if 'dtype' in self._assumptions:
            dtype = self._assumptions['dtype']
            if dtype is not None:
                return True
        definition = self.definition
        if definition is not None:
            return definition.is_set
        return False

    @property
    def atomic_dtype(self):
        definition = self.definition
        if definition is not None:
            return definition.atomic_dtype

        if 'dtype' in self._assumptions:
            return self._assumptions['dtype'].set
        
        assumptions = {}
        if self._assumptions.get('positive'):
            assumptions['positive'] = True
        elif self._assumptions.get('nonnegative'):
            assumptions['nonnegative'] = True
        elif self._assumptions.get('negative'):
            assumptions['negative'] = True
        elif self._assumptions.get('nonpositive'):
            assumptions['nonpositive'] = True
             
        if self.is_integer:
            return dtype.integer(**assumptions)
        elif self.is_rational:
            return dtype.rational  # (**self.assumptions0)
        elif self.is_real:
            return dtype.real  # (**self.assumptions0)
        elif self.is_complex:
            return dtype.complex  # (**self.assumptions0)
        else:
            return dtype.real  # (**self.assumptions0)

    def _has(self, pattern):
        """Helper for .has()"""
        if Expr._has(self, pattern):
            return True

        from sympy.core.assumptions import ManagedProperties

        if not isinstance(pattern, (FunctionClass, ManagedProperties)):
            if 'definition' in self._assumptions:
                definition = self._assumptions['definition']
                return definition._has(pattern)

            if 'domain' in self._assumptions:
                from sympy.core.numbers import Infinity, NegativeInfinity
                if isinstance(pattern, (Infinity, NegativeInfinity)):  # excludes oo, -oo, because these are not variables;
                    return False
                domain = self._assumptions['domain']
                return domain._has(pattern)

        return False

    @property
    def element_type(self):
        if 'dtype' in self._assumptions:
            return self._assumptions['dtype']
        definition = self.definition
        if definition is not None:
            return definition.element_type        

    def element_symbol(self, excludes=set(), free_symbol=None):
        element_type = self.element_type
        if element_type is None:
            return

        return self.generate_free_symbol(excludes=excludes, free_symbol=free_symbol, **element_type.dict)

    def assertion(self, reverse=False):
        definition = self.definition
        from sympy.sets import sets
        if definition is None:
            return sets.Set.static_assertion(self)
        
        if definition.is_ConditionSet:
            sym = definition.variable
            condition = definition.condition
            from sympy.concrete.expr_with_limits import ForAll
            if not definition.base_set.is_UniversalSet:
                from sympy.sets.contains import Contains
                condition &= Contains(sym, definition.base_set)
            return ForAll(condition, (sym, self))

        from sympy.sets.conditionset import image_set_definition
        return image_set_definition(self, reverse=reverse)

    def equality_defined(self):
        from sympy import Mul, Equality
        from sympy.concrete.expr_with_limits import LAMBDA
        if isinstance(self.definition, LAMBDA):
            return Equality(self[tuple(var for var, *_ in self.definition.limits[::-1])], self.definition.function, evaluate=False)
        elif isinstance(self.definition, Mul):
            args = []
            ref = None
            for arg in self.definition.args:
                if isinstance(arg, LAMBDA):
                    assert ref is None
                    ref = arg
                else:
                    args.append(arg)
            if ref is not None:
                (var, *_), *_ = ref.limits
                return Equality(self[var], Mul(*args) * ref.function, evaluate=False)
        
        return Equality(self, self.definition, evaluate=False)
        
    @property
    def shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
        
        if 'domain' in self._assumptions:
            domain = self._assumptions['domain']
            dtype = domain.element_type
            shape = dtype.shape
        elif self.definition is not None:
            shape = self.definition.shape            
        else:
            shape = ()
            
        # dangerous codes? possibly make the hashable content obselete!
#         if shape:            
#             self._assumptions['shape'] = shape
            
        return shape        

    @property
    def cols(self):
        if self.shape:
            return self.shape[-1]
        return 1

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        if len(self.shape) > 1:
            return self.shape[-2]
        return 1

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices, **kw_args):
        from sympy.tensor.indexed import Indexed, Slice
        if is_sequence(indices):
            # Special case needed because M[*my_tuple] is a syntax error.
#             if self.shape and len(self.shape) != len(indices):
#                 raise IndexException("Rank mismatch.")
            if len(indices) == 2 and isinstance(indices[0], slice):
                start, stop = indices[0].start, indices[0].stop
                if start is None:
                    if stop is None:
                        return self.T[indices[1]]
                    start = 0
                if stop is None:
                    stop = self.shape[0]                
                return self[start:stop].T[indices[1]]
            return Indexed(self, *indices, **kw_args)
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            if start == stop - 1:
                return Indexed(self, start, **kw_args)
            if start == 0 and stop == self.shape[-1]:
                return self
            return Slice(self, indices, **kw_args)
        else:
            if self.definition is not None:
                from sympy.concrete.expr_with_limits import LAMBDA
                if isinstance(self.definition, LAMBDA):
                    ref = self.definition
                    from sympy.stats.rv import RandomSymbol
                    if len(ref.limits) == 1 and isinstance(ref.function, RandomSymbol):
                        return ref[indices]
            boolean = indices < self.shape[0]
            assert boolean is True or not boolean.is_BooleanFalse
            return Indexed(self, indices, **kw_args)

    def has_match(self, exp):
        if exp == self:
            return True 
        
        from sympy.matrices.expressions.matexpr import MatrixElement
        if isinstance(exp, MatrixElement) and exp.parent == self:
            return True
        
        if exp.is_Indexed and exp.base == self:
            return True
        if exp.is_Slice and exp.base == self:
            index_start, index_stop = exp.indices
            start, stop = 0, self.shape[-1]

            if index_stop <= start:
                return False  # index < start
            if index_start >= stop:
                return False  # index >= stop
    # it is possible for them to be equal!
            return True
        return False
    
    def _eval_transpose(self):
        if len(self.shape) < 2:
            return self

    greek_letters = {'Alpha': 'Α',
                     'ALPHA': 'Α',
                     'alpha': 'α',
                     'Beta': 'Β',
                     'BETA': 'Β',
                     'beta': 'β',
                     'Gamma': 'Γ',
                     'GAMMA': 'Γ',
                     'gamma': 'γ',
                     'Delta': 'Δ',
                     'DELTA': 'Δ',
                     'delta': 'δ',
                     'Epsilon': 'Ε',
                     'EPSILON': 'Ε',
                     'epsilon': 'ε',
                     'Zeta': 'Ζ',
                     'ZETA': 'Ζ',
                     'zeta': 'ζ',
                     'Eta': 'Η',
                     'ETA': 'Η',
                     'eta': 'η',
                     'Theta': 'Θ',
                     'THETA': 'Θ',
                     'theta': 'θ',
                     'Iota': 'Ι',
                     'IOTA': 'Ι',
                     'iota': 'ι',
                     'Kappa': 'Κ',
                     'KAPPA': 'Κ',
                     'kappa': 'κ',
                     'Lambda': 'Λ',
                     'LAMBDA': 'Λ',
                     'lamda': 'λ',
                     'lambda': 'λ',
                     'Mu': 'Μ',
                     'MU': 'Μ',
                     'mu': 'μ',
                     'Nu': 'Ν',
                     'NU': 'Ν',
                     'nu': 'ν',
                     'Xi': 'Ξ',
                     'XI': 'Ξ',
                     'xi': 'ξ',
                     'Omicron': 'Ο',
                     'OMICRON': 'Ο',
                     'omicron': 'ο',
                     'Pi': 'Π',
                     'PI': 'Π',
                     'pi': 'π',
                     'Rho': 'Ρ',
                     'RHO': 'Ρ',
                     'rho': 'ρ',
                     'Sigma': 'Σ',
                     'SIGMA': 'Σ',
                     'sigma': 'σ',
                     'Tau': 'Τ',
                     'TAU': 'Τ',
                     'tau': 'τ',
                     'Upsilon': 'Υ',
                     'UPSILON': 'Υ',
                     'upsilon': 'υ',
                     'Phi': 'Φ',
                     'PHI': 'Φ',
                     'phi': 'φ',
                     'Chi': 'Χ',
                     'CHI': 'Χ',
                     'chi': 'χ',
                     'Psi': 'Ψ',
                     'PSI': 'Ψ',
                     'psi': 'ψ',
                     'Omega': 'Ω',
                     'OMEGA': 'Ω',
                     'omega': 'ω'}
            
    @staticmethod
    def sympystr(name):
        m = _re.compile("([a-zA-Z]+)(?:(\d+)|_(\w+))?").fullmatch(name)
        if m: 
            x = m.group(1)
            if x in Symbol.greek_letters:
                x = Symbol.greek_letters[x]
            d = m.group(2)
            if d is not None:
                x += d
            else:
                a = m.group(3)
                if a is not None:
                    if a in Symbol.greek_letters:
                        a = Symbol.greek_letters[a]
                    x += '_' + a                    
                
            return x
        return name  
        
    def _sympystr(self, _):   
        return Symbol.sympystr(self.name)     

    def _latex(self, p):
        if self in p._settings['symbol_names']:
            return p._settings['symbol_names'][self]

        name = self.name
        name = name.replace('_quote', "'")
        result = p._deal_with_super_sub(name) if '\\' not in name else name

        if self.is_random:
            return r'{\color{red} {%s}}' % result
        
        if self.domain_assumed:
            return r"{\color{green} {%s}}" % result
        
        if self.definition is not None:
            return r"{\color{blue} {%s}}" % result

        return result

    def _eval_is_extended_positive(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_extended_positive
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_extended_positive        
        if 'distribution' in self._assumptions:
            distribution = self._assumptions['distribution']
            return distribution.is_extended_positive
                 
    def _eval_is_extended_negative(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_extended_negative
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_extended_negative
        if 'distribution' in self._assumptions:
            distribution = self._assumptions['distribution']
            return distribution.is_extended_negative

    def _eval_is_zero(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_zero
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_zero
        if 'distribution' in self._assumptions:
            distribution = self._assumptions['distribution']
            return distribution.is_zero
        
    def _eval_is_extended_real(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_extended_real
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_extended_real
        if 'distribution' in self._assumptions:
            distribution = self._assumptions['distribution']
            return distribution.is_extended_real
        if 'dtype' in self._assumptions:
            dtype = self._assumptions['dtype']
            return dtype.is_real

    def _eval_is_finite(self):
        if 'domain' in self._assumptions:
            domain_assumed = self.domain_assumed
            if domain_assumed.is_Interval:                
                return True
            if domain_assumed.is_FiniteSet:
                if all(arg.is_finite for arg in domain_assumed.args):
                    return True
                if all(arg.is_infinite for arg in domain_assumed.args):
                    return False
            return
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_finite
        return True

    def _eval_is_integer(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_integer
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_integer        
        if 'distribution' in self._assumptions:
            distribution = self._assumptions['distribution']
            return distribution.is_integer
        if 'dtype' in self._assumptions:
            dtype = self._assumptions['dtype']            
            return dtype.is_integer

    def _eval_is_rational(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_rational
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_rational        
        if 'distribution' in self._assumptions:
            distribution = self._assumptions['distribution']
            return distribution.is_rational
        if 'dtype' in self._assumptions:
            dtype = self._assumptions['dtype']            
            return dtype.is_rational

    def _eval_is_complex(self):
        if 'domain' in self._assumptions:
            return True
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_complex        
        return True

    def _eval_is_algebraic(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_algebraic
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_algebraic
    
    def _eval_is_hermitian(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_hermitian
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_hermitian
    
    def _eval_is_imaginary(self):
        if 'domain' in self._assumptions:
            return self._assumptions['domain'].is_imaginary
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_imaginary

    def _eval_is_random(self):
        if 'distribution' in self._assumptions:
            return True
        if 'definition' in self._assumptions:
            return self._assumptions['definition'].is_random
            
    @property
    def distribution(self):
        if 'distribution' in self._assumptions:         
            return self._assumptions['distribution']
    
    @property
    def is_given(self):
        return self._assumptions.get('given')
    
    def __hash__(self):
        return super(Symbol, self).__hash__()        

    def __eq__(self, other):
        try:
            other = sympify(other)
            if type(other) != type(self):
                return False
        except :
            return False
        
        if self.name != other.name:
            return False
        
        nonboolean_attributes = {'domain', 'definition', 'shape', 'dtype', 'distribution'}
        for attr in nonboolean_attributes:
            if (attr in self._assumptions) != (attr in other._assumptions):
                return False
        
        for fact in self._assumptions.keys() & other._assumptions.keys():
            if self._assumptions[fact] != other._assumptions[fact]:
                return False

        for fact in self._assumptions.keys() - other._assumptions.keys() - nonboolean_attributes:            
            if other._ask(fact) != self._assumptions[fact]:
#                 other._mhash = None
                return False
            
        for fact in other._assumptions.keys() - self._assumptions.keys() - nonboolean_attributes:
            if self._ask(fact) != other._assumptions[fact]:
#                 self._mhash = None
                return False

        return True

    def to_wolfram(self, global_variables):
        from wolframclient.language import wlexpr
        global_variables.add(self)
        return wlexpr(self.name)
      
    def is_independent_of(self, y, **kwargs):
        from sympy.core.relational import Equality
        return Equality(self | y, self, **kwargs)

    def as_boolean(self):
        if self.is_random:
            from sympy import Equality
            from sympy.stats.rv import pspace
            return Equality(self, pspace(self).symbol)

    def _subs(self, old, new, **hints):
        """Substitutes an expression old -> new. when self is a Symbol
        """        
        assert old != new
        
        if old.is_Symbol:
            if self == old:
                return new
            if not old.shape and not old.is_set and hints.get('symbol') is not False:
                element_type = self.element_type
                if element_type:        
                    _element_type = element_type._subs(old, new)
                    if _element_type is not element_type:
                        assumptions = self.assumptions_hashable()
                        assumptions['dtype'] = _element_type
                        return self.func(r"{%s}_{%s}" % (self.name, str(new)), **assumptions)
                    
                definition = self.definition
                if definition is not None:
                    if definition.is_LAMBDA:
                        for var in definition.variables:
                            if old == var:
                                return self
                            if old in var.free_symbols:
                                return self
                    _definition = definition._subs(old, new)
                    if _definition != definition:
                        assumptions = self.assumptions_hashable()
                        assumptions['definition'] = _definition
                        if 'shape' in assumptions:
                            del assumptions['shape']
        # rgb values for colors                 
        #                 https://www.917118.com/tool/color_3.html
        # darkyellow                
                        return self.func(r"{\color{ADAD00} %s}" % self.name, **assumptions)
        return self
        
class Dummy(Symbol):
    """Dummy symbols are each unique, even if they have the same name:

    >>> from sympy import Dummy
    >>> Dummy("x") == Dummy("x")
    False

    If a name is not supplied then a string value of an internal count will be
    used. This is useful when a temporary variable is needed and the name
    of the variable used in the expression is not important.

    >>> Dummy() #doctest: +SKIP
    _Dummy_10

    """

    # In the rare event that a Dummy object needs to be recreated, both the
    # `name` and `dummy_index` should be passed.  This is used by `srepr` for
    # example:
    # >>> d1 = Dummy()
    # >>> d2 = eval(srepr(d1))
    # >>> d2 == d1
    # True
    #
    # If a new session is started between `srepr` and `eval`, there is a very
    # small chance that `d2` will be equal to a previously-created Dummy.

    _count = 0
    _prng = random.Random()
    _base_dummy_index = _prng.randint(10 ** 6, 9 * 10 ** 6)

    __slots__ = ['dummy_index']

    def __new__(cls, name=None, dummy_index=None, **assumptions):
        if dummy_index is not None:
            assert name is not None, "If you specify a dummy_index, you must also provide a name"

        if name is None:
            name = "Dummy_" + str(Dummy._count)

        if dummy_index is None:
            dummy_index = Dummy._base_dummy_index + Dummy._count
            Dummy._count += 1

        cls._sanitize(assumptions, cls)
        obj = Symbol.__xnew__(cls, name, **assumptions)

        obj.dummy_index = dummy_index

        return obj

    def __getstate__(self):
        return {'_assumptions': self._assumptions, 'dummy_index': self.dummy_index}

    @cacheit
    def sort_key(self, order=None):
        return self.class_key(), (
            2, (str(self), self.dummy_index)), S.One.sort_key(), S.One

    def _hashable_content(self):
        return Symbol._hashable_content(self) + (self.dummy_index,)


class Wild(Symbol):
    """
    A Wild symbol matches anything, or anything
    without whatever is explicitly excluded.

    Parameters
    ==========

    name : str
        Name of the Wild instance.
    exclude : iterable, optional
        Instances in ``exclude`` will not be matched.
    properties : iterable of functions, optional
        Functions, each taking an expressions as input
        and returns a ``bool``. All functions in ``properties``
        need to return ``True`` in order for the Wild instance
        to match the expression.

    Examples
    ========

    >>> from sympy import Wild, WildFunction, cos, pi
    >>> from sympy.abc import x, y, z
    >>> a = Wild('a')
    >>> x.match(a)
    {a_: x}
    >>> pi.match(a)
    {a_: pi}
    >>> (3*x**2).match(a*x)
    {a_: 3*x}
    >>> cos(x).match(a)
    {a_: cos(x)}
    >>> b = Wild('b', exclude=[x])
    >>> (3*x**2).match(b*x)
    >>> b.match(a)
    {a_: b_}
    >>> A = WildFunction('A')
    >>> A.match(a)
    {a_: A_}

    Tips
    ====

    When using Wild, be sure to use the exclude
    keyword to make the pattern more precise.
    Without the exclude pattern, you may get matches
    that are technically correct, but not what you
    wanted. For example, using the above without
    exclude:

    >>> from sympy import symbols
    >>> a, b = symbols('a b', cls=Wild)
    >>> (2 + 3*y).match(a*x + b*y)
    {a_: 2/x, b_: 3}

    This is technically correct, because
    (2/x)*x + 3*y == 2 + 3*y, but you probably
    wanted it to not match at all. The issue is that
    you really didn't want a and b to include x and y,
    and the exclude parameter lets you specify exactly
    this.  With the exclude parameter, the pattern will
    not match.

    >>> a = Wild('a', exclude=[x, y])
    >>> b = Wild('b', exclude=[x, y])
    >>> (2 + 3*y).match(a*x + b*y)

    Exclude also helps remove ambiguity from matches.

    >>> E = 2*x**3*y*z
    >>> a, b = symbols('a b', cls=Wild)
    >>> E.match(a*b)
    {a_: 2*y*z, b_: x**3}
    >>> a = Wild('a', exclude=[x, y])
    >>> E.match(a*b)
    {a_: z, b_: 2*x**3*y}
    >>> a = Wild('a', exclude=[x, y, z])
    >>> E.match(a*b)
    {a_: 2, b_: x**3*y*z}

    Wild also accepts a ``properties`` parameter:

    >>> a = Wild('a', properties=[lambda k: k.is_Integer])
    >>> E.match(a*b)
    {a_: 2, b_: x**3*y*z}

    """

    __slots__ = ['exclude', 'properties']

    def __new__(cls, name, exclude=(), properties=(), **assumptions):
        exclude = tuple([sympify(x) for x in exclude])
        properties = tuple(properties)
        cls._sanitize(assumptions, cls)
        return Wild.__xnew__(cls, name, exclude, properties, **assumptions)

    def __getnewargs__(self):
        return (self.name, self.exclude, self.properties)

    @staticmethod
    @cacheit
    def __xnew__(cls, name, exclude, properties, **assumptions):
        obj = Symbol.__xnew__(cls, name, **assumptions)
        obj.exclude = exclude
        obj.properties = properties
        return obj

    def _hashable_content(self):
        return super(Wild, self)._hashable_content() + (self.exclude, self.properties)

    # TODO add check against another Wild
    def matches(self, expr, repl_dict={}, old=False):
        if any(expr.has(x) for x in self.exclude):
            return None
        if any(not f(expr) for f in self.properties):
            return None
        repl_dict = repl_dict.copy()
        repl_dict[self] = expr
        return repl_dict

    @property
    def shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
        return ()


_range = _re.compile('([0-9]*:[0-9]+|[a-zA-Z]?:[a-zA-Z])')


def symbols(names, **args):
    r"""
    Transform strings into instances of :class:`Symbol` class.

    :func:`symbols` function returns a sequence of symbols with names taken
    from ``names`` argument, which can be a comma or whitespace delimited
    string, or a sequence of strings::

        >>> from sympy import symbols, Function

        >>> x, y, z = symbols('x,y,z')
        >>> a, b, c = symbols('a b c')

    The type of output is dependent on the properties of input arguments::

        >>> symbols('x')
        x
        >>> symbols('x,')
        (x,)
        >>> symbols('x,y')
        (x, y)
        >>> symbols(('a', 'b', 'c'))
        (a, b, c)
        >>> symbols(['a', 'b', 'c'])
        [a, b, c]
        >>> symbols({'a', 'b', 'c'})
        {a, b, c}

    If an iterable container is needed for a single symbol, set the ``seq``
    argument to ``True`` or terminate the symbol name with a comma::

        >>> symbols('x', seq=True)
        (x,)

    To reduce typing, range syntax is supported to create indexed symbols.
    Ranges are indicated by a colon and the type of range is determined by
    the character to the right of the colon. If the character is a digit
    then all contiguous digits to the left are taken as the nonnegative
    starting value (or 0 if there is no digit left of the colon) and all
    contiguous digits to the right are taken as 1 greater than the ending
    value::

        >>> symbols('x:10')
        (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9)

        >>> symbols('x5:10')
        (x5, x6, x7, x8, x9)
        >>> symbols('x5(:2)')
        (x50, x51)

        >>> symbols('x5:10,y:5')
        (x5, x6, x7, x8, x9, y0, y1, y2, y3, y4)

        >>> symbols(('x5:10', 'y:5'))
        ((x5, x6, x7, x8, x9), (y0, y1, y2, y3, y4))

    If the character to the right of the colon is a letter, then the single
    letter to the left (or 'a' if there is none) is taken as the start
    and all characters in the lexicographic range *through* the letter to
    the right are used as the range::

        >>> symbols('x:z')
        (x, y, z)
        >>> symbols('x:c')  # null range
        ()
        >>> symbols('x(:c)')
        (xa, xb, xc)

        >>> symbols(':c')
        (a, b, c)

        >>> symbols('a:d, x:z')
        (a, b, c, d, x, y, z)

        >>> symbols(('a:d', 'x:z'))
        ((a, b, c, d), (x, y, z))

    Multiple ranges are supported; contiguous numerical ranges should be
    separated by parentheses to disambiguate the ending number of one
    range from the starting number of the next::

        >>> symbols('x:2(1:3)')
        (x01, x02, x11, x12)
        >>> symbols(':3:2')  # parsing is from left to right
        (00, 01, 10, 11, 20, 21)

    Only one pair of parentheses surrounding ranges are removed, so to
    include parentheses around ranges, double them. And to include spaces,
    commas, or colons, escape them with a backslash::

        >>> symbols('x((a:b))')
        (x(a), x(b))
        >>> symbols(r'x(:1\,:2)')  # or r'x((:1)\,(:2))'
        (x(0,0), x(0,1))

    All newly created symbols have assumptions set according to ``args``::

        >>> a = symbols('a', integer=True)
        >>> a.is_integer
        True

        >>> x, y, z = symbols('x,y,z', real=True)
        >>> x.is_real and y.is_real and z.is_real
        True

    Despite its name, :func:`symbols` can create symbol-like objects like
    instances of Function or Wild classes. To achieve this, set ``cls``
    keyword argument to the desired type::

        >>> symbols('f,g,h', cls=Function)
        (f, g, h)

        >>> type(_[0])
        <class 'sympy.core.function.UndefinedFunction'>

    """
    result = []

    if isinstance(names, string_types):
        marker = 0
        literals = [r'\,', r'\:', r'\ ']
        for i in range(len(literals)):
            lit = literals.pop(0)
            if lit in names:
                while chr(marker) in names:
                    marker += 1
                lit_char = chr(marker)
                marker += 1
                names = names.replace(lit, lit_char)
                literals.append((lit_char, lit[1:]))

        def literal(s):
            if literals:
                for c, l in literals:
                    s = s.replace(c, l)
            return s

        names = names.strip()
        as_seq = names.endswith(',')
        if as_seq:
            names = names[:-1].rstrip()
        if not names:
            raise ValueError('no symbols given')

        # split on commas
        names = [n.strip() for n in names.split(',')]
        if not all(n for n in names):
            raise ValueError('missing symbol between commas')
        # split on spaces
        for i in range(len(names) - 1, -1, -1):
            names[i: i + 1] = names[i].split()

        cls = args.pop('cls', Symbol)
        seq = args.pop('seq', as_seq)

        for name in names:
            if not name:
                raise ValueError('missing symbol')

            if ':' not in name:
                symbol = cls(literal(name), **args)
                result.append(symbol)
                continue

            split = _range.split(name)
            # remove 1 layer of bounding parentheses around ranges
            for i in range(len(split) - 1):
                if i and ':' in split[i] and split[i] != ':' and \
                        split[i - 1].endswith('(') and \
                        split[i + 1].startswith(')'):
                    split[i - 1] = split[i - 1][:-1]
                    split[i + 1] = split[i + 1][1:]
            for i, s in enumerate(split):
                if ':' in s:
                    if s[-1].endswith(':'):
                        raise ValueError('missing end range')
                    a, b = s.split(':')
                    if b[-1] in string.digits:
                        a = 0 if not a else int(a)
                        b = int(b)
                        split[i] = [str(c) for c in range(a, b)]
                    else:
                        a = a or 'a'
                        split[i] = [string.ascii_letters[c] for c in range(
                            string.ascii_letters.index(a),
                            string.ascii_letters.index(b) + 1)]  # inclusive
                    if not split[i]:
                        break
                else:
                    split[i] = [s]
            else:
                seq = True
                if len(split) == 1:
                    names = split[0]
                else:
                    names = [''.join(s) for s in cartes(*split)]
                if literals:
                    result.extend([cls(literal(s), **args) for s in names])
                else:
                    result.extend([cls(s, **args) for s in names])

        if not seq and len(result) <= 1:
            if not result:
                return ()
            return result[0]

        return tuple(result)
    else:
        for name in names:
            result.append(symbols(name, **args))

        return type(names)(result)


def var(names, **args):
    """
    Create symbols and inject them into the global namespace.

    This calls :func:`symbols` with the same arguments and puts the results
    into the *global* namespace. It's recommended not to use :func:`var` in
    library code, where :func:`symbols` has to be used::

    Examples
    ========

    >>> from sympy import Symbol

    >>> var('x')
    x
    >>> x
    x

    >>> var('a,ab,abc')
    (a, ab, abc)
    >>> abc
    abc

    >>> var('x,y', real=True)
    (x, y)
    >>> x.is_real and y.is_real
    True

    See :func:`symbol` documentation for more details on what kinds of
    arguments can be passed to :func:`var`.

    """

    def traverse(symbols, frame):
        """Recursively inject symbols to the global namespace. """
        for symbol in symbols:
            if isinstance(symbol, Basic):
                frame.f_globals[symbol.name] = symbol
            elif isinstance(symbol, FunctionClass):
                frame.f_globals[symbol.__name__] = symbol
            else:
                traverse(symbol, frame)

    from inspect import currentframe
    frame = currentframe().f_back

    try:
        syms = symbols(names, **args)

        if syms is not None:
            if isinstance(syms, Basic):
                frame.f_globals[syms.name] = syms
            elif isinstance(syms, FunctionClass):
                frame.f_globals[syms.__name__] = syms
            else:
                traverse(syms, frame)
    finally:
        del frame  # break cyclic dependencies as stated in inspect docs

    return syms


def disambiguate(*iter):
    """
    Return a Tuple containing the passed expressions with symbols
    that appear the same when printed replaced with numerically
    subscripted symbols, and all Dummy symbols replaced with Symbols.

    Parameters
    ==========

    iter: list of symbols or expressions.

    Examples
    ========

    >>> from sympy.core.symbol import disambiguate
    >>> from sympy import Dummy, Symbol, Tuple
    >>> from sympy.abc import y

    >>> tup = Symbol('_x'), Dummy('x'), Dummy('x')
    >>> disambiguate(*tup)
    (x_2, x, x_1)

    >>> eqs = Tuple(Symbol('x')/y, Dummy('x')/y)
    >>> disambiguate(*eqs)
    (x_1/y, x/y)

    >>> ix = Symbol('x', integer=True)
    >>> vx = Symbol('x')
    >>> disambiguate(vx + ix)
    (x + x_1,)

    To make your own mapping of symbols to use, pass only the free symbols
    of the expressions and create a dictionary:

    >>> free = eqs.free_symbols
    >>> mapping = dict(zip(free, disambiguate(*free)))
    >>> eqs.xreplace(mapping)
    (x_1/y, x/y)

    """
    new_iter = Tuple(*iter)
    key = lambda x:tuple(sorted(x.assumptions0.items()))
    syms = ordered(new_iter.free_symbols, keys=key)
    mapping = {}
    for s in syms:
        mapping.setdefault(str(s).lstrip('_'), []).append(s)
    reps = {}
    for k in mapping:
        # the first or only symbol doesn't get subscripted but make
        # sure that it's a Symbol, not a Dummy
        mapk0 = Symbol("%s" % (k), **mapping[k][0].assumptions0)
        if mapping[k][0] != mapk0:
            reps[mapping[k][0]] = mapk0
        # the others get subscripts (and are made into Symbols)
        skip = 0
        for i in range(1, len(mapping[k])):
            while True:
                name = "%s_%i" % (k, i + skip)
                if name not in mapping:
                    break
                skip += 1
            ki = mapping[k][i]
            reps[ki] = Symbol(name, **ki.assumptions0)
    return new_iter.xreplace(reps)


class Dtype:
    is_set = False
    is_condition = False
    is_integer = False
    is_rational = False
    is_real = False
    is_complex = False
    
    def as_Set(self):
        ...
        
    def __hash__(self):
        return hash(type(self).__name__)

    @property
    def integer(self):
        return DtypeInteger()

    @property
    def natural(self):
        return self.integer(nonnegative=True)

    @property
    def real(self):
        return DtypeReal()

    @property
    def rational(self):
        return DtypeRational()

    @property
    def complex(self):
        return DtypeComplex()

    @property
    def set(self):
        return DtypeSet(self)

    @property
    def condition(self):
        return DtypeCondition()

    @property
    def distribution(self):
        return DtypeDistribution()

    def __mul__(self, length):
        if isinstance(length, (tuple, Tuple, list)):
            if not length:
                return self
            if len(length) == 1:
                return DtypeVector(self, length[0])
            return DtypeMatrix(self, length)
        return DtypeVector(self, length)

    def __contains__(self, x):
        if isinstance(x, Symbol):
            for key, value in self.dict.items():
                x._assumptions[key] = value
            return True
        return isinstance(x, type(self))

    @property
    def shape(self):
        return ()

    def _has(self, pattern):
        return False

    def _subs(self, old, new, **hints):
        return self
    
    def __repr__(self):
        return str(self)
    
    def __str__(self, head):
        return '%s(%s)' % (head, ', '.join(("%s=%s" % args for args in self.assumptions.items())))


class DtypeComplex(Dtype):
    is_complex = True

    def as_Set(self):
        return S.Complexes        

    def __str__(self):
        return 'complex'
    
    @property
    def dict(self):
        return {'complex' : True}

    def __eq__(self, other):
        return isinstance(other, DtypeComplex)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeComplexConditional(**kwargs)


class DtypeComplexConditional(DtypeComplex):
    
    def as_Set(self):
        return S.Complexes

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'complex')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['complex'] = True        
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeComplexConditional)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeCondition(Dtype):
    is_condition = True
    
    def __str__(self):
        return 'condition'
    
    @property
    def dict(self):
        return {'condition' : True}

    def __eq__(self, other):
        return isinstance(other, DtypeCondition)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeDistribution(Dtype):
    is_distribution = True
    
    def __str__(self):
        return 'distribution'
    
    @property
    def dict(self):
        return {'random' : True}

    def __eq__(self, other):
        return isinstance(other, DtypeDistribution)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeReal(DtypeComplex):
    
    is_real = True
    
    def as_Set(self):
        return S.Reals

    def __str__(self):
        return 'real'
    
    @property
    def dict(self):
        return {'real' : True}

    def __eq__(self, other):
        return isinstance(other, DtypeReal)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeRealConditional(**kwargs)


class DtypeRealConditional(DtypeReal):

    def as_Set(self):
        if self.assumptions.get('positive') is True:
            ...
        return S.Reals

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'real')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['real'] = True        
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeRealConditional)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeRational(DtypeReal):

    is_rational = True

    def as_Set(self):
        return S.Rationals

    def __str__(self):
        return 'rational'
    
    @property
    def dict(self):
        return {'rational' : True}

    def __eq__(self, other):
        return isinstance(other, DtypeRational)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeRationalConditional(**kwargs)


class DtypeRationalConditional(DtypeRational):

    def as_Set(self):
        if self.assumptions.get('positive') is True:
            ...
        return S.Rationals

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'rational')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['rational'] = True        
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeRationalConditional)

    def __hash__(self):
        return hash(type(self).__name__)


class DtypeInteger(DtypeRational):
    
    is_integer = True
    
    def as_Set(self):
        from sympy.sets import Integers
        return Integers

    def __str__(self):
        return 'integer'
    
    @property
    def dict(self):
        return {'integer' : True}

    def __eq__(self, other):
        return isinstance(other, DtypeInteger)

    def __hash__(self):
        return hash(type(self).__name__)

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeIntegerConditional(**kwargs)

        
class DtypeIntegerConditional(DtypeInteger):

    def as_Set(self):
        positive = self.assumptions.get('positive')
        if positive:
            from sympy.sets import PositiveIntegers
            return PositiveIntegers
        nonnegative = self.assumptions.get('nonnegative')
        if nonnegative:
            from sympy.sets import NonnegativeIntegers
            return NonnegativeIntegers
        
        from sympy.sets.sets import Interval
        negative = self.assumptions.get('negative')
        if negative:
            return Interval(S.NegativeInfinity, -1, integer=True)
        nonpositive = self.assumptions.get('nonpositive')
        if nonpositive:
            return Interval(S.NegativeInfinity, 0, integer=True)

        even = self.assumptions.get('even')
        odd = self.assumptions.get('odd')
        
        
        if even:
            return Interval(0, S.PositiveInfinity, step=2, integer=True) | Interval(S.NegativeInfinity, 0, step=2, integer=True)
        if odd:
            return Interval(1, S.PositiveInfinity, step=2, integer=True) | Interval(S.NegativeInfinity, -1, step=2, integer=True)
        return S.Integers

    def __init__(self, **assumptions):
        self.assumptions = assumptions
    
    def __str__(self):
        return Dtype.__str__(self, 'integer')
    
    @property
    def dict(self):
        assumptions = {**self.assumptions}
        assumptions['integer'] = True        
        return assumptions

    def __eq__(self, other):
        return isinstance(other, DtypeIntegerConditional)

    def __hash__(self):
        return hash(type(self).__name__)

    def __add__(self, start):
        from sympy import Interval, oo
        if 'nonnegative' in self.assumptions:
            if start != 0:
                return self.integer(domain=Interval(start, oo, integer=True)) 
            return self
        return self.integer


class DtypeSet(Dtype):
    is_set = True
    
    def __init__(self, dtype):
        self.dtype = dtype

    def __str__(self):
        return '{%s}' % self.dtype
    
    @property
    def dict(self):
        return {'dtype' : self.dtype}

    def __eq__(self, other):
        return isinstance(other, DtypeSet) and self.dtype == other.dtype

    def __hash__(self):
        return hash((type(self).__name__, self.dtype))
    
    def _has(self, pattern):
        return self.dtype._has(pattern)
    
    def _subs(self, old, new, **hints):
        dtype = self.dtype._subs(old, new)
        if dtype is not self.dtype:
            return type(self)(dtype)
        return self


class DtypeVector(Dtype):
    
    @property
    def is_integer(self):
        return self.dtype.is_integer
    
    @property
    def is_rational(self):
        return self.dtype.is_rational

    @property
    def is_real(self):
        return self.dtype.is_real

    @property
    def is_complex(self):
        return self.dtype.is_complex
    
    def as_Set(self):
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(self.dtype.as_Set(), self.length)

    def __init__(self, dtype, length, **kwargs):
        self.dtype = dtype
        self.length = length
        self.assumptions = kwargs

    def __str__(self):
        if self.assumptions:
            return '%s[%s]%s' % (self.dtype, self.length, str(self.assumptions))
        return '%s[%s]' % (self.dtype, self.length)
    
    def __getitem__(self, indices):
        if isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            return DtypeVector(self.dtype, stop - start)
        else:
            return self.dtype

    def __mul__(self, length):
        if isinstance(length, (tuple, Tuple, list)):
            return DtypeMatrix(self.dtype, (self.length,) + length)
        return DtypeMatrix(self, (self.length, length))

    @property
    def shape(self):
        return (self.length,)

    @property
    def dict(self):
        dic = self.dtype.dict
        dic['shape'] = (self.length,)
        dic.update(self.assumptions)
        return dic

    def __eq__(self, other):
        return isinstance(other, DtypeVector) and self.length == other.length and self.dtype == other.dtype

    def __hash__(self):
        return hash((type(self).__name__, self.dtype, self.length))

    def __call__(self, **kwargs):
        if not kwargs:
            return self
        return DtypeVector(self.dtype, self.length, **kwargs)

    def _has(self, pattern):
        return self.length._has(pattern)

    def _subs(self, old, new, **hints):
        hit = False
        dtype = self.dtype._subs(old, new)
        if dtype is not self.dtype:
            hit = True
            
        length = self.length._subs(old, new)
        if length != self.length:
            hit = True            
        
        if hit:
            return type(self)(dtype, length)
        
        return self


class DtypeMatrix(Dtype):
    
    @property
    def is_integer(self):
        return self.dtype.is_integer
    
    @property
    def is_rational(self):
        return self.dtype.is_rational

    @property
    def is_real(self):
        return self.dtype.is_real

    @property
    def is_complex(self):
        return self.dtype.is_complex

    def as_Set(self):
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(self.dtype.as_Set(), *self.lengths)

    def __init__(self, dtype, shape):
        self.dtype = dtype
        self.lengths = tuple(shape)

    @property
    def shape(self):
        return self.lengths

    def __str__(self):
        return '%s[%s]' % (self.dtype, ', '.join(str(length) for length in self.shape))
    
    def __getitem__(self, indices):
        if isinstance(indices, (tuple, Tuple, list)):
            diff = len(self.shape) - len(indices)
            if diff == 0:
                return self.dtype
            if diff == 1:
                return DtypeVector(self.dtype, self.shape[-1])
            return DtypeMatrix(self.dtype, self.shape[-diff:])
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            shape = (stop - start,) + self.shape[1:]
            return Basic.__new__(DtypeMatrix, self.dtype, shape)
        else:
            diff = len(self.shape) - 1
            if diff == 1:
                return DtypeVector(self.dtype, self.shape[-1])
            return DtypeMatrix(self.dtype, self.shape[-diff:])

    def __mul__(self, length):
        if isinstance(length, (tuple, Tuple, list)):
            length = tuple(length)
            return DtypeMatrix(self.dtype, self.shape + length)
        return Basic.__new__(DtypeMatrix, self, self.shape + (length,))

    @property
    def dict(self):
        dic = self.dtype.dict
        dic['shape'] = self.shape
        return dic

    def __eq__(self, other):
        return isinstance(other, DtypeMatrix) and self.shape == other.shape and self.dtype == other.dtype

    def __hash__(self):
        return hash((type(self).__name__, self.dtype, self.shape))
    
    def transpose(self):         
        return DtypeMatrix(self.dtype, (*self.lengths[:-2], self.lengths[-1], self.lengths[-2]))


dtype = Dtype()
