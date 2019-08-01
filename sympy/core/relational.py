from __future__ import print_function, division

from sympy.utilities.exceptions import SymPyDeprecationWarning
from .add import _unevaluated_Add, Add
from .basic import S
from .compatibility import ordered
from .expr import Expr
from .evalf import EvalfMixin
from .sympify import _sympify
from .evaluate import global_evaluate

from sympy.logic.boolalg import Boolean, BooleanAtom, process_options

__all__ = (
    'Rel', 'Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge',
    'Relational', 'Equality', 'Unequality', 'StrictLessThan', 'LessThan',
    'StrictGreaterThan', 'GreaterThan',
)

# Note, see issue 4986.  Ideally, we wouldn't want to subclass both Boolean
# and Expr.


def _canonical(cond):
    # return a condition in which all relationals are canonical
    reps = {r: r.canonical for r in cond.atoms(Relational)}
    return cond.xreplace(reps)
    # XXX: AttributeError was being caught here but it wasn't triggered by any of
    # the tests so I've removed it...


class Relational(Boolean, Expr, EvalfMixin):
    """Base class for all relation types.

    Subclasses of Relational should generally be instantiated directly, but
    Relational can be instantiated with a valid `rop` value to dispatch to
    the appropriate subclass.

    Parameters
    ==========
    rop : str or None
        Indicates what subclass to instantiate.  Valid values can be found
        in the keys of Relational.ValidRelationalOperator.

    Examples
    ========

    >>> from sympy import Rel
    >>> from sympy.abc import x, y
    >>> Rel(y, x + x**2, '==')
    Eq(y, x**2 + x)

    """
    __slots__ = []

    is_Relational = True

    _op_priority = 12
    # ValidRelationOperator - Defined below, because the necessary classes
    #   have not yet been defined

    def __new__(cls, lhs, rhs, rop=None, **assumptions):
        # If called by a subclass, do nothing special and pass on to Expr.
        if cls is not Relational:
            return Expr.__new__(cls, lhs, rhs, **assumptions)
        # If called directly with an operator, look up the subclass
        # corresponding to that operator and delegate to it
        try:
            cls = cls.ValidRelationOperator[rop]
            rv = cls(lhs, rhs, **assumptions)
            # /// drop when Py2 is no longer supported
            # validate that Booleans are not being used in a relational
            # other than Eq/Ne;
            if isinstance(rv, (Eq, Ne)):
                pass
            elif isinstance(rv, Relational):  # could it be otherwise?
                from sympy.core.symbol import Symbol
                from sympy.logic.boolalg import Boolean
                for a in rv.args:
                    if isinstance(a, Symbol):
                        continue
                    if isinstance(a, Boolean):
                        from sympy.utilities.misc import filldedent
                        raise TypeError(filldedent('''
                            A Boolean argument can only be used in
                            Eq and Ne; all other relationals expect
                            real expressions.
                        '''))
            # \\\
            return rv
        except KeyError:
            raise ValueError(
                "Invalid relational operator symbol: %r" % rop)

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.reversed
        Eq(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        assumptions = self._assumptions.copy()
        assumptions['equivalent'] = self if self.plausible else None

        return Relational.__new__(reversed_ops.get(self.func, self.func), b, a, **assumptions)

    def __neg__(self):
        """Return the relationship with signs reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.neg
        Eq(-x, -1)
        >>> x < 1
        x < 1
        >>> _.neg
        -x > -1
        """

        return reversed_ops[self.func](-self.lhs, -self.rhs, equivalent=self if self.plausible else None)

    @property
    def negated(self):
        """Return the negated relationship.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.negated
        Ne(x, 1)
        >>> x < 1
        x < 1
        >>> _.negated
        x >= 1

        Notes
        =====

        This works more or less identical to ``~``/``Not``. The difference is
        that ``negated`` returns the relationship even if `evaluate=False`.
        Hence, this is useful in code when checking for e.g. negated relations
        to exisiting ones as it will not be affected by the `evaluate` flag.

        """
        for_clause = self.for_clause
        with_clause = self.with_clause
        plausible = self.plausible

        if plausible is False:
            plausible = None
        elif plausible is None:
            plausible = False

        ops = {Eq: Ne, Ge: Lt, Gt: Le, Le: Gt, Lt: Ge, Ne: Eq}
        # If there ever will be new Relational subclasses, the following line
        # will work until it is properly sorted out
        # return ops.get(self.func, lambda a, b, evaluate=False: ~(self.func(a,
        #      b, evaluate=evaluate)))(*self.args, evaluate=False)
        return Relational.__new__(ops.get(self.func), *self.args,
                                  for_clause=with_clause,
                                  with_clause=for_clause,
                                  plausible=self.plausible)

    def _eval_evalf(self, prec):
        return self.func(*[s._evalf(prec) for s in self.args])

    @property
    def canonical(self):
        """Return a canonical form of the relational by putting a
        Number on the rhs else ordering the args. The relation is also changed
        so that the left-hand side expression does not start with a `-`.
        No other simplification is attempted.

        Examples
        ========

        >>> from sympy.abc import x, y
        >>> x < 2
        x < 2
        >>> _.reversed.canonical
        x < 2
        >>> (-y < x).canonical
        x > -y
        >>> (-y > x).canonical
        x < -y
        """
        args = self.args
        r = self
        if r.rhs.is_number:
            if r.rhs.is_Number and r.lhs.is_Number and r.lhs > r.rhs:
                r = r.reversed
        elif r.lhs.is_number:
            r = r.reversed
        elif tuple(ordered(args)) != args:
            r = r.reversed

        # Check if first value has negative sign
        if not isinstance(r.lhs, BooleanAtom) and \
                r.lhs.could_extract_minus_sign():
            r = -r
        elif not isinstance(r.rhs, BooleanAtom) and not r.rhs.is_number and \
                r.rhs.could_extract_minus_sign():
            # Right hand side has a minus, but not lhs.
            # How does the expression with reversed signs behave?
            # This is so that expressions of the type Eq(x, -y) and Eq(-x, y)
            # have the same canonical representation
            expr1, _ = ordered([r.lhs, -r.rhs])
            if expr1 != r.lhs:
                r = -r.reversed
        return r

    def equals(self, other, failing_expression=False):
        """Return True if the sides of the relationship are mathematically
        identical and the type of relationship is the same.
        If failing_expression is True, return the expression whose truth value
        was unknown."""
        if isinstance(other, Relational):
            if self == other or self.reversed == other:
                return True
            a, b = self, other
            if a.func in (Eq, Ne) or b.func in (Eq, Ne):
                if a.func != b.func:
                    return False
                left, right = [i.equals(j,
                                        failing_expression=failing_expression)
                               for i, j in zip(a.args, b.args)]
                if left is True:
                    return right
                if right is True:
                    return left
                lr, rl = [i.equals(j, failing_expression=failing_expression)
                          for i, j in zip(a.args, b.reversed.args)]
                if lr is True:
                    return rl
                if rl is True:
                    return lr
                e = (left, right, lr, rl)
                if all(i is False for i in e):
                    return False
                for i in e:
                    if i not in (True, False):
                        return i
            else:
                if b.func != a.func:
                    b = b.reversed
                if a.func != b.func:
                    return False
                left = a.lhs.equals(b.lhs,
                                    failing_expression=failing_expression)
                if left is False:
                    return False
                right = a.rhs.equals(b.rhs,
                                     failing_expression=failing_expression)
                if right is False:
                    return False
                if left is True:
                    return right
                return left

    def _eval_simplify(self, ratio, measure, rational, inverse):
        r = self
        r = r.func(*[i.simplify(ratio=ratio, measure=measure,
                                rational=rational, inverse=inverse)
                     for i in r.args])
        if r.is_Relational:
            dif = r.lhs - r.rhs
            # replace dif with a valid Number that will
            # allow a definitive comparison with 0
            v = None
            if dif.is_comparable:
                v = dif.n(2)
            elif dif.equals(0):  # XXX this is expensive
                v = S.Zero
            if v is not None:
                r = r.func._eval_relation(v, S.Zero)

        r = r.canonical
        if measure(r) < ratio * measure(self):
            return r
        else:
            return self

    def _eval_trigsimp(self, **opts):
        from sympy.simplify import trigsimp
        return self.func(trigsimp(self.lhs, **opts), trigsimp(self.rhs, **opts))

    def __nonzero__(self):
        return False
        raise TypeError("cannot determine truth value of Relational")

    __bool__ = __nonzero__

    def _eval_as_set(self):
        # self is univariate and periodicity(self, x) in (0, None)
        from sympy.solvers.inequalities import solve_univariate_inequality
        syms = self.free_symbols
        assert len(syms) == 1
        x = syms.pop()
        return solve_univariate_inequality(self, x, relational=False)

    @property
    def binary_symbols(self):
        # override where necessary
        return set()

    @property
    def definition(self):
        if 'definition' in self._assumptions:
            return self._assumptions['definition']
        return None

    def simplifier(self):
        lhs, rhs = self.args
        from sympy.core.mul import Mul
        lhs_func = lhs.func
        rhs_func = rhs.func
        if lhs_func == rhs_func == Add:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                for arg in intersect:
                    lhs_args.remove(arg)
                    rhs_args.remove(arg)
                return self.func(lhs_func(*lhs_args), rhs_func(*rhs_args), equivalent=self if self.plausible else None).simplifier()
        elif rhs_func == Add:
            rhs_args = [*rhs.args]
            if lhs in rhs_args:
                rhs_args.remove(lhs)
                return self.func(0, rhs_func(*rhs_args), equivalent=self if self.plausible else None).simplifier()
        elif lhs_func == Add:
            lhs_args = [*lhs.args]
            if rhs in lhs_args:
                lhs_args.remove(rhs)
                return self.func(lhs_func(*lhs_args), 0, equivalent=self if self.plausible else None).simplifier()

        return self

    def sqrt(self):
        from sympy import sqrt
        return self.func(sqrt(self.lhs), sqrt(self.rhs), equivalent=self if self.plausible else None, with_clause=self.with_clause)

    def real_root(self, n):
        from sympy import real_root
        return self.func(real_root(self.lhs, n), real_root(self.rhs, n), equivalent=self if self.plausible else None, with_clause=self.with_clause)

    def expand(self, *args, **kwargs):
        return self.func(self.lhs.expand(*args, **kwargs), self.rhs.expand(*args, **kwargs), equivalent=self if self.plausible else None, with_clause=self.with_clause)

    def rewrite(self, *args, **hints):
        return self.func(self.lhs.rewrite(*args, **hints), self.rhs.rewrite(*args, **hints), equivalent=self if self.plausible else None, with_clause=self.with_clause)

    def doit(self, *args, **kwargs):
        return self.func(self.lhs.doit(*args, **kwargs), self.rhs.doit(*args, **kwargs), equivalent=self if self.plausible else None, with_clause=self.with_clause)

    def __add__(self, exp):
        if isinstance(exp, Equality):
            if exp.plausible:
                if self.plausible:
                    return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
                return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=exp)
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=self if self.plausible else None)
        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self if self.plausible else None)

    def __sub__(self, exp):
        if isinstance(exp, Equality):
            if exp.plausible:
                if self.plausible:
                    return self.func(self.lhs - exp.lhs, self.rhs - exp.rhs, equivalent=[self, exp])
                return self.func(self.lhs - exp.lhs, self.rhs - exp.rhs, equivalent=exp, **self.clauses(exp))
            return self.func(self.lhs - exp.lhs, self.rhs - exp.rhs, equivalent=self if self.plausible else None)
        else:
            return self.func(self.lhs - exp, self.rhs - exp, equivalent=self if self.plausible else None)

    def __mul__(self, exp):
        if isinstance(exp, Equality):
            nonzero = exp.lhs.is_nonzero or exp.rhs.is_nonzero
            if exp.plausible:
                if self.plausible:
                    if nonzero:
                        return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                    return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
                if nonzero:
                    return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=exp)
                return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, given=exp)
            if self.plausible:
                if nonzero:
                    return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=self)
                return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)
            return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs)

        else:
            if exp > 0:
                return self.func(self.lhs * exp, self.rhs * exp, equivalent=self if self.plausible else None, with_clause=self.with_clause)
            if exp < 0:
                return reversed_ops[self.func](self.lhs * exp, self.rhs * exp, equivalent=self if self.plausible else None, with_clause=self.with_clause)
            elif exp >= 0:
                return self.func(self.lhs * exp, self.rhs * exp, given=self if self.plausible else None, with_clause=self.with_clause)
            elif exp <= 0:
                return reversed_ops[self.func](self.lhs * exp, self.rhs * exp, given=self if self.plausible else None, with_clause=self.with_clause)
            return self

    def __truediv__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs != 0 or exp.rhs != 0:
                if exp.plausible:
                    if self.plausible:
                        return self.func(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=[self, exp])
                    return self.func(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=exp)
                return self.func(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=self if self.plausible else None)
            return self
        else:
            if exp > 0:
                return self.func((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self if self.plausible else None, with_clause=self.with_clause)
            if exp < 0:
                return reversed_ops[self.func]((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self if self.plausible else None, with_clause=self.with_clause)
            return self


Rel = Relational


class Equality(Relational):
    """An equal relation between two objects.

    Represents that two objects are equal.  If they can be easily shown
    to be definitively equal (or unequal), this will reduce to True (or
    False).  Otherwise, the relation is maintained as an unevaluated
    Equality object.  Use the ``simplify`` function on this object for
    more nontrivial evaluation of the equality relation.

    As usual, the keyword argument ``evaluate=False`` can be used to
    prevent any evaluation.

    Examples
    ========

    >>> from sympy import Eq, simplify, exp, cos
    >>> from sympy.abc import x, y
    >>> Eq(y, x + x**2)
    Eq(y, x**2 + x)
    >>> Eq(2, 5)
    False
    >>> Eq(2, 5, evaluate=False)
    Eq(2, 5)
    >>> _.doit()
    False
    >>> Eq(exp(x), exp(x).rewrite(cos))
    Eq(exp(x), sinh(x) + cosh(x))
    >>> simplify(_)
    True

    See Also
    ========

    sympy.logic.boolalg.Equivalent : for representing equality between two
        boolean expressions

    Notes
    =====

    This class is not the same as the == operator.  The == operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    If either object defines an `_eval_Eq` method, it can be used in place of
    the default algorithm.  If `lhs._eval_Eq(rhs)` or `rhs._eval_Eq(lhs)`
    returns anything other than None, that return value will be substituted for
    the Equality.  If None is returned by `_eval_Eq`, an Equality object will
    be created as usual.

    Since this object is already an expression, it does not respond to
    the method `as_expr` if one tries to create `x - y` from Eq(x, y).
    This can be done with the `rewrite(Add)` method.
    """
    rel_op = '=='

    __slots__ = []

    is_Equality = True

    def __new__(cls, lhs, rhs=None, **options):
#         from sympy.core.add import Add
        from sympy.core.logic import fuzzy_bool
        from sympy.core.expr import _n2
        from sympy.simplify.simplify import clear_coefficients

        if rhs is None:
            SymPyDeprecationWarning(
                feature="Eq(expr) with rhs default to 0",
                useinstead="Eq(expr, 0)",
                issue=16587,
                deprecated_since_version="1.5"
            ).warn()
            rhs = 0

        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        evaluate = options.pop('evaluate', global_evaluate[0])

        if evaluate:
            # If one expression has an _eval_Eq, return its results.
            if hasattr(lhs, '_eval_Eq'):
                r = lhs._eval_Eq(rhs)
                if r is not None:
                    return r
            if hasattr(rhs, '_eval_Eq'):
                r = rhs._eval_Eq(lhs)
                if r is not None:
                    return r
            # If expressions have the same structure, they must be equal.
            if lhs == rhs:
                process_options(options)
                return S.true  # e.g. True == True
            elif all(isinstance(i, BooleanAtom) for i in (rhs, lhs)):
                return S.false  # True != False
            elif not (lhs.is_Symbol or rhs.is_Symbol) and (
                    isinstance(lhs, Boolean) !=
                    isinstance(rhs, Boolean)):
                return S.false  # only Booleans can equal Booleans

            # check finiteness
#             fin = L, R = [i.is_finite for i in (lhs, rhs)]
#             if None not in fin:
#                 if L != R:
#                     return S.false
#                 if L is False:
#                     if lhs == -rhs:  # Eq(oo, -oo)
#                         return S.false
#                     return S.true
#             elif None in fin and False in fin:
#                 return Relational.__new__(cls, lhs, rhs, **options)

            if all(isinstance(i, Expr) for i in (lhs, rhs)):
                # see if the difference evaluates
                dif = (lhs - rhs).simplifier()
                z = dif.is_zero
                if z is not None:
                    if z is False and dif.is_commutative:  # issue 10728
                        process_options(options, value=False)
                        return S.false
                    if z:
                        process_options(options)
                        return S.true
                # evaluate numerically if possible
#                 n2 = _n2(lhs, rhs)
#                 if n2 is not None:
#                     return _sympify(n2 == 0)
                # see if the ratio evaluates
#                 n, d = dif.as_numer_denom()
#                 rv = None
#                 if n.is_zero:
#                     rv = d.is_nonzero
#                 elif n.is_finite:
#                     if d.is_infinite:
#                         rv = S.true
#                     elif n.is_zero is False:
#                         rv = d.is_infinite
#                         if rv is None:
#                             # if the condition that makes the denominator
#                             # infinite does not make the original expression
#                             # True then False can be returned
#                             l, r = clear_coefficients(d, S.Infinity)
#                             args = [_.subs(l, r) for _ in (lhs, rhs)]
#                             if args != [lhs, rhs]:
#                                 rv = fuzzy_bool(Eq(*args))
#                                 if rv is True:
#                                     rv = None
#                 elif any(a.is_infinite for a in Add.make_args(n)):
#                     # (inf or nan)/x != 0
#                     rv = S.false
#                 if rv is not None:
#                     return _sympify(rv)

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs == rhs)

    def _eval_rewrite_as_Add(self, *args, **kwargs):
        """return Eq(L, R) as L - R. To control the evaluation of
        the result set pass `evaluate=True` to give L - R;
        if `evaluate=None` then terms in L and R will not cancel
        but they will be listed in canonical order; otherwise
        non-canonical args will be returned.

        Examples
        ========

        >>> from sympy import Eq, Add
        >>> from sympy.abc import b, x
        >>> eq = Eq(x + b, x - b)
        >>> eq.rewrite(Add)
        2*b
        >>> eq.rewrite(Add, evaluate=None).args
        (b, b, x, -x)
        >>> eq.rewrite(Add, evaluate=False).args
        (b, x, b, -x)
        """
        L, R = args
        evaluate = kwargs.get('evaluate', True)
        if evaluate:
            # allow cancellation of args
            return L - R
        args = Add.make_args(L) + Add.make_args(-R)
        if evaluate is None:
            # no cancellation, but canonical
            return _unevaluated_Add(*args)
        # no cancellation, not canonical
        return Add._from_args(args)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return set([self.lhs])
            elif self.rhs.is_Symbol:
                return set([self.rhs])
        return set()

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        e = super(Equality, self)._eval_simplify(
            ratio, measure, rational, inverse)
        if not isinstance(e, Equality):
            return e
        free = self.free_symbols
        if len(free) == 1:
            try:
                x = free.pop()
                m, b = linear_coeffs(
                    e.rewrite(Add, evaluate=False), x)
                if m.is_zero is False:
                    enew = e.func(x, -b / m)
                else:
                    enew = e.func(m * x, -b)
                if measure(enew) <= ratio * measure(e):
                    e = enew
            except ValueError:
                pass
        return e.canonical

    def __truediv__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs != 0 or exp.rhs != 0:
                if exp.plausible:
                    if self.plausible:
                        return Eq(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=[self, exp])
                    return Eq(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=exp)
                return Eq(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=self if self.plausible else None)
            return self
        else:
            if exp != 0:
                return Eq(self.lhs / exp, self.rhs / exp, equivalent=self if self.plausible else None)
            return self

    def __mul__(self, exp):
        if isinstance(exp, Equality):
            nonzero = exp.lhs.is_nonzero or exp.rhs.is_nonzero
            if exp.plausible:
                if self.plausible:
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
                if nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=exp)
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=exp)
            if self.plausible:
                if nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=self)
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)
            return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs)

        elif isinstance(exp, StrictLessThan):
            if exp.lhs > 0:
                if exp.plausible:
                    if self.plausible:
                        return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                    return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=exp)
                if self.plausible:
                    return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=self)
                return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs)
            elif exp.lhs >= 0:
                if exp.plausible:
                    if self.plausible:
                        if nonzero:
                            return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                        return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=exp)
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=exp)
                if self.plausible:
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=self)
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs)
            elif exp.rhs < 0:
                if exp.plausible:
                    if self.plausible:
                        if nonzero:
                            return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                        return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=exp)
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=exp)
                if self.plausible:
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=self)
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs)
            elif exp.rhs <= 0:
                if exp.plausible:
                    if self.plausible:
                        if nonzero:
                            return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                        return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=exp)
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=exp)
                if self.plausible:
                    if nonzero:
                        return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=self)
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs)
            return self
        else:
            if exp.is_nonzero:
                return Eq(self.lhs * exp, self.rhs * exp, equivalent=self if self.plausible else None, with_clause=self.with_clause)
            return Eq(self.lhs * exp, self.rhs * exp, given=self if self.plausible else None, with_clause=self.with_clause)

    def __rmatmul__(self, lhs):
        from sympy.matrices.expressions.determinant import det
        if isinstance(lhs, Equality):
            nonzero = det(lhs.lhs).is_nonzero or det(lhs.rhs).is_nonzero
            if lhs.plausible:
                if self.plausible:
                    if nonzero:
                        return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, equivalent=[self, lhs])
                    return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=[self, lhs])
                if nonzero:
                    return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, equivalent=lhs)
                return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=lhs)
            if self.plausible:
                if nonzero:
                    return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, equivalent=self)
                return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=self)
            return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs)
        else:
            if det(lhs).is_nonzero:
                return Eq(lhs @ self.lhs, lhs @ self.rhs, equivalent=self if self.plausible else None, with_clause=self.with_clause)
            return Eq(lhs @ self.lhs, lhs @ self.rhs, given=self if self.plausible else None, with_clause=self.with_clause)

    def __rpow__(self, exp):
        return Eq(exp ** self.lhs, exp ** self.rhs, equivalent=self if self.plausible else None)

    def powsimp(self, *args, **kwargs):
        return Eq(self.lhs.powsimp(*args, **kwargs), self.rhs.powsimp(*args, **kwargs), equivalent=self if self.plausible else None)

    def collect(self, syms):
        return Eq(self.lhs.collect(syms), self.rhs.collect(syms), equivalent=self if self.plausible else None)

    @property
    def right(self):
        return Invoker(self, True)

    @property
    def left(self):
        return Invoker(self, False)

    def rsolve(self, y):
        from sympy.solvers.recurr import rsolve
        solution = rsolve(self, y, symbols=True)
        if solution is None:
            return self
        solution, C = solution
        if len(C) == 1:
            C = C[0]
        elif len(C) == 0:
            C = None

        return self.func(y, solution, with_clause=C, equivalent=self if self.plausible else None)

    def solve(self, x):
        from sympy.solvers.solvers import solve
        res = solve(self.lhs - self.rhs, x)
        clauses = self.clauses()

        with_clause = clauses['with_clause']
        if len(res) == 1:
            x_sol, *_ = res
            return Eq(x, x_sol, equivalent=self if self.plausible else None, **clauses)
        if len(res) > 1:
            if x == with_clause or x in with_clause:
                x_sol = [x_sol for x_sol in res if x_sol.domain & x.domain]

                if len(x_sol) == 1:
                    x_sol = x_sol[0]
                    from sympy.sets.contains import Contains

                    if x == with_clause:
                        del clauses['with_clause']
                    else:
                        clauses['with_clause'].remove(x)

                    return Contains(x_sol, x.domain, equivalent=self if self.plausible else None, **clauses)
                if not x_sol:
                    self.plausible = False
                    return self

            from sympy.logic.boolalg import Or
            return Or(*(Equality(x, x_sol, equivalent=self if self.plausible else None, **clauses) for x_sol in res))

        return self

    def subs(self, *args, **kwargs):
        if isinstance(args[0], Equality):
            if len(args) == 1:
                eq, *_ = args
                if isinstance(eq, Equality):
                    args = eq.args
                    if eq.plausible:
                        if self.plausible:
                            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq], **self.clauses(eq)).simplifier()
                        return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=eq, **self.clauses(eq)).simplifier()
                    return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=self if self.plausible else None, **self.clauses()).simplifier()
                return self
            else:
                res = self
                for eq in args:
                    res = res.subs(eq)
                return res
        old, new = args
#         if old in self.for_clause:
#             domain = self.for_clause[old]
#
#             for_clause[old] = domain.subs(old, new)
#             return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), substituent=self, for_clause=for_clause)
#         else:
        from sympy import Symbol
        if not isinstance(old, Symbol):
            free_symbols = self.free_symbols
            variables = [symbol for symbol in old.free_symbols if symbol in free_symbols]
            if not variables:
                return self

            if len(variables) == 1:
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                g = self.lhs - self.rhs
                _g = lhs - rhs
                if g > _g:
                    return StrictLessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g >= _g:
                    return LessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

                if g < _g:
                    return GreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g <= _g:
                    return StrictGreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

            else:
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                g = self.lhs - self.rhs
                _g = lhs - rhs
                if g > _g:
                    return StrictLessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g >= _g:
                    return LessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

                if g < _g:
                    return GreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g <= _g:
                    return StrictGreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = self.func(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self, **self.clauses())
            else:
                eq = self.func(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self, **self.clauses())
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
#         return self

    @staticmethod
    def by_definition_of(x):
        from sympy.tensor.indexed import IndexedBase
        from sympy.stats.rv import Density, PDF
        from sympy.core.symbol import Symbol
        from sympy.stats.rv import random_symbols, pspace

        if isinstance(x, IndexedBase):
            from sympy import Mul
            from sympy.functions.elementary.miscellaneous import Ref
            if isinstance(x.definition, Ref):
                return Eq(x[tuple(var for var, *_ in x.definition.limits)], x.definition.function)
            elif isinstance(x.definition, Mul):
                args = []
                ref = None
                for arg in x.definition.args:
                    if isinstance(arg, Ref):
                        assert ref is None
                        ref = arg
                    else:
                        args.append(arg)
                if ref is not None:
                    (var, *_), *_ = ref.limits
                    return Eq(x[var], Mul(*args) * ref.function)
        elif isinstance(x, Density):
            rvs = random_symbols(x.expr)

            if any(pspace(rv).is_Continuous for rv in rvs):
                y = Symbol("y", real=True)
            else:
                nonnegative = x.expr.domain.is_nonnegative

                if nonnegative:
                    y = Symbol("y", integer=True, nonnegative=True)
                else:
                    y = Symbol("y", integer=True)

            pdf = x(y)

            return Eq(pdf, pdf.doit(evaluate=False))

        elif isinstance(x, PDF):
            return Eq(x, x.doit(evaluate=False))
        return Eq(x, x.definition)

    def subscript(self, *key):
        return self.func(self.lhs[key], self.rhs[key], equivalent=self if self.plausible else None)

    def log(self):
        from sympy import log
        return self.func(log(self.lhs), log(self.rhs), equivalent=self if self.plausible else None)

    def combsimp(self, *args):
        from sympy import combsimp
        return self.func(combsimp(self.lhs, *args), combsimp(self.rhs, *args), equivalent=self if self.plausible else None)

    def det(self):
        from sympy import det
        return self.func(det(self.lhs), det(self.rhs), given=self if self.plausible else None)

    def simplifier(self):
        lhs, rhs = self.args
        from sympy.core.mul import Mul
        from sympy.matrices.expressions.matmul import MatMul

        if type(lhs) == type(rhs):
            op = lhs.func
            if op == Mul or op == Add or op == MatMul:
                lhs_args = [*lhs.args]
                rhs_args = [*rhs.args]
                intersect = set(lhs_args) & set(rhs_args)
                if intersect:
                    for arg in intersect:
                        lhs_args.remove(arg)
                        rhs_args.remove(arg)
                    return self.func(op(*lhs_args), op(*rhs_args), equivalent=self if self.plausible else None, **self.clauses()).simplifier()

        return self

    def as_two_terms(self):
        return self.func(self.lhs.as_two_terms(), self.rhs.as_two_terms(), equivalent=self if self.plausible else None).simplifier()


Eq = Equality


class Invoker:

    def __init__(self, eq, right=True):
        self.eq = eq
        self.right = right
        j = int(right)

        self.obj = eq.args[j]
        self.func = [eq.func]
        self._args = [[*eq.args]]
        self.index = [j]

    def __call__(self, *args, **kwargs):
        if self.obj.__name__ == 'subs':
            from sympy.concrete.summations import Sum
            from sympy.integrals.integrals import Integral
            if isinstance(self.obj.__self__, Sum) or isinstance(self.obj.__self__, Integral):
                if len(args) == 2:
                    (x, *_), *_ = self.obj.__self__.limits
                    # domain might be different!
                    assert args[0].name == x.name
            else:
                assert all(isinstance(arg, Equality) for arg in args)

        obj = self.obj(*args, **kwargs)

        for i in range(-1, -len(self.func) - 1, -1):
            self._args[i][self.index[i]] = obj

            if i == -len(self.func):
                obj = self.func[i](*self._args[i], equivalent=self.eq if self.eq.plausible else None, **self.eq.clauses())
            else:
                obj = self.func[i](*self._args[i])

            obj = obj.simplifier()
        return obj

    def __getattr__(self, method):
        obj = getattr(self.obj, method)
        if not callable(obj):
            self.func.append(self.obj.func)
            self._args.append([*self.obj.args])
            if not isinstance(obj, tuple):
                self.index.append(self.obj.args.index(obj))

        self.obj = obj
        return self

    def __str__(self):
        return str(self.obj)

    @property
    def latex(self):
        return self.obj.latex

    def __getitem__(self, j):
        self.obj = self.obj[j]
        self.index.append(j)
        return self

    def __iter__(self):
        return iter(self.obj)


class Unequality(Relational):
    """An unequal relation between two objects.

    Represents that two objects are not equal.  If they can be shown to be
    definitively equal, this will reduce to False; if definitively unequal,
    this will reduce to True.  Otherwise, the relation is maintained as an
    Unequality object.

    Examples
    ========

    >>> from sympy import Ne
    >>> from sympy.abc import x, y
    >>> Ne(y, x+x**2)
    Ne(y, x**2 + x)

    See Also
    ========
    Equality

    Notes
    =====
    This class is not the same as the != operator.  The != operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    This class is effectively the inverse of Equality.  As such, it uses the
    same algorithms, including any available `_eval_Eq` methods.

    """
    rel_op = '!='

    __slots__ = []

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        evaluate = options.pop('evaluate', global_evaluate[0])

        if evaluate:
            is_equal = Equality(lhs, rhs)
            if isinstance(is_equal, BooleanAtom):
                return is_equal.negated

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs != rhs)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return set([self.lhs])
            elif self.rhs.is_Symbol:
                return set([self.rhs])
        return set()

    def _eval_simplify(self, ratio, measure, rational, inverse):
        # simplify as an equality
        eq = Equality(*self.args)._eval_simplify(
            ratio, measure, rational, inverse)
        if isinstance(eq, Equality):
            # send back Ne with the new args
            return self.func(*eq.args)
        return eq.negated  # result of Ne is the negated Eq


Ne = Unequality


class _Inequality(Relational):
    """Internal base class for all *Than types.

    Each subclass must implement _eval_relation to provide the method for
    comparing two real numbers.

    """
    __slots__ = []

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        evaluate = options.pop('evaluate', global_evaluate[0])

        if evaluate:
            # First we invoke the appropriate inequality method of `lhs`
            # (e.g., `lhs.__lt__`).  That method will try to reduce to
            # boolean or raise an exception.  It may keep calling
            # superclasses until it reaches `Expr` (e.g., `Expr.__lt__`).
            # In some cases, `Expr` will just invoke us again (if neither it
            # nor a subclass was able to reduce to boolean or raise an
            # exception).  In that case, it must call us with
            # `evaluate=False` to prevent infinite recursion.
            r = cls._eval_relation(lhs, rhs)
            if r :
                process_options(options)
                return r
            if r == S.false:
                process_options(options, False)
                return r

            # Note: not sure r could be None, perhaps we never take this
            # path?  In principle, could use this to shortcut out if a
            # class realizes the inequality cannot be evaluated further.

        # make a "non-evaluated" Expr for the inequality
        return Relational.__new__(cls, lhs, rhs, **options)


class _Greater(_Inequality):
    """Not intended for general use

    _Greater is only used so that GreaterThan and StrictGreaterThan may
    subclass it for the .gts and .lts properties.

    """
    __slots__ = ()

    @property
    def gts(self):
        return self._args[0]

    @property
    def lts(self):
        return self._args[1]


class _Less(_Inequality):
    """Not intended for general use.

    _Less is only used so that LessThan and StrictLessThan may subclass it for
    the .gts and .lts properties.

    """
    __slots__ = ()

    @property
    def gts(self):
        return self._args[1]

    @property
    def lts(self):
        return self._args[0]

    def __and__(self, other):
        from sympy.sets.sets import Interval
        from sympy.sets.contains import Contains
        if isinstance(other, _Greater) and self.lhs == other.lhs:
            return Contains(self.lhs,
                            Interval(other.rhs, self.rhs,
                                     left_open=isinstance(other, StrictGreaterThan),
                                     right_open=isinstance(self, StrictLessThan)),
                            equivalent=[self, other], **self.clauses(other))
        return Relational.__and__(self, other)


class GreaterThan(_Greater):
    """Class representations of inequalities.

    Extended Summary
    ================

    The ``*Than`` classes represent inequal relationships, where the left-hand
    side is generally bigger or smaller than the right-hand side.  For example,
    the GreaterThan class represents an inequal relationship where the
    left-hand side is at least as big as the right side, if not bigger.  In
    mathematical notation:

    lhs >= rhs

    In total, there are four ``*Than`` classes, to represent the four
    inequalities:

    +-----------------+--------+
    |Class Name       | Symbol |
    +=================+========+
    |GreaterThan      | (>=)   |
    +-----------------+--------+
    |LessThan         | (<=)   |
    +-----------------+--------+
    |StrictGreaterThan| (>)    |
    +-----------------+--------+
    |StrictLessThan   | (<)    |
    +-----------------+--------+

    All classes take two arguments, lhs and rhs.

    +----------------------------+-----------------+
    |Signature Example           | Math equivalent |
    +============================+=================+
    |GreaterThan(lhs, rhs)       |   lhs >= rhs    |
    +----------------------------+-----------------+
    |LessThan(lhs, rhs)          |   lhs <= rhs    |
    +----------------------------+-----------------+
    |StrictGreaterThan(lhs, rhs) |   lhs >  rhs    |
    +----------------------------+-----------------+
    |StrictLessThan(lhs, rhs)    |   lhs <  rhs    |
    +----------------------------+-----------------+

    In addition to the normal .lhs and .rhs of Relations, ``*Than`` inequality
    objects also have the .lts and .gts properties, which represent the "less
    than side" and "greater than side" of the operator.  Use of .lts and .gts
    in an algorithm rather than .lhs and .rhs as an assumption of inequality
    direction will make more explicit the intent of a certain section of code,
    and will make it similarly more robust to client code changes:

    >>> from sympy import GreaterThan, StrictGreaterThan
    >>> from sympy import LessThan,    StrictLessThan
    >>> from sympy import And, Ge, Gt, Le, Lt, Rel, S
    >>> from sympy.abc import x, y, z
    >>> from sympy.core.relational import Relational

    >>> e = GreaterThan(x, 1)
    >>> e
    x >= 1
    >>> '%s >= %s is the same as %s <= %s' % (e.gts, e.lts, e.lts, e.gts)
    'x >= 1 is the same as 1 <= x'

    Examples
    ========

    One generally does not instantiate these classes directly, but uses various
    convenience methods:

    >>> for f in [Ge, Gt, Le, Lt]:  # convenience wrappers
    ...     print(f(x, 2))
    x >= 2
    x > 2
    x <= 2
    x < 2

    Another option is to use the Python inequality operators (>=, >, <=, <)
    directly.  Their main advantage over the Ge, Gt, Le, and Lt counterparts,
    is that one can write a more "mathematical looking" statement rather than
    littering the math with oddball function calls.  However there are certain
    (minor) caveats of which to be aware (search for 'gotcha', below).

    >>> x >= 2
    x >= 2
    >>> _ == Ge(x, 2)
    True

    However, it is also perfectly valid to instantiate a ``*Than`` class less
    succinctly and less conveniently:

    >>> Rel(x, 1, ">")
    x > 1
    >>> Relational(x, 1, ">")
    x > 1

    >>> StrictGreaterThan(x, 1)
    x > 1
    >>> GreaterThan(x, 1)
    x >= 1
    >>> LessThan(x, 1)
    x <= 1
    >>> StrictLessThan(x, 1)
    x < 1

    Notes
    =====

    There are a couple of "gotchas" to be aware of when using Python's
    operators.

    The first is that what your write is not always what you get:

        >>> 1 < x
        x > 1

        Due to the order that Python parses a statement, it may
        not immediately find two objects comparable.  When "1 < x"
        is evaluated, Python recognizes that the number 1 is a native
        number and that x is *not*.  Because a native Python number does
        not know how to compare itself with a SymPy object
        Python will try the reflective operation, "x > 1" and that is the
        form that gets evaluated, hence returned.

        If the order of the statement is important (for visual output to
        the console, perhaps), one can work around this annoyance in a
        couple ways:

        (1) "sympify" the literal before comparison

        >>> S(1) < x
        1 < x

        (2) use one of the wrappers or less succinct methods described
        above

        >>> Lt(1, x)
        1 < x
        >>> Relational(1, x, "<")
        1 < x

    The second gotcha involves writing equality tests between relationals
    when one or both sides of the test involve a literal relational:

        >>> e = x < 1; e
        x < 1
        >>> e == e  # neither side is a literal
        True
        >>> e == x < 1  # expecting True, too
        False
        >>> e != x < 1  # expecting False
        x < 1
        >>> x < 1 != x < 1  # expecting False or the same thing as before
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of Relational

        The solution for this case is to wrap literal relationals in
        parentheses:

        >>> e == (x < 1)
        True
        >>> e != (x < 1)
        False
        >>> (x < 1) != (x < 1)
        False

    The third gotcha involves chained inequalities not involving
    '==' or '!='. Occasionally, one may be tempted to write:

        >>> e = x < y < z
        Traceback (most recent call last):
        ...
        TypeError: symbolic boolean expression has no truth value.

        Due to an implementation detail or decision of Python [1]_,
        there is no way for SymPy to create a chained inequality with
        that syntax so one must use And:

        >>> e = And(x < y, y < z)
        >>> type( e )
        And
        >>> e
        (x < y) & (y < z)

        Although this can also be done with the '&' operator, it cannot
        be done with the 'and' operarator:

        >>> (x < y) & (y < z)
        (x < y) & (y < z)
        >>> (x < y) and (y < z)
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of Relational

    .. [1] This implementation detail is that Python provides no reliable
       method to determine that a chained inequality is being built.
       Chained comparison operators are evaluated pairwise, using "and"
       logic (see
       http://docs.python.org/2/reference/expressions.html#notin). This
       is done in an efficient way, so that each object being compared
       is only evaluated once and the comparison can short-circuit. For
       example, ``1 > 2 > 3`` is evaluated by Python as ``(1 > 2) and (2
       > 3)``. The ``and`` operator coerces each side into a bool,
       returning the object itself when it short-circuits. The bool of
       the --Than operators will raise TypeError on purpose, because
       SymPy cannot determine the mathematical ordering of symbolic
       expressions. Thus, if we were to compute ``x > y > z``, with
       ``x``, ``y``, and ``z`` being Symbols, Python converts the
       statement (roughly) into these steps:

        (1) x > y > z
        (2) (x > y) and (y > z)
        (3) (GreaterThanObject) and (y > z)
        (4) (GreaterThanObject.__nonzero__()) and (y > z)
        (5) TypeError

       Because of the "and" added at step 2, the statement gets turned into a
       weak ternary statement, and the first object's __nonzero__ method will
       raise TypeError.  Thus, creating a chained inequality is not possible.

           In Python, there is no way to override the ``and`` operator, or to
           control how it short circuits, so it is impossible to make something
           like ``x > y > z`` work.  There was a PEP to change this,
           :pep:`335`, but it was officially closed in March, 2012.

    """
    __slots__ = ()

    rel_op = '>='

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__ge__(rhs))


Ge = GreaterThan


class LessThan(_Less):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    rel_op = '<='

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__le__(rhs))

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                if eq.plausible:
                    if self.plausible:
                        return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=eq)
                return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=self if self.plausible else None)
            elif isinstance(eq, StrictLessThan):
                old, new = eq.args
                if eq.plausible:
                    if self.plausible:
                        return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=eq)

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = self.lhs.subs(old, new).simplify()
                    rhs = self.rhs.subs(old, new).simplify()
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self if self.plausible else None)
                return self
            elif isinstance(eq, LessThan):
                old, new = eq.args
                if eq.plausible:
                    if self.plausible:
                        return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=eq)

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = self.lhs.subs(old, new).simplify()
                    rhs = self.rhs.subs(old, new).simplify()
#                     _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self if self.plausible else None)
                return self

            return self

        if all(isinstance(arg, Relational) for arg in args):
            from sympy import Symbol
            free_symbols = self.free_symbols
            f = self.lhs - self.rhs
            given = []
            for eq in args:
                if eq.plausible:
                    given.append(eq)
                old, new = eq.args
                if old in free_symbols:
                    domain = old.domain & old.conditional_domain(eq)
                    if domain != old.domain:
                        _old = Symbol(old.name, domain=domain)
                        f = f.subs(old, _old)
                else:
                    return self

            maxi = f.max()
            if self.plausible:
                return LessThan(maxi, 0, imply=self, given=given if given else None)
            return self

        old, new = args
#         if old in self.for_clause:
#             domain = self.for_clause[old]
#
#             for_clause[old] = domain.subs(old, new)
#             return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), substituent=self, for_clause=for_clause)
#         else:
        from sympy import Symbol
        if not isinstance(old, Symbol):
            free_symbols = self.free_symbols
            variables = [symbol for symbol in old.free_symbols if symbol in free_symbols]
            if not variables:
                return self

            if len(variables) == 1:
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                g = self.lhs - self.rhs
                _g = lhs - rhs
                if g > _g:
                    return StrictLessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g >= _g:
                    return LessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

                if g < _g:
                    return GreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g <= _g:
                    return StrictGreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

            else:
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                g = self.lhs - self.rhs
                _g = lhs - rhs
                if g > _g:
                    return StrictLessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g >= _g:
                    return LessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

                if g < _g:
                    return GreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g <= _g:
                    return StrictGreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))


Le = LessThan


class StrictGreaterThan(_Greater):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    rel_op = '>'

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__gt__(rhs))

    def __add__(self, exp):
        if isinstance(exp, Equality):
            if exp.plausible:
                if self.plausible:
                    return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
                return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=exp)
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=self if self.plausible else None)
        elif isinstance(exp, StrictGreaterThan):
            if exp.plausible:
                if self.plausible:
                    return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=[self, exp])
                return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=exp)
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=self if self.plausible else None)

        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self if self.plausible else None)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                if eq.plausible:
                    if self.plausible:
                        return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=eq)
                return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=self if self.plausible else None)
            elif isinstance(eq, StrictLessThan):
                old, new = eq.args
                if eq.plausible:
                    if self.plausible:
                        return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=eq)

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = self.lhs.subs(old, new).simplify()
                    rhs = self.rhs.subs(old, new).simplify()
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self if self.plausible else None)
                return self

            return self
        old, new = args
#         if old in self.for_clause:
#             domain = self.for_clause[old]
#
#             for_clause[old] = domain.subs(old, new)
#             return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), substituent=self, for_clause=for_clause)
#         else:
        from sympy import Symbol
        if not isinstance(old, Symbol):
            free_symbols = self.free_symbols
            variables = [symbol for symbol in old.free_symbols if symbol in free_symbols]
            if not variables:
                return self

            if len(variables) == 1:
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                g = self.lhs - self.rhs
                _g = lhs - rhs
                if g > _g:
                    return StrictLessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g >= _g:
                    return LessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

                if g < _g:
                    return GreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g <= _g:
                    return StrictGreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

            else:
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                g = self.lhs - self.rhs
                _g = lhs - rhs
                if g > _g:
                    return StrictLessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g >= _g:
                    return LessThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

                if g < _g:
                    return GreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())
                if g <= _g:
                    return StrictGreaterThan(lhs, rhs, given=self if self.plausible else None, **self.clauses())

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
#         return self


Gt = StrictGreaterThan


class StrictLessThan(_Less):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    rel_op = '<'

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__lt__(rhs))

    def __add__(self, exp):
        if isinstance(exp, Equality):
            if exp.plausible:
                if self.plausible:
                    return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
                return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=exp)
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=self if self.plausible else None)
        elif isinstance(exp, StrictLessThan):
            if exp.plausible:
                if self.plausible:
                    return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=[self, exp])
                return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=exp)
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=self if self.plausible else None)
        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self if self.plausible else None, **self.clauses())


Lt = StrictLessThan

reversed_ops = {Eq: Eq, Gt: Lt, Ge: Le, Lt: Gt, Le: Ge, Ne: Ne}
# A class-specific (not object-specific) data item used for a minor speedup.
# It is defined here, rather than directly in the class, because the classes
# that it references have not been defined until now (e.g. StrictLessThan).
Relational.ValidRelationOperator = {
    None: Equality,
    '==': Equality,
    'eq': Equality,
    '!=': Unequality,
    '<>': Unequality,
    'ne': Unequality,
    '>=': GreaterThan,
    'ge': GreaterThan,
    '<=': LessThan,
    'le': LessThan,
    '>': StrictGreaterThan,
    'gt': StrictGreaterThan,
    '<': StrictLessThan,
    'lt': StrictLessThan,
}
