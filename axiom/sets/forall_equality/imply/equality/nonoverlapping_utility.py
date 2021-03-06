from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy.concrete.expr_with_limits import ForAll, UNION
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.summations import Sum
from axiom import sets
from sympy.sets.contains import Contains

# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@plausible
def apply(given):
    assert given.is_ForAll
    eq = given.function
    assert eq.is_Equality
    limits = given.limits
    * limits, (_, j_domain) = limits
    assert j_domain.is_Complement
    
    n_interval, i = j_domain.args
    n = n_interval.stop
    i, *_ = i.args
    
    intersection, emptyset = eq.args
    assert emptyset.is_EmptySet
    
    xi, xj = intersection.args
    if not xi.has(i):
        xi = xj
        assert xj.has(i)
        
    eq = Equality(abs(UNION[i:0:n - 1](xi)), Sum[i:0:n - 1](abs(xi)))
    if limits:
        return ForAll(eq, *limits, given=given)
    else:
        eq.given = given
        return eq


from axiom.utility import check


@check
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    baseset = Interval(0, n, integer=True)
    
    assert Contains(0, baseset)

    domain = n.set
    assert n in baseset
    assert baseset & domain == domain

    x = Symbol.x(shape=(oo,), dtype=dtype.integer, finite=True)

    i_domain = Interval(0, n - 1, integer=True)
    
    Eq << apply(ForAll(Equality(x[i] & x[j], S.EmptySet), (j, i_domain - {i})))
    
    Eq << Eq[-1].subs(n, 2).doit()
    
    Eq << Eq[0].subs(i, 1)
    
    Eq << Eq[-1].subs(j, 0)
    
    Eq << sets.imply.equality.inclusion_exclusion_principle.apply(*Eq[-1].lhs.args).subs(Eq[-1])
    
    Eq.plausible = Eq[1].subs(n, n + 1)
    
    Eq << Eq.plausible.lhs.arg.this.bisect({n})
    
    Eq << sets.imply.equality.inclusion_exclusion_principle.apply(*Eq[-1].rhs.args)
    
    Eq << Eq[0].subs(i, n).limits_subs(j, i)
    
    Eq << Eq[-1].union_comprehension((i, 0, n - 1))
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq.plausible.rhs.this.bisect({n})
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    
if __name__ == '__main__':
    prove(__file__)

