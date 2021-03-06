from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Interval
from axiom import sets
from sympy import S
from sympy.concrete.expr_with_limits import ForAll, UNION
from sympy import Symbol
# given: Union[i](x[i]) = {}
# x[i] = {}


@plausible
def apply(given):
    assert given.is_Equality
    x_union, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = x_union
        x_union = tmp
        assert emptyset == S.EmptySet

    assert x_union.is_UNION
    return ForAll(Equality(x_union.function, S.EmptySet), *x_union.limits, given=given)


from axiom.utility import check


@check
def prove(Eq):
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True, given=True)
    x = Symbol.x(shape=(k + 1,), dtype=dtype.integer, given=True)

    Eq << apply(Equality(UNION[i:0:k](x[i]), S.EmptySet))

    j = Symbol.j(domain=Interval(0, k, integer=True))
    
    Eq << Eq[-1].limits_subs(i, j)
    
    Eq.paradox = ~Eq[-1]

    Eq.positive = Eq.paradox.apply(sets.inequality.imply.strict_greater_than)

    Eq.union_empty = Eq[0].abs()

    Eq << Eq[0] - Eq.paradox.lhs

    Eq << Eq[-1].abs()

    Eq << Eq[-2].lhs.assertion()

    Eq << Eq[-1].subs(Eq[-2], Eq.union_empty)

    Eq << Eq[-1].subs(Eq.positive)


if __name__ == '__main__':
    prove(__file__)

