from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy import S
from sympy.concrete.expr_with_limits import ForAll, UNION
from sympy import var
# given: A & Union[i](x[i]) = {}
# A & x[i] = {}


@plausible
def apply(given):
    assert given.is_Equality
    x_union_intersect_A, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = x_union_intersect_A
        x_union_intersect_A = tmp
        assert emptyset == S.EmptySet

    assert x_union_intersect_A.is_Intersection
    x_union, A = x_union_intersect_A.args

    if not x_union.is_UnionComprehension:
        tmp = x_union
        x_union = A
        A = tmp
    assert x_union.is_UnionComprehension

    return ForAll(Equality(x_union.function & A, S.EmptySet),
                  *x_union.limits,
                  given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    i = var(integer=True).i
    k = var(integer=True, positive=True).k
    x = Symbol('x', shape=(k + 1,), dtype=dtype.integer)

    equality = Equality(UNION[i:0:k](x[i]) & A, S.EmptySet)

    Eq << apply(equality)    
    
    Eq << Eq[-1].simplify()

    Eq << UNION[i:0:k](x[i] & A).this.simplify()

    Eq << Eq[-1].this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].apply(discrete.sets.union_comprehension.emptyset)


if __name__ == '__main__':
    prove(__file__)

