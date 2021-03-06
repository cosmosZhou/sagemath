from sympy.core.relational import Unequality, GreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S 
from axiom import sets
from sympy import Symbol
# given: A != {}
# |A| >= 1


@plausible
def apply(given):
    assert given.is_Unequality
    A, B = given.args
    if B != S.EmptySet:
        assert A == S.EmptySet
        A = B

    return GreaterThan(abs(A), 1, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    inequality = Unequality(A, S.EmptySet)

    Eq << apply(inequality)

    Eq << sets.inequality.imply.strict_greater_than.apply(inequality)
    
    Eq << ~Eq[1]
    Eq << Eq[-1].this.function.solve(Eq[-1].lhs)
    
    Eq << Eq[2].subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

