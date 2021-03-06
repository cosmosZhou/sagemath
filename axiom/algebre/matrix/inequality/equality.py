from axiom.utility import plausible
from sympy.core.relational import Unequal, Equality
from sympy import Symbol
from sympy.matrices.expressions.determinant import Determinant
from sympy.matrices.expressions.inverse import Inverse
from sympy.matrices.expressions.cofactor import Cofactors
from axiom import algebre


@plausible
def apply(*given):
    unequality, equality = given
    if not unequality.is_Unequality:
        unequality, equality = equality, unequality
    assert unequality.is_Unequality
    unequality.rhs.is_zero
    
    assert unequality.lhs.is_Determinant
    divisor = unequality.lhs.arg    
    return Equality(equality.lhs @ Inverse(divisor), equality.rhs @ Inverse(divisor), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True)
    A = Symbol.A(real=True, shape=(n, n))
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Unequal(Determinant(A), 0), Equality(a @ A, b))
    
    Eq << Eq[1] @ Cofactors(A).T
    
    Eq << algebre.matrix.determinant.adjugate.apply(A)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << algebre.scalar.inequality.equality.apply(Eq[0], Eq[-1])
    
    Eq << algebre.matrix.inequality.determinant.apply(Eq[0]) * Determinant(A)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    

if __name__ == '__main__':
    prove(__file__)
