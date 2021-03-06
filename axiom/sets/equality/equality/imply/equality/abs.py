from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.core.function import Function
from sympy.concrete.expr_with_limits import UNION
from sympy.functions.elementary.complexes import Abs
from axiom import sets


@plausible
def apply(*given):
    equality_A, equality_B = given    
    assert equality_A.is_Equality and equality_B.is_Equality
    image_B, A = equality_A.args
    image_A, B = equality_B.args
        
    gb, b, _B = image_B.image_set()
    fb, a, _A = image_A.image_set()
    
    assert A == _A and B == _B
    
    return Equality(Abs(A), Abs(B), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(dtype=dtype.integer * n)
    a = Symbol.a(integer=True, shape=(n,))
    B = Symbol.B(dtype=dtype.integer * m)
    b = Symbol.b(integer=True, shape=(m,))
    
    f = Function.f(nargs=(n,), integer=True, shape=(m,))
    g = Function.g(nargs=(m,), integer=True, shape=(n,))

    assert f.is_integer
    assert g.is_integer
    assert f.shape == (m,)
    assert g.shape == (n,)
    
    Eq << apply(Equality(UNION[a:A](f(a).set), B), Equality(UNION[b:B](g(b).set), A))
    
    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[0].lhs.args)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[1].lhs.args)
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    prove(__file__)

