from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.core.relational import Equality, LessThan
from sympy import Symbol
from sympy.functions.elementary.complexes import Abs
from sympy.concrete.expr_with_limits import ForAll
from axiom import sets
from sympy.core.function import Function
from axiom.sets.forall_contains.forall_contains.forall_equality.imply.equality import analyze
# given: ForAll[x:A] (f(x) in B)
#        ForAll[y:B] (g(y) in A)

 
# |A| = |B|
@plausible
def apply(*given):
    A, B, a, b, fa, gb = analyze(*given)
    return LessThan(Abs(A), Abs(B), given=given)


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
    
    Eq << apply(ForAll[a:A](Contains(f(a), B)), ForAll[b:B](Contains(g(b), A)),
                ForAll[a:A](Equality(a, g(f(a)))))
    
    Eq << sets.forall_contains.forall_contains.forall_equality.imply.equality.apply(Eq[0], Eq[1], Eq[2])

    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[-1].lhs.args)

    Eq << Eq[-1].subs(Eq[-2])
            
if __name__ == '__main__':
    prove(__file__)

