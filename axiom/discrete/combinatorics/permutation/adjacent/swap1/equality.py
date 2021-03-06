from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol


@plausible
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol.w(shape=(n, n, n), definition=LAMBDA[j](Swap(n, 0, j)))
#     else:
    assert w.shape == (n, n, n)
    assert w[j].definition == Swap(n, 0, j)
    
    return Equality(x[w[j][i] @ LAMBDA[i:n](i)], Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True)))


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(dtype=dtype.integer, shape=(n,))    
    
    Eq << apply(x)
    
    i = Eq[1].rhs.args[2][0].indices[0]
    Eq << Eq[0][i]

    Eq << Eq[0][i] @ Eq[1].lhs.indices[0].args[1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[1].lhs.this.subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)
