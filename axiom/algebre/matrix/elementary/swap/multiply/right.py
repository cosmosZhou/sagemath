
from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol


@plausible
def apply(x):
    n = x.shape[0]
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j, i](Swap(n, i, j)))
    
    return Equality(x @ w[i, j] @ w[i, j], x)


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices    

    w = Eq[0].lhs.base
    
    Eq << (x @ w[i, j]).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << (Eq[-1] @ w[i, j]).this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].this.rhs.expand()    


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
