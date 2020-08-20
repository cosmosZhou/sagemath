
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, identity

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Shift
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Shift(n, i, j)))
    else:
        assert w[i, j] == Shift(n, i, j)
    
    return Equality(x @ w[i, j] @ w[i, j].T, x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    i = Symbol('i', domain=Interval(0, j - 1, integer=True))    
    k = Symbol('k', domain=Interval(0, n - 1, integer=True) - Interval(i, j, integer=True))
    
    assert KroneckerDelta(i, k) == 0
            
    x = Symbol('x', shape=(n,), real=True)
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices    
    

    w = Eq[0].lhs.base
    
    Eq << identity(x @ w[i, j]).subs(Eq[0])
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=i)
    
    Eq << Eq[-1] @ w[i, j].T
    
    Eq << Eq[-1].this.rhs.expand()    
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=i)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
