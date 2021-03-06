from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import check, plausible
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.permutation.adjacent import swap1
from sympy.concrete.expr_with_limits import LAMBDA


@plausible
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    if w is None:
        w = Symbol.w(shape=(n, n, n), definition=LAMBDA[j:n](Swap(n, 0, j)))

    assert w.shape == (n, n, n)
    assert w[j].definition == Swap(n, 0, j)
    
    return Equality(LAMBDA[i:n](x[w[j][i] @ LAMBDA[i:n](i)]), LAMBDA[i:n](Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True))))


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(dtype=dtype.integer, shape=(n,))    
    
    Eq << apply(x)    
    
    w = Eq[0].lhs.base
    
    Eq << swap1.equality.apply(x, w)
    
    i, j = Eq[-1].rhs.args[0][1].args
    Eq << Eq[-1].forall((i,), (j,))
    
    _i = i.unbounded
    Eq << Eq[-1].this.lhs.args[1].args[1].limits_subs(i, _i)
    
    Eq << Eq[-1].reference((_i, 0, n - 1))
    

if __name__ == '__main__':
    prove(__file__)
