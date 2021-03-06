from sympy.core.relational import Equality

from axiom.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol


@plausible
def apply(x, d, w=None):
    n = x.shape[0]
    assert d.shape == (n,)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    k = Symbol.k(integer=True)

    if w is None:
        w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j:n, i:n](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    return Equality(x[d @ w[i, j, k]], LAMBDA[k:n](x[d[k]]) @ w[i, j, k])


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(complex=True, shape=(n,))
    d = Symbol.d(integer=True, shape=(n,))
    
    Eq << apply(x, d)        
    
    k = Eq[-1].rhs.args[1].indices[-1]

    d = Eq[-1].lhs.indices[0].args[0]
        
    Eq << Eq[-1].rhs.this.subs(Eq[0][k]).this.rhs.expand()
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].lhs.indices[0].this.subs(Eq[0][k]).this.rhs.expand()
    
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)
