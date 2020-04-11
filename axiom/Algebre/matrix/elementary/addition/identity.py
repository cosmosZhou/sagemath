
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Identity, Addition


@plausible
def apply(x, lamda, w=None):
    n = x.shape[0]    
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Addition(n, lamda, i, j)))
        w_quote = IndexedBase("w'", integer=True, shape=(n, n, n, n), definition=Ref[i, j](Addition(n, -lamda, i, j)))
    else:
        assert w[i, j] == Addition(n, lamda, i, j)
        assert w_quote[i, j] == Addition(n, -lamda, i, j)

    return Equality(w_quote[i, j] @ w[i, j], Identity(n))    


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    lamda = Symbol('lamda', real=True)    
    Eq << apply(x, lamda)
    
    Eq << Eq[0] @ Eq[1]    


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
