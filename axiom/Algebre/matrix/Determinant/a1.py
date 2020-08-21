from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.matrices.expressions.determinant import Determinant
from sympy.concrete.products import Product
from sympy.concrete.expr_with_limits import Ref
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.concrete.summations import Sum 
from sympy.core.numbers import oo


@plausible
def apply(n, a):
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)
    return Equality(Determinant(1 + Ref[i:n, j:n](a[i] * KroneckerDelta(i, j))),
                    (1 + Sum[i:0:n - 1](1 / a[i])) * Product[i:0:n - 1](a[i]))


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True, positive=True)
    a = Symbol('a', shape=(oo,), complex=True, zero=False)
    Eq << apply(n, a)
    
    Eq << Eq[-1].subs(n, 1)
    
    Eq << Eq[-1].this.lhs.arg.args[1].as_Matrix()
    
    Eq << Eq[-1].this.rhs.args[1].doit()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[0].subs(n, n + 1)
 

if __name__ == '__main__':
    prove(__file__)

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html