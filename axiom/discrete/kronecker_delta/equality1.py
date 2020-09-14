from sympy import var
from sympy.sets.sets import FiniteSet
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.sets.contains import Contains


@plausible
def apply(given):
    assert given.is_Contains
    x, domain = given.args
    assert domain == FiniteSet(0, 1)
        
    return Equality(KroneckerDelta(1, x), x, given=given)


from sympy.utility import check


@check
def prove(Eq):
    x = var(integer=True).x
    given = Contains(x, {0, 1})
    
    Eq << apply(given)
    
    Eq << Eq[-1].this.lhs.as_Piecewise()
    
    Eq << Eq[-1].as_Or()
    
    


if __name__ == '__main__':
    prove(__file__)
