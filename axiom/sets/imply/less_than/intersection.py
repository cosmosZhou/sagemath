from sympy.core.relational import LessThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Intersection
from sympy import Symbol
from axiom import sets


@plausible
def apply(A, B):
    return LessThan(abs(Intersection(A, B)), abs(A))


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.equality.inclusion_exclusion_principle.apply(A, B).reversed
    
    Eq << sets.imply.greater_than.apply(B, A)
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << Eq[-1] - Eq[-1].lhs.args[1]
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

