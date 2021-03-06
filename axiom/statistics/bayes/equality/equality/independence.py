
from sympy.core.relational import Equality, Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes


# given: P(x, y) = P(x) P(y)
# imply: x | y = x
@plausible
def apply(*given):
    equality, inequality = given    
    assert equality.is_Equality
    assert inequality.is_Unequality
    assert inequality.rhs.is_zero
    inequality.lhs.is_Probability 
    x = inequality.lhs.arg
    
    lhs, rhs = equality.args
    assert lhs.is_Probability
    _x, y = lhs.arg.args

    if x != _x:
        _x, y = y, _x
    assert x == _x
    assert rhs == P(x) * P(y)
   
    return Equality(P(y, given=x), P(y), given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    given = Equality(P(x, y), P(x) * P(y))
    
    Eq << apply(given, Unequal(P(x), 0))
    
    Eq << Eq[-1].simplify()
    
    Eq << bayes.theorem.apply(Eq[1], var=y)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1] - Eq[-1].rhs
    
    Eq << Eq[-1].this.lhs.collect(P(x))
    
    Eq << Eq[-1].as_Or()
    
    Eq << (Eq[-1] & Eq[1]).split()
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)
