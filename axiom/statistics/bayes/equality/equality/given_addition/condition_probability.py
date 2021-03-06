
from sympy.core.relational import Equality, Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from axiom import algebre


# given: x | y = x
# imply: x | y & z = x | z
@plausible
def apply(*given):
    equality, unequal = given
    assert unequal.is_Unequality
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero
    assert unequal.lhs.arg.is_Conditioned
    z, _y = unequal.lhs.arg.args
        
    assert equality.is_Equality
    lhs, rhs = equality.args
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs
    
    if _y != y:
        _y, z = z, _y
        
    assert _y == y    
    
    return Equality(x | y & z, x | z, given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equality(x | y, x), Unequal(P(z | y), 0))
    
    Eq << P(x | y, z).bayes_theorem(z)    
    Eq << Eq[-1].as_Or()

    Eq << (Eq[-1] & Eq[1]).split()

    Eq << Eq[-1].subs(Eq[0])
    
    Eq << bayes.inequality.inequality.marginal.apply(Eq[1])
    
    Eq << bayes.theorem.apply(Eq[-1], var=x)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << algebre.scalar.inequality.equality.apply(Eq[-1], Eq[-3])
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)
