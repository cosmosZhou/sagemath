
from sympy.core.relational import Unequal

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P
from axiom.statistics import bayes
from sympy.logic.boolalg import And
from axiom import algebre


# given: P(x, y) != 0
# imply: P(y) != 0
@plausible
def apply(given, wrt=None):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    
    eqs = given.lhs.arg
    assert eqs.is_And
    if wrt is not None:
        lhs, rhs = [], []
        for eq in eqs.args:
            if eq.lhs in wrt:
                rhs.append(eq)
            else:
                lhs.append(eq)
        lhs = And(*lhs)
        rhs = And(*rhs)
        return And(Unequal(P(lhs), 0), Unequal(P(rhs), 0), given=given)            
    else:
        return And(*[Unequal(P(eq), 0) for eq in eqs.args], given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    Eq << apply(Unequal(P(x, y), 0))
    
    Eq.x_marginal_probability, Eq.y_marginal_probability = P(x, y).total_probability_theorem(y), P(x, y).total_probability_theorem(x)
    
    _y = Eq.x_marginal_probability.lhs.variable
    _x = Eq.y_marginal_probability.lhs.variable
    
    Eq << bayes.inequality.strict_greater_than.apply(Eq[0])
    
    Eq <<= Eq[-1].integrate((_y,)), Eq[-1].integrate((_x,))
    
    Eq <<= Eq[-2].subs(Eq.x_marginal_probability), Eq[-1].subs(Eq.y_marginal_probability)
    
    Eq <<= algebre.scalar.strict_greater_than.inequality.apply(Eq[-1]) & algebre.scalar.strict_greater_than.inequality.apply(Eq[-2])
    
    
if __name__ == '__main__':
    prove(__file__)
