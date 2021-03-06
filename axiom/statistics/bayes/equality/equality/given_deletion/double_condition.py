
from sympy.core.relational import Equality

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from axiom.statistics import bayes
from sympy.stats.rv import pspace
from axiom import algebre


# given: x | y & z = x | y
# imply: x | z = x
@plausible
def apply(*given):
    eq_x_given_yz, z_given_y = given
    assert z_given_y.is_Equality
    assert z_given_y.lhs.is_Conditioned
    z, y = z_given_y.lhs.args
    assert z == z_given_y.rhs
    
    assert eq_x_given_yz.is_Equality
    lhs, rhs = eq_x_given_yz.args
    assert lhs.is_Conditioned
    assert rhs.is_Conditioned
    
    x, yz = lhs.args
    _x, _y = rhs.args
    assert x == _x
    assert y == _y

    _y, _z = yz.args
    
    if _y != y:
        _z, _y = _y, _z    
    assert _z == z or _z == z.as_boolean()
    assert _y == y    
    
    return Equality(x | z, x, given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equality(x | y.as_boolean() & z.as_boolean(), x | y), Equality(z | y, z))
    
    Eq.yz_nonzero, Eq.y_nonzero = Eq[0].domain_definition().split()
    
    _, Eq.z_nonzero = bayes.inequality.et.apply(Eq.yz_nonzero).split()
    
    Eq << bayes.theorem.apply(Eq.yz_nonzero, var=x)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << bayes.theorem.apply(Eq.y_nonzero, var=z)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.xy_probability = bayes.theorem.apply(Eq.y_nonzero, var=x)
    
    Eq << Eq[-1].subs(Eq.xy_probability.reversed)
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1].lhs.total_probability_theorem(y).subs(bayes.theorem.apply(Eq.z_nonzero, var=x))
    
    Eq << Eq[-2].integrate((pspace(y).symbol,)).subs(Eq[-1])
    
    Eq << Eq.xy_probability.lhs.total_probability_theorem(y)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << algebre.scalar.inequality.equality.apply(Eq[-1], Eq.z_nonzero)


if __name__ == '__main__':
    prove(__file__)
