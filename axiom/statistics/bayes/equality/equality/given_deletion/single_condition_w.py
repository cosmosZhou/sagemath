
from sympy.core.relational import Equality
from sympy.stats.symbolic_probability import Probability as P
from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from axiom.statistics import bayes
from axiom import algebre
from sympy.stats.rv import pspace


# given: x | y & z = x
# imply: x | y = x
@plausible
def apply(given, wrt=None):    
        
    assert given.is_Equality
    lhs, rhs = given.args
    assert lhs.is_Conditioned
    x, yzw = lhs.args
    assert rhs.is_Conditioned
    _x, w = rhs.args
    assert x == _x

    assert w in yzw.args
    args = [*yzw.args]
    args.remove(w)
    y, z = args
#     assert w in yzw._argset
#     y, z = {*yzw.args} - {w}
    
    if wrt is not None:
        if y.is_Equality:
            y = y.lhs
        if z.is_Equality:
            z = z.lhs
            
        assert wrt in {y, z}
        return Equality(x | wrt.as_boolean() & w, x | w, given=given)
    return Equality(x | y & w, x | w, given=given)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    w = Symbol.w(real=True, random=True)
    
    Eq << apply(Equality(x | y.as_boolean() & z.as_boolean() & w.as_boolean(), x | w), wrt=y)
    
    Eq.xyz_nonzero, Eq.w_nonzero = Eq[0].domain_definition().split()
    
    _, Eq.y_nonzero, Eq.z_nonzero = bayes.inequality.et.apply(Eq.xyz_nonzero).split()
    
    Eq.xy_probability = bayes.theorem.apply(Eq.y_nonzero, var=x | w)
    
    Eq << bayes.inequality.inequality.conditioned.apply(Eq.xyz_nonzero, wrt=w)
    
    Eq << P(x | w, y, z).bayes_theorem(y, z)
    Eq << Eq[-1].as_Or()
    
    Eq << (Eq[-1] & Eq[-3]).split()
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq <<= Eq[-1].lhs.total_probability_theorem(z), Eq[-1].rhs.args[0].total_probability_theorem(z), Eq[-1].integral((pspace(z).symbol,))
    
    Eq << Eq[-3].subs(Eq.xy_probability)
    
    Eq << Eq[-1].subs(Eq[-2]) 
    
    Eq << Eq[-1].subs(Eq[-4])
    
    Eq << algebre.scalar.inequality.equality.apply(Eq[-1], Eq.y_nonzero)
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

