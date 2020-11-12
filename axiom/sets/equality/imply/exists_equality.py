from sympy.core.relational import Equality , StrictGreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy.concrete.expr_with_limits import Exists
from axiom import sets, algebre
# given: |S| = 1
# Exists[x:S] ({x}) = S


@plausible
def apply(given):
    assert given.is_Equality
    S_abs, one = given.args
    
    assert S_abs.is_Abs and one == 1
    S = S_abs.arg
    x = S.element_symbol()
    return Exists(Equality(x.set, S), (x,), given=given)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(dtype=dtype.integer)

    Eq << apply(Equality(abs(S), 1))
    
    Eq << StrictGreaterThan(abs(S), 0, plausible=True)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << sets.strict_greater_than.imply.inequality.apply(Eq[-1])
    
    Eq << sets.inequality.imply.exists.contains.apply(Eq[-1])
    
    Eq << Eq[-1].apply(sets.contains.imply.subset, simplify=False)
    
    Eq << Eq[-1].apply(sets.subset.equality.imply.equality, Eq[0])


if __name__ == '__main__':
    prove(__file__)


