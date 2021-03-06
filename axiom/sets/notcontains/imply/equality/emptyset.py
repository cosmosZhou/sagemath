from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy.sets.contains import NotContains
from sympy import Symbol
from axiom import sets


# given e not in S
@plausible
def apply(given):
    assert given.is_NotContains
    e, s = given.args
    return Equality(e.set & s, S.EmptySet, given=given)


from axiom.utility import check


@check
def prove(Eq):
    s = Symbol.s(dtype=dtype.integer, given=True)
    e = Symbol.e(integer=True, given=True)

    Eq << apply(NotContains(e, s))

    Eq << ~Eq[-1]
    
    Eq << sets.inequality.imply.exists.overlapping.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    prove(__file__)

