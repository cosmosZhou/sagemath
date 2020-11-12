
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol


@plausible
def apply(*given):
    notcontains1, notcontains2 = given
    assert notcontains1.is_Contains    
    assert notcontains2.is_Contains
    
    e, A = notcontains1.args
    _e, B = notcontains2.args
    assert e == _e
    
    return Contains(e, A & B, given=given)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True)
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)    

    Eq << apply(Contains(e, A), Contains(e, B))
    
    Eq << Eq[-1].split()
    
if __name__ == '__main__':
    prove(__file__)

