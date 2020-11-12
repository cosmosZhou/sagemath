from sympy.core.relational import Unequality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
from sympy import S
from sympy.sets.contains import Contains
from sympy.concrete.expr_with_limits import Exists


# given A & B != Ø
# then Exists[e:B] e in A
@plausible
def apply(given, wrt=None, domain=None):
    assert given.is_Unequality
    AB, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = AB
        AB = emptyset
        emptyset = tmp
    assert AB.is_Intersection
    A, B = AB.args
    if domain is None:
        domain = B
    else:
        if domain == A:
            A, B = B, A
            
    assert domain == B
    if wrt is None:
        wrt = B.element_symbol(A.free_symbols)
    assert wrt.dtype == B.element_type
    return Exists[wrt:B](Contains(wrt, A), given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)

    inequality = Unequality(A & B, S.EmptySet)
    Eq << apply(inequality)

    Eq << (A & B).assertion()

    Eq << (Eq[-1] & inequality)

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()

    Eq << (~Eq[1]).limits_subs(Eq[1].variable, Eq[-1].variable)
    
    Eq << (Eq[-1] & Eq[-3])


if __name__ == '__main__':
    prove(__file__)

