from sympy.core.relational import Unequality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype

from sympy import S
from sympy.sets.contains import Contains
from sympy.concrete.expr_with_limits import Exists


# given A & B != emptyset
# then Exists[e:B] e in A
@plausible
def apply(given):
    assert given.is_Unequality
    AB, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = AB
        AB = emptyset
        emptyset = tmp
    assert AB.is_Intersection
    A, B = AB.args
    e = B.element_symbol(A.free_symbols)
    return Exists(Contains(e, A), (e, B), given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    inequality = Unequality(A & B, S.EmptySet)
    Eq << inequality
    Eq << apply(inequality)

    Eq << (A & B).assertion()

    Eq << (Eq[-1] & inequality)

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()

    Eq << (~Eq[1] & Eq[-2])


if __name__ == '__main__':
    prove(__file__)

