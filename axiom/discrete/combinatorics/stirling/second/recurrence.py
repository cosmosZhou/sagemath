from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality, StrictGreaterThan, \
    Unequality
from axiom.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import image_set, Interval, Union
from sympy.sets.contains import Subset, Contains
from sympy.functions.elementary.piecewise import Piecewise
from axiom import sets, discrete
from sympy.sets.conditionset import conditionset
from sympy.concrete.expr_with_limits import UNION, LAMBDA
from sympy.core.numbers import oo


@plausible
def apply(n, k):
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    Eq.stirling2 = Eq[0].lhs.this.definition
    Eq.stirling0 = Eq[0].rhs.args[1].this.definition
    Eq.stirling1 = Eq[0].rhs.args[0].args[1].this.definition

    s2 = Symbol.s2(definition=Eq.stirling2.rhs.arg)
    Eq << s2.this.definition
    s2_quote = Symbol.s_quote_2(definition=Eq.stirling2.rhs.arg.limits[0][1])
    Eq.stirling2 = Eq.stirling2.subs(Eq[-1].reversed)

    s0 = Symbol.s0(definition=Eq.stirling0.rhs.arg)
    Eq << s0.this.definition
    s0_quote = Symbol.s_quote_0(definition=Eq.stirling0.rhs.arg.limits[0][1])
    Eq.stirling0 = Eq.stirling0.subs(Eq[-1].reversed)

    s1 = Symbol.s1(definition=Eq.stirling1.rhs.arg)
    Eq << s1.this.definition
    s1_quote = Symbol("s'_1", definition=Eq.stirling1.rhs.arg.limits[0][1]) 
    Eq.stirling1 = Eq.stirling1.subs(Eq[-1].reversed)
    e = Symbol.e(dtype=dtype.integer.set)

    Eq << s2.this.bisect(conditionset(e, Contains({n}, e), s2))

    Eq.s2_abs = Eq[-1].abs()

    Eq.s2_abs_plausible = Eq[0].subs(Eq.stirling2, Eq.stirling0, Eq.stirling1)

    Eq << discrete.combinatorics.stirling.second.mapping.s2_A.apply(n, k, s2)
    
    A = Eq[-1].rhs.function.base

    Eq << discrete.combinatorics.stirling.second.mapping.s2_B.apply(n, k, s2)
    B = Eq[-1].rhs

    Eq.s2_abs = Eq.s2_abs.subs(Eq[-1], Eq[-2])

    Eq << discrete.combinatorics.stirling.second.mapping.s0_B.apply(n, k, s0, B)

    Eq << Eq.s2_abs.subs(Eq[-1].reversed)

    Eq.A_union_abs = Eq.s2_abs_plausible.subs(Eq[-1])

    Eq << discrete.combinatorics.stirling.second.nonoverlapping.apply(n, k, A)

    Eq << Eq.A_union_abs.subs(Eq[-1])
    
    Eq << discrete.combinatorics.stirling.second.mapping.s1_Aj.apply(n, k, s1, A).reversed
     
    Eq << Eq[-1].sum(*Eq[-2].lhs.limits)


if __name__ == '__main__':
    prove(__file__)

