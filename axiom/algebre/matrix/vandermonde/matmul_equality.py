from sympy.functions.combinatorial.factorials import binomial

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom.utility import plausible
from sympy.core.relational import Equality
import axiom
from sympy.concrete.expr_with_limits import LAMBDA
from sympy.concrete.summations import Sum
from sympy import Symbol

@plausible
def apply(x, m, n, d, delta):
    i = Symbol.i(domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol.j(domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol.h(integer=True)

    return Equality(LAMBDA[j:m, i](binomial(d, j - i) * (-1) ** (d + i - j)) @ LAMBDA[j, i:m]((i + delta) ** j * x ** i),
                    LAMBDA[j, i]((i + delta) ** j * x ** i) @ LAMBDA[j, i:n](binomial(j, i) * Sum[h:0:d](binomial(d, h) * (-1) ** (d - h) * x ** h * h ** (j - i))))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(domain=Interval(1, oo, right_open=True, integer=True))
    m = Symbol.m(domain=Interval(1, oo, right_open=True, integer=True))
    d = Symbol.d(domain=Interval(0, oo, right_open=True, integer=True))

    i = Symbol.i(domain=Interval(0, m - d, right_open=True, integer=True))
    j = Symbol.j(domain=Interval(0, n, right_open=True, integer=True))
    h = Symbol.h(integer=True)

    delta = Symbol.delta(real=True)
    
    x = Symbol.x(real=True)

    Eq << apply(x, m, n, d, delta)

    Eq << Eq[-1].expand()

    Eq << Eq[-1][i, j]

    Eq << Eq[-1].this.rhs.args[1].limits_swap()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(h, h - i)
    
    Eq.distribute = Eq[-1].this.rhs.distribute()
   
    Eq << Eq.distribute.this.lhs.limits_subs(Eq.distribute.lhs.variable, h)

    Eq << axiom.discrete.combinatorics.binomial.theorem.apply(delta + i, h - i, j).reversed

    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, Eq.distribute.rhs.function.args[-1].variable)

    Eq << Eq.distribute.this.rhs.subs(Eq[-1])

    Eq << Eq[2].reference((j,), (i,))


if __name__ == '__main__':
    prove(__file__)
