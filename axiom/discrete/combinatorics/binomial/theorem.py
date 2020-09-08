from sympy.core.symbol import Symbol
from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy import var
from axiom.discrete.combinatorics.binomial import Pascal
from sympy.concrete.summations import Sum

@plausible
def apply(x, y, n=None, free_symbol=None):
    if free_symbol is None:
        k = var(integer=True).k
    else:
        k = free_symbol
    if n is None:
        n = var(integer=True, nonnegative=True).n
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)))
    elif n < 0:
        return None
    else:
        return Equality((x + y) ** n, Sum[k:0:n](binomial(n, k) * x ** k * y ** (n - k)))


from sympy.utility import check


@check
def prove(Eq):
    x = var(integer=True).x
    y = var(integer=True).y
    n = var(integer=True, nonnegative=True).n
    Eq << apply(x, y, n)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << (Eq[-2] * (x + y)).powsimp()

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.distribute()

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.function.powsimp()

    (k, *_), *_ = Eq[-1].rhs.limits
    Eq << Eq[-1].this.rhs.as_two_terms()

    Eq << Eq[-1].this.rhs.args[1].subs(k, k - 1)

    Eq << Eq[-1].subs(Pascal.apply(n + 1, k))

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[0].subs(n, 0)


if __name__ == '__main__':
    prove(__file__)

