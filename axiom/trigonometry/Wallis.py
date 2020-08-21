from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.core.singleton import S
from sympy.functions.elementary.trigonometric import cos, sin
from sympy.utility import plausible
from sympy.core.sympify import sympify
from sympy.functions.special.beta_functions import beta
from axiom.trigonometry import sine
from sympy.integrals.integrals import Integral


@plausible
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol("x", real=True)
    return Equality(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    beta(m / 2, n / 2) / 2)


from sympy.utility import check


@check(wolfram=True)
def prove(Eq, wolfram):
    m = Symbol("m", integer=True, positive=True)
    n = Symbol("n", integer=True, positive=True)

    Eq << apply(m, n)

    (x, *_), *_ = Eq[0].lhs.limits

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[1].subs(m, 1)

    Eq << sine.Wallis.apply(n)

    Eq << Eq[1].subs(m, m + 2)

    Eq << Eq[-1].this.lhs.by_parts(u=cos(x) ** m, wolfram=wolfram)

    Eq << Eq[-1] / (m / n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[1].subs(n, n + 2).expand(func=True)

    Eq << Eq[1].subs(m, 2)

    Eq << Eq[-1].this.lhs.doit(manul=True, wolfram=wolfram)

    Eq << Eq[-1].this.rhs.expand(func=True)


if __name__ == '__main__':
    prove(__file__)

