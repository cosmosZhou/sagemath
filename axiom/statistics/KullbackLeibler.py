from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import GreaterThan
from sympy import log
from sympy.concrete.summations import summation
from sympy.core.function import Function


def KL(p, q, *limit):
    return summation(p * log(p / q), *limit)

@plausible
def apply(p, q):
    x = Symbol('x')
    y = Symbol('y')
    return GreaterThan(KL(p(x, y), q(x, y), (x,), (y,)), KL(p(x), q(x), (x,)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    p = Function('p')
    q = Function('q')
    Eq << apply(p, q)


if __name__ == '__main__':
    prove(__file__)
