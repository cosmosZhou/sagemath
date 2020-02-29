
from sympy.core.symbol import Symbol

from sympy.utility import Ref, Sum, Min, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase
from sympy.core.numbers import oo


@plausible
def apply(G, x, y):
    _, d = x.shape
    i = Symbol('i', integer=True)
    t = Symbol('t', integer=True, nonnegative=True)

    s = IndexedBase('s', (oo,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    x_quote = IndexedBase("x'", (oo, d),
                          definition=Ref[t](Ref[y[t]](Min[y[0:t]](s[t]))))

    return Equality(x_quote[t + 1], x[t + 1] + Min(x_quote[t] + G)), \
        Equality(Min[y[:t + 1]](s[t]), Min(x_quote[t]))


from sympy.utility import check


@check
def prove(Eq):
    d = Symbol('d', integer=True)

    # oo is the length of the sequence
    # d is the number of output labels
    G = IndexedBase('G', (d, d))
    x = IndexedBase('x', (oo, d))
    y = IndexedBase('y', (oo,))

    Eq.s_definition, Eq.x_quote_definition, Eq.recursion, Eq.aggregate = apply(G, x, y)
    
    s = Eq.x_quote_definition.rhs.function.function.base

    t = Eq.recursion.lhs.indices[0] - 1
    Eq << Eq.s_definition.subs(t, t + 1)

    Eq << Eq[-1] - Eq.s_definition

    Eq << Eq[-1].this.rhs.simplifier() + s[t]

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplifier()

    Eq << Eq[-1].this.rhs.args[1].function.bisect(back=1)

    Eq << Eq[-1].this.rhs.args[1].function.as_Ref()

    Eq << Eq[-1].this.rhs.args[1].as_Min()

    Eq << Eq[-1].this.rhs.subs(Eq.x_quote_definition.reversed)

    Eq << Eq.aggregate.this.lhs.bisect(back=1)

    Eq << Eq[-1].this.lhs.as_Ref()

    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)


if __name__ == '__main__':
    prove(__file__)
