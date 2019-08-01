from sympy.concrete import summations, products
from sympy.core.relational import Equality, Relational
import sympy
import os
from sympy.logic.boolalg import BooleanTrue, plausibles_dict, \
    equivalent_ancestor
from sympy.sets.contains import Contains
import traceback
from sympy.matrices.expressions import matexpr
from sympy.functions.elementary import miscellaneous


def init(func):

    def _func(*args, **kwrags):
        Eq.clear()
        func(*args, **kwrags)

    return _func


class Operator:
    stack = []

    def __getitem__(self, key):
        if isinstance(key, tuple):
            limit = []
            for t in key:
                if isinstance(t, slice):
                    if t.step:
                        limit.append((t.start, t.stop, t.step))
                    else:
                        limit.append((t.start, t.stop))
                else:
                    limit.append(t)
        elif isinstance(key, slice):
            if key.step:
                limit = [(key.start, key.stop, key.step)]
            else:
                limit = [(key.start, key.stop)]
        else:
            limit = [(key,)]
        self.stack.append(limit)

        return self


class Sum(Operator):

    def __call__(self, hk):
        if self.stack:
            limits = self.stack.pop()
            for i, limit in enumerate(limits):
                if len(limit) == 2:
                    x, n = limit
                    limits[i] = (x, 0, n - 1)
            return summations.Sum(hk, *limits)
        return summations.Sum(hk)


Sum = Sum()


class Integral(Operator):

    def __call__(self, hk):
        from sympy.integrals import integrals

        limits = self.stack.pop()
        return integrals.Integral(hk, *limits)


Integral = Integral()


class Product(Operator):

    def __call__(self, hk):
        limit = self.stack.pop()
        return products.Product(hk, limit)


Product = Product()


class Min(Operator):

    def __call__(self, hk):
        from sympy.functions.elementary.miscellaneous import Minimum
        if self.stack:
            limit = self.stack.pop()
            return Minimum(hk, *limit)
        return Minimum(hk)


Min = Min()


# Reference operator &, or [x]f[x]
class Ref(Operator):

    def __call__(self, hk):
        limit = self.stack.pop()

        return miscellaneous.Ref(hk, *limit)


Ref = Ref()

sympy.init_printing()

# https://www.programiz.com/python-programming/operator-overloading
Eq = []

batch_proving = False


class cout:

    def __init__(self):
        from util.utility import Text
        path = os.path.dirname(__file__) + '/../../latex/txt/latex.txt'

        self.file = Text(path)
        self.file.clear()
#         self.file.write(["$$\\begin{align}", "\\end{align}$$"])

    def add_to_list(self, rhs):
        if rhs not in Eq:
            Eq.append(rhs)
            return len(Eq) - 1
        else:
            index = Eq.index(rhs)
            plausible = rhs.plausible
            if plausible is False:
                Eq[index].plausible = False
            elif plausible is None:
                Eq[index].plausible = True
            else:
                eq = Eq[index]
                if id(rhs.equivalent) != id(eq):
                    rhs_equivalent = equivalent_ancestor(rhs)
                    if eq != rhs_equivalent:
                        if not isinstance(rhs_equivalent, set):
                            rhs_equivalent.equivalent = eq

            return index

    def __lshift__(self, rhs):

        if isinstance(rhs, (list, tuple)):
            for arg in rhs:
                self.__lshift__(arg)
            return self

        if isinstance(rhs, identity):
            rhs = rhs.expr

        if batch_proving:
            if isinstance(rhs, (Relational, Contains)):
                self.add_to_list(rhs)
            return self

        try:
            latex = rhs.latex
        except Exception as e:
            print(e)
            traceback.print_exc()
            latex = ''

        infix = str(rhs)
        if isinstance(rhs, (Relational, Contains)):
            index = self.add_to_list(rhs)

            tag = r'\tag*{Eq[%d]}' % index
#             if rhs.given is not None:
#                 if isinstance(rhs.given, (list, tuple)):
#                     tag += r'\Leftarrow ' + ','.join('Eq[%d]' % Eq.index(given) for given in rhs.given)
#                 else:
#                     tag += r'\Leftarrow Eq[%d]' % Eq.index(rhs.given)
#             elif rhs.equivalent is not None:
#                 if isinstance(rhs.equivalent, (list, tuple)):
#                     tag += r'\Leftrightarrow ' + ','.join('Eq[%d]' % Eq.index(equivalent) for equivalent in rhs.equivalent)
#                 else:
#                     tag += r'\Leftrightarrow Eq[%d]' % Eq.index(rhs.equivalent)
#
#             tag += '}'
            latex += tag
            for_clause = rhs.for_clause
            with_clause = rhs.with_clause
            if for_clause is not None:
                latex += r',\ for\ '
                if isinstance(for_clause, (tuple, list)):
                    latex += ',\ '.join(var.domain_latex() for var in for_clause)

                else:
                    latex += for_clause.domain_latex()
            if with_clause is not None:
                latex += r',\ with\ '
                if isinstance(with_clause, (tuple, list)):
                    latex += ',\ '.join(var.domain_latex() for var in with_clause)

                else:
                    latex += with_clause.domain_latex()
#             latex += r'\\'
            infix = 'Eq[%d] : %s' % (index, infix)

#         else:
#             latex += r'\\'

        self.file.append(r'\[%s\]' % latex)
#         self.file.insert(-2, latex)

        print(infix)
        return self


cout = cout()


def show_latex():
    import matplotlib.pyplot as plt
    ax = plt.subplot(111)
#     defaultFamily
    ax.text(0.1, 0.8, r"$\int_a^b f(x)\mathrm{d}x$", fontsize=30, color="red")
    ax.text(0.1, 0.3, r"$\sum_{n=1}^\infty\frac{-e^{i\pi}}{2^n}!$", fontsize=30)
    plt.show()
# https://www.cnblogs.com/chaosimple/p/4031421.html


def test_latex_parser():
    from sympy.parsing.latex import parse_latex
    expr = parse_latex(r"\frac {1 + \sqrt {\a}} {\b}")  # doctest: +SKIP
    print(expr)


def topological_sort(graph):
    in_degrees = {u : 0 for u in graph}

    vertex_num = len(in_degrees)
    for u in graph:
        for v in graph[u]:
            in_degrees[v] += 1
    Q = [u for u in in_degrees if in_degrees[u] == 0]
    Seq = []
    while Q:
        u = Q.pop()
        Seq.append(u)
        for v in graph[u]:
            in_degrees[v] -= 1
            if in_degrees[v] == 0:
                Q.append(v)

    if len(Seq) == vertex_num:
        return Seq

#         print("there's a circle.")
    return None


def plausible():
    s = traceback.extract_stack()
    if s[-2][0] == s[-3][0]:
        return True
    return None


class identity:

    def __init__(self, lhs):
        self.lhs = lhs
        self.rhs = lhs

        self.func = []
        self._args = []
        self.index = []

    @property
    def expr(self):
        return Relational.__new__(Equality, self.lhs, self.rhs)

    def __call__(self, *args, **kwargs):
        if self.rhs.__name__ == 'subs':
            from sympy.concrete.summations import Sum
            from sympy.integrals.integrals import Integral
            if isinstance(self.rhs.__self__, Sum) or isinstance(self.rhs.__self__, Integral):
                if len(args) == 2:
                    (x, *_), *_ = self.rhs.__self__.limits
                    # domain might be different!
                    assert args[0].name == x.name
            else:
                assert len(args) == 1 and isinstance(args[0], Equality)

        obj = self.rhs(*args, **kwargs)

        for i in range(-1, -len(self.func) - 1, -1):
            self._args[i][self.index[i]] = obj

            if i == -len(self.func):
                obj = self.func[i](*self._args[i], equivalent=self.eq if self.eq.plausible else None)
            else:
                obj = self.func[i](*self._args[i])

            obj = obj.simplifier()
        self.rhs = obj
        return self

    def __getattr__(self, method):
        obj = getattr(self.rhs, method)
        if not callable(obj):
            self.func.append(self.rhs.func)
            self._args.append([*self.rhs.args])
            if not isinstance(obj, tuple):
                self.index.append(self.rhs.args.index(obj))

        self.rhs = obj
        return self

    def __str__(self):
        return str(self.rhs)

    @property
    def latex(self):
        return self.rhs.latex

    def __getitem__(self, j):
        self.rhs = self.rhs[j]
        self.index.append(j)
        return self

    def __iter__(self):
        return iter(self.rhs)


def check(func):

    def _func():
        Eq.clear()
        func()
        plausibles = plausibles_dict(Eq)
        if plausibles:
            print('plausibles_dict:')
            for index, eq in plausibles.items():
                print("Eq[%d] : %s" % (index, eq))

            return False
        return True

    return _func


# https://en.wikipedia.org/wiki/Topological_sorting#
# http://ctex.math.org.cn/blackboard.html
# https://tex.stackexchange.com/questions/256644/convert-latex-to-sympy-format
# https://cloud.tencent.com/developer/article/1057779
# http://www.wiris.com/plugins/demo/ckeditor4/php/
# https://docs.wiris.com/en/mathtype/mathtype_web/sdk-api/embedding
# http://www.wiris.com/editor/demo/en/developers
# https://zh.numberempire.com/latexequationeditor.php
# https://www.numberempire.com/latexequationeditor.php
# ..................................................\\

# http://www.sagemath.org/download-source.html
# https://www.sagemath.org/
if __name__ == '__main__':
    ...
