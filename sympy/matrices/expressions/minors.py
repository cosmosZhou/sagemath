from __future__ import print_function, division

from sympy.core.sympify import _sympify
from sympy.core import S, Basic
from sympy.matrices.expressions.matexpr import MatrixExpr


class Minors(MatrixExpr):
    """
    The minors of a matrix expression

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the minors, use the ``.minors()``
    method of matrices.

    """
    is_Minors = True

    def __new__(cls, mat):        
        mat = _sympify(mat)
        return Basic.__new__(cls, mat)

    @property
    def arg(self):
        return self.args[0]

    @property
    def shape(self):
        return self.arg.shape

    def doit(self, **hints):
        wolfram = hints.get("wolfram", None)
        if wolfram:
            return self._eval_wolfram(wolfram)
        
        try:
            return self.arg._eval_minors()
        except:
            return self

# Needs["Combinatorica`"]
# mat = Array[Subscript[A, ##] &, {10, 10}, 0]
# Block[{i = 3, j = 7}, 
#  Cofactor[mat, {i, j}] == 
#   Map[Reverse, Minors[mat], {0, 1}][[i, j]]*(-1)^(i + j)]