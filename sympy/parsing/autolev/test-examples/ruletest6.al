% ruletest6.al
VARIABLES Q{2}
VARIABLES X,Y,Z
Q1 = X^2 + Y^2
Q2 = X-Y
E = Q1 + Q2
A = EXPLICIT(E)
E2 = COS(X)
E3 = COS(X*Y)
A = TAYLOR(E2, 0:2, X=0)
B = TAYLOR(E3, 0:2, X=0, Y=0)

E = EXPAND((X+Y)^2)
A = EVALUATE(E, X=1, Y=Z)
BM = EVALUATE([E;2*E], X=1, Y=Z)

E = Q1 + Q2
A = EVALUATE(E, X=2, Y=Z^2)

CONSTANTS J,K,L
P1 = POLYNOMIAL([J,K,L],X)
P2 = POLYNOMIAL(J*X+K,X,1)

ROOT1 = ROOTS(P1, X, 2)
ROOT2 = ROOTS([1;2;3])

M = [1,2,3,4;5,6,7,8;9,10,11,12;13,14,15,16]

AM = TRANSPOSE(M) + M
BM = EIG(M)
C1 = DIAGMAT(4, 1)
C2 = DIAGMAT(3, 4, 2)
DM = INV(M+C1)
E = DET(M+C1) + TRACE([1,0;0,1])
F = ELEMENT(M, 2, 3)

A = COLS(M)
BM = COLS(M, 1)
CM = COLS(M, 1, 2:4, 3)
DM = ROWS(M, 1)
EM = ROWS(M, 1, 2:4, 3)
