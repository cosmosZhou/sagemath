VARIABLES X, Y
CONSTANTS A{1:2, 1:2}, B{1:2}
EQN[1] = A11*x + A12*y - B1
EQN[2] = A21*x + A22*y - B2
INPUT A11=2, A12=5, A21=3, A22=4, B1=7, B2=6
CODE ALGEBRAIC(EQN, X, Y) some_filename.c
