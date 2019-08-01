% ruletest8.al
FRAMES A
CONSTANTS C{3}
A>> = EXPRESS(1>>,A)
PARTICLES P1, P2
BODIES R
R_A = [1,1,1;1,1,0;0,0,1]
POINT O
MASS P1=M1, P2=M2, R=MR
INERTIA R, I1, I2, I3
P_P1_O> = C1*A1>
P_P2_O> = C2*A2>
P_RO_O> = C3*A3>
A>> = EXPRESS(I_P1_O>>, A)
A>> = EXPRESS(I_P2_O>>, A)
A>> = EXPRESS(I_R_O>>, A)
A>> = EXPRESS(INERTIA(O), A)
A>> = EXPRESS(INERTIA(O, P1, R), A)
A>> = EXPRESS(I_R_O>>, A)
A>> = EXPRESS(I_R_RO>>, A)

P_P1_P2> = C1*A1> + C2*A2>
P_P1_RO> = C3*A1>
P_P2_RO> = C3*A2>

B> = CM(O)
B> = CM(O, P1, R)
B> = CM(P1)

MOTIONVARIABLES U{3}
V> = U1*A1> + U2*A2> + U3*A3>
U> = UNITVEC(V> + C1*A1>)
V_P1_A> = U1*A1>
A> = PARTIALS(V_P1_A>, U1)

M = MASS(P1,R)
M = MASS(P2)
M = MASS()