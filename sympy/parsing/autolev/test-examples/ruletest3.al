% ruletest3.al
FRAMES A, B
NEWTONIAN N

VARIABLES X{3}
CONSTANTS L

V1> = X1*A1> + X2*A2> + X3*A3>
V2> = X1*B1> + X2*B2> + X3*B3>
V3> = X1*N1> + X2*N2> + X3*N3>

V> = V1> + V2> + V3>

POINTS C, D
POINTS PO{3}

PARTICLES L
PARTICLES P{3}

BODIES S
BODIES R{2}

V4> = X1*S1> + X2*S2> + X3*S3>

P_C_SO> = L*N1>
