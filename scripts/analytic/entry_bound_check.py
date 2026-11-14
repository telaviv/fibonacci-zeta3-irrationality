# Numerical sanity check of the triple-root entry bound used in FibZeta/Analytic (Prop 2):
#   |L(B_i B_j / D_K)| <= (64/3) (i+j+1)^2 2^(i+j) r^(a_i+a_j),  r = t^2,
# and of Delta_K(Xi) = det[L(B_i B_j/D_K)] vs t^(2 b_K).
from mpmath import mp, mpf, sqrt, diff, matrix, det, log
mp.dps = 80
t = (sqrt(5)-1)/2; w = -t**2; rho = -t; r = t**2
def B(j, s):
    p = mpf(1)
    for u in range(1, j+1):
        p *= (s - w**((u+2)//3))
    return p
def D(K, s):
    p = mpf(1)
    for a in range(1, K+1):
        p *= (1 - w**a*s)
    return p
def aj(j): return sum((u+2)//3 for u in range(1, j+1))
def L(h, nmax=120):
    tot = mpf(0)
    for n in range(1, nmax):
        s = w**n
        d1 = diff(h, s, 1); d2 = diff(h, s, 2)
        tot += rho**n*(s**2*d2 + 2*s*d1)
    return tot
worst = 0
for K in range(1, 6):
    M = matrix(K, K)
    for i in range(K):
        for j in range(K):
            v = L(lambda s: B(i, s)*B(j, s)/D(K, s), 60)
            M[i, j] = v
            bound = mpf(64)/3*(i+j+1)**2*2**(i+j)*r**(aj(i)+aj(j))
            worst = max(worst, abs(v)/bound)
    bK = 2*sum(aj(j) for j in range(K))
    print(K, "det", mp.nstr(det(M), 8), "t^(2bK)", mp.nstr(t**(2*bK), 8))
print("max ratio entry/bound", mp.nstr(worst, 6))
