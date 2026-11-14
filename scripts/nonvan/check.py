# Numerical sanity checks for FibZeta/NonVan (mpmath, 60 digits).
from mpmath import mp, mpf, sqrt, nsum, inf
mp.dps = 60
t = (sqrt(5)-1)/2
rho, w = -t, -t**2
alpha = lambda k: rho*w**k
nu = lambda k: k*(k+1)*alpha(k)/(1-alpha(k))
psi = lambda N: t**(3*N)/(1-w**N)**3
Xi = nsum(lambda N: psi(int(N)), [1, inf])
S = lambda a: sum(psi(N) for N in range(1, a+1))
kern = lambda n, z: 2*rho**(n+1)*w**(n+1)*z/(z-w**(n+1))**3   # n >= 0
F = lambda z: nsum(lambda n: kern(int(n), z), [0, inf])
# 1. node values  F(x_a) = 2 t^a (Xi - S_a)
for a in range(1, 6):
    x = w**(-a)
    print('node', a, F(x) - 2*t**a*(Xi - S(a)))
# 2. F(1/u) = sum_k nu_k u^{k+1}
for u in [mpf('0.3'), mpf('-0.7'), mpf('0.95')]:
    print('ser', u, F(1/u) - nsum(lambda k: nu(int(k))*u**(int(k)+1), [0, inf]))
# 3. shift: kern(n+N, y) = rho^N w^-N kern(n, y/w^N)
y = mpf('0.123')
for N in [1, 2, 3]:
    print('shift', N, kern(5+N, y) - rho**N*w**(-N)*kern(5, y/w**N))
# 4. cubic pole residue: (z-a)^3 F(z) -> 2 rho^{m+1} w^{2(m+1)}, a=w^{m+1}
for m in [1, 3]:
    a = w**(m+1); z = a*(1+mpf(10)**-20)
    print('pole', m, (z-a)**3*F(z), 2*rho**(m+1)*w**(2*(m+1)))
