# symbolic error terms for the per-q closed forms (T1, T2)
import sympy as sp
K,s,q,p = sp.symbols('K s q p', nonnegative=True)
# T1: x = q n = K - s, 0<=s<q;  6q*S1 = x(x+q)(3K-2x-q)
x = K - s
e1 = sp.expand(x*(x+q)*(3*K-2*x-q) - K**3)
print("6q*S1 - K^3 =", sp.collect(e1, K))
# T2: y = p m = K - s, 0<=s<p, p=4q;  p*S2 = y K^2 - K y (y+p) + y(y+p)(2y+p)/6 ; main K^3/3
y = K - s
e2 = sp.expand(y*K**2 - K*y*(y+p) + y*(y+p)*(2*y+p)/6 - K**3/3)
print("p*S2 - K^3/3 =", sp.collect(e2, K))
