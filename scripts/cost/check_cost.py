# Exact checks of every inequality used in FibZeta/Cost (rationals / integers).
from fractions import Fraction as Fr
from math import gcd, log
from sympy import totient, divisors, mobius
import mpmath as mp

def eW(d): return 2*d//gcd(d+4, 2*d)          # order of -zeta^2, zeta = exp(2 pi i/d)
def alpha(d,k): return (d*(k+1) + 2*(2*k+1)) % (2*d) == 0
def cW(m): return sum(max(0, m+2-2*j) for j in range(max(m-1,0)))
def cWp(m): return sum(max(0, m+2-2*j) for j in range(m))
def csize(K,e,r): return sum(1 for a in range(1,K+1) if a%e == r%e)
def Wc(K,e): return sum(cW(csize(K,e,r)) for r in range(1,e)) + cWp(csize(K,e,e))
def nW(K,d):
    e = eW(d)
    return Wc(K,e) if 1 <= e <= K else 0
def nAlpha(K,d):
    ks = [k for k in range(1, K-1) if alpha(d,k)]
    return K-1-ks[0] if ks else 0
def nExp(K,d): return nW(K,d) + nAlpha(K,d)

# 4: cluster cost bounds
for m in range(1,400):
    assert 4*cW(m)+16 <= 16*m + max(m-5,0)**2, m
    assert cWp(m) <= cW(m)+4
    assert cW(m+2) == cW(m) + m + 4 + max(4-m,0)
assert cWp(0) == 0 and cW(0) == 0
# 1, 6: W root count; 2: alpha count
for e in range(1,300):
    ds = [d for d in range(1, 4*e+50) if eW(d) == e]
    assert sum(totient(d) for d in ds) <= 2*totient(e), e
    assert len(ds) <= 8 and all(4*e % d == 0 and e <= 2*d for d in ds)
for j in range(0,150):
    assert sum(totient(d) for d in range(1, 4*j+20) if alpha(d,j)) <= 2*j+1, j
# 3: W cost per e
for K in range(1,90):
    for e in range(1,K+1):
        assert 4*Wc(K,e) + 16*e <= 16*K + e*max(K//e-4,0)**2 + 16, (K,e)
        assert e*max(K//e-4,0) <= max(K-4*e,0)
# sieve
qs = [1,2,3,5,7,6,10,14,15,21,35,30,42,70,105,210]
def cq(q): return Fr(int(mobius(q)), q)
def w(e):
    r = Fr(1)
    for p in (2,3,5,7):
        if e % p == 0: r *= Fr(p-1,p)
    return r
for e in range(0,500):
    assert w(e) == sum(cq(q) for q in qs if e % q == 0)
    if e: assert totient(e) <= e*w(e)
mu = sum(cq(q)/q for q in qs); print("mu =", mu, float(mu))
const = mu*Fr(4,3) + mu*Fr(1,24) + Fr(1,3); print("cubic constant =", const, float(const))
assert const < Fr(121,100)
# per-q errors T1, T2
for q in qs:
    for K in range(0,700):
        S1 = sum(Fr(q*k*(K-q*k)) for k in range(1, K//q+1))
        assert abs(S1 - Fr(K**3, 6*q)) <= Fr(K*q+q*q, 6), (q,K)
        S2 = sum(Fr(max(K-4*q*k,0)**2) for k in range(1, K//q+1))
        assert abs(S2 - Fr(K**3, 12*q)) <= K*K + q*K + 16*q*q, (q,K)
# 5: the full phi-weighted sum vs. the bound used
def T1(K): return sum(w(e)*e*(K-e) for e in range(1,K+1))
def T2(K): return sum(w(e)*max(K-4*e,0)**2 for e in range(1,K+1))
for K in list(range(1,41)) + [60, 80]:
    tot = sum(nExp(K,d)*totient(d) for d in range(1,4*K+1))
    W = sum(nW(K,d)*totient(d) for d in range(1,4*K+1))
    A = sum(nAlpha(K,d)*totient(d) for d in range(1,4*K+1))
    assert A <= sum((K-1-j)*(2*j+1) for j in range(1,K-1)) <= Fr(K**3,3)
    assert W <= 8*T1(K) + T2(K)/2 + 8*sum(range(1,K+1))
    assert T1(K) <= mu*Fr(K**3,6) + sum(Fr(K*q+q*q,6)/q for q in qs)
    assert T2(K) <= mu*Fr(K**3,12) + sum(Fr(K*K+q*K+16*q*q)/q for q in qs)
    ntot = sum(nExp(K,d) for d in range(1,4*K+1))
    if K % 10 == 0 or K < 4:
        print(K, "sum n phi / K^3 =", float(tot)/K**3, " sum n / (K^2(1+logK)) =", ntot/(K*K*(1+log(K))))
# 7: cyclotomic error F(d)
mp.mp.dps = 60
t = (mp.sqrt(5)-1)/2; ph = 1/t
def Phi(d, x):
    r = mp.mpf(1)
    for a in divisors(d):
        r *= (x**a - 1)**int(mobius(d//a))
    return r
mx = 0
for d in range(1, 300):
    F = mp.log(abs(Phi(d,t))) + mp.log(abs(Phi(d,-ph))) - totient(d)*mp.log(ph)
    mx = max(mx, abs(F))
print("max |F(d)| d<300:", mx)
print("all checks passed")
