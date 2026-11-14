from sympy import totient
from math import gcd
def c(m): return sum(max(0,m+2-2*j) for j in range(0,m-1))
def cp(m): return sum(max(0,m+2-2*j) for j in range(0,m))
def e_of(d):
    if d%2: return 2*d
    if d%4==2: return d
    if d%8==4: return d//4
    return d//2
def kmin(d):
    # brute force: alpha_k(zeta)=1 iff zeta^{2k+1} = (-1)^{k+1}; zeta=exp(2pi i/d): exponent arithmetic mod 2d (in units of pi i/d)
    for k in range(1,4*d+5):
        # zeta^{2k+1} = exp(2pi i (2k+1)/d); (-1)^{k+1}=exp(pi i (k+1))
        # compare 2(2k+1)/d - (k+1) in Z/2  <=> 2(2k+1) - d(k+1) == 0 mod 2d
        if (2*(2*k+1) - d*(k+1)) % (2*d) == 0: return k
    return None
def kmin_paper(d):
    if d%4==0: return None
    if d==2: return 2
    if d%4==3: return (d-1)//2
    if d%4==1: return (3*d-1)//2
    if d%8==2: return (d-2)//4
    if d%8==6: return (3*d-2)//4
for d in range(1,400):
    assert kmin(d)==kmin_paper(d),(d,kmin(d),kmin_paper(d))
print("kmin table ok")
def b(K,d):
    e=e_of(d); tot=0
    if e<=K:
        ms=[len([a for a in range(1,K+1) if a%e==r%e]) for r in range(1,e+1)]
        tot+=sum(c(m) for m in ms[:-1])+cp(ms[-1])
    k=kmin(d)
    if k is not None and k<=K-2: tot+=K-1-k
    return tot
for K in ((8,20,26,40,80) if __name__=="__main__" else ()):
    S=sum(b(K,d)*int(totient(d)) for d in range(1,4*K+1))
    print(K,S,S/K**3)
