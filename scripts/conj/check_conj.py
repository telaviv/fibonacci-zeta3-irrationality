# Numerical checks for the ConjBound proof plan (tau = -phi, X = -Xi).
import sys; sys.path.insert(0,'..')
from mpmath import mp, mpf, sqrt, nsum, inf, binomial
mp.dps=200
phi=(1+sqrt(5))/2; t=1/phi; w=-t**2
Xi=nsum(lambda N: t**(3*N)/(1-w**N)**3,[1,inf])
def polymul(a,b):
    r=[mpf(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]+=x*y
    return r
def polydiv(num, den):
    num=num[:]; q=[mpf(0)]*max(1,len(num)-len(den)+1)
    for i in range(len(num)-len(den),-1,-1):
        c=num[i+len(den)-1]/den[-1]; q[i]=c
        for j in range(len(den)): num[i+j]-=c*den[j]
    return q
tau=-phi
psi=lambda tau,N: tau**(3*N)/(1-(-tau**2)**N)**3
for K in [1,2,3,5,8]:
    r=[None]+[(-t**2)**a for a in range(1,K+1)]
    node=[None]+[1/((-tau**2)**a) for a in range(1,K+1)]
    assert max(abs(r[a]-node[a]) for a in range(1,K+1))<mpf(10)**-150
    W=[None]+[1/mp.fprod([r[a]-r[b] for b in range(1,K+1) if b!=a]) for a in range(1,K+1)]
    E=lambda m: sum(r[a]**m*W[a] for a in range(1,K+1))
    # base values and bound
    for m in range(0,K): assert abs(E(m)-(1 if m==K-1 else 0))<mpf(10)**-100
    mx=max(abs(E(m)) for m in range(0,4*K+5)); assert mx<=phi**K
    F=[mpf(1)]
    for a in range(1,K+1): F=polymul(F,[-r[a],mpf(1)])
    alpha=lambda k: (-tau)*(-tau**2)**k
    nu=lambda k: k*(k+1)*alpha(k)/(1-alpha(k))
    S=lambda a: sum(psi(tau,N) for N in range(1,a+1))
    worst=0
    for k in range(0,2*K-1):
        q=polydiv([mpf(0)]*k+[mpf(1)],F) if k>=K else [mpf(0)]
        for j in range(len(q) if k>=1 else 0): assert abs(q[j]-E(k-1-j))<mpf(10)**-100
        res=[None]+[r[a]**k*W[a] for a in range(1,K+1)]
        mc=sum(q[j]*nu(j) for j in range(len(q)))+2*sum(res[a]*tau**a*S(a) for a in range(1,K+1))
        ml=-2*sum(res[a]*tau**a for a in range(1,K+1))
        T=mc-Xi*ml
        # Gamma form
        Gam=lambda x: 2*x*nsum(lambda M: t**(3*M)/(1-x*w**M)**3,[1,inf])
        T2=sum(q[j]*nu(j) for j in range(len(q)))+sum(res[a]*Gam(r[a]) for a in range(1,K+1))
        # double-series form
        T3=sum(q[j]*nu(j) for j in range(len(q)))+nsum(lambda M: 2*t**(3*M)*nsum(lambda j: binomial(j+2,2)*w**(M*j)*E(k+1+j),[0,inf]),[1,inf])
        assert abs(T-T2)<mpf(10)**-40 and abs(T-T3)<mpf(10)**-40, (K,k,T,T2,T3)
        worst=max(worst,abs(T))
    print(K, 'max|E|',mp.nstr(mx,6),'phi^K',mp.nstr(phi**K,6),'max|T_k|',mp.nstr(worst,8))
print('all checks OK')
