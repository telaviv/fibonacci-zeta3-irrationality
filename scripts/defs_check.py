from mpmath import mp, mpf, sqrt, matrix, det, fib, nsum, inf
mp.dps=80
def polydiv(num, den):  # coeff lists low->high, den monic
    num=num[:]; q=[mpf(0)]*max(1,len(num)-len(den)+1)
    for i in range(len(num)-len(den),-1,-1):
        c=num[i+len(den)-1]/den[-1]; q[i]=c
        for j in range(len(den)): num[i+j]-=c*den[j]
    return q
def polymul(a,b):
    r=[mpf(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]+=x*y
    return r
def generic(tau,K,X):
    w=-tau**2
    alpha=lambda k: (-tau)*w**k
    nu=lambda k: k*(k+1)*alpha(k)/(1-alpha(k))
    psi=lambda N: tau**(3*N)/(1-w**N)**3
    S=lambda a: sum(psi(N) for N in range(1,a+1))
    node=lambda a: 1/w**a
    F=[mpf(1)]
    for a in range(1,K+1): F=polymul(F,[-node(a),mpf(1)])
    def Fp(x):
        return sum(i*F[i]*x**(i-1) for i in range(1,len(F)))
    res=lambda k,a: node(a)**k/Fp(node(a))
    def Lpoly(f): return sum(f[j]*nu(j) for j in range(len(f)))
    def m(k):
        q=polydiv([mpf(0)]*k+[mpf(1)],F) if k>=K else [mpf(0)]
        mc=Lpoly(q)+2*sum(res(k,a)*tau**a*S(a) for a in range(1,K+1))
        ml=-2*sum(res(k,a)*tau**a for a in range(1,K+1))
        return mc+X*ml
    AK=K*(K+1)//2
    nrm=(-1)**K/(w**AK)
    M=matrix(K,K)
    for i in range(K):
        for j in range(K): M[i,j]=nrm*m(i+j)
    return det(M)
phi=(1+sqrt(5))/2; t=1/phi
Xi=nsum(lambda N: t**(3*N)/(1-(-t**2)**N)**3,[1,inf])
zF=nsum(lambda n: 1/fib(n)**3,[1,inf])
print('Xi vs zF/(5sqrt5)', Xi - zF/(5*sqrt(5)))
# direct Gram via real functional
def Lreal(h_dd, K):  # h given as function returning theta(theta+1)h at s
    return nsum(lambda n: (-t)**n*h_dd(( -t**2)**n),[1,inf])
from mpmath import diff
def gram(K):
    w=-t**2
    D=lambda s: mp.fprod([1-w**a*s for a in range(1,K+1)])
    M=matrix(K,K)
    for i in range(K):
        for j in range(K):
            f=lambda s,k=i+j: s**k/D(s)
            tt=lambda s: s**2*diff(f,s,2)+2*s*diff(f,s,1)
            M[i,j]=sum((-t)**n*tt(w**n) for n in range(1,120))
    return det(M)
for K in [2,3,4]:
    a=generic(t,K,Xi); b=gram(K); c=generic(-phi,K,-Xi)
    print(K, mp.nstr(a,15), mp.nstr(b,15), mp.nstr(c,15))
