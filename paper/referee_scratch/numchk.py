from exact import build, F, tau, X, s
from sympy import lambdify, sqrt as ssqrt, together, fraction
import mpmath as m
m.mp.dps=60
phi=(1+m.sqrt(5))/2; t=1/phi
Xi=m.nsum(lambda N: t**(3*N)/(1-(-t*t)**N)**3,[1,m.inf])
print("zetaF3 check", Xi*5*m.sqrt(5), m.nsum(lambda n: 1/m.fib(n)**3,[1,m.inf]))
def Lfun(h):
    w=-t*t; rho=-t
    return m.nsum(lambda n: rho**n*( (lambda x: x*x*m.diff(h,x,2)+2*x*m.diff(h,x))(w**n)),[1,m.inf])
C0=m.nprod(lambda i:1/(1-t**(2*i)),[1,m.inf])
for K in range(2,6):
    d=F.to_sympy(build(K))
    f=lambdify((tau,X),d,'mpmath')
    real=f(t,Xi); conj=f(-phi,-Xi)
    if K<=3:
        DK=lambda x: m.fprod([1-(-t*t)**a*x for a in range(1,K+1)])
        Mx=m.matrix(K,K)
        for i in range(K):
            for j in range(K):
                Mx[i,j]=Lfun(lambda x,k=i+j: x**k/DK(x))
        print(" direct det",m.det(Mx))
    BK=C0*(K**2/((1-t**3)*(1-t**2))+4)
    print(K,"log|D|/logphi",m.log(abs(real))/m.log(phi),"pred -2/9(K^3+3K^2-c)",-2*(K**3+3*K**2)/9,
          "| log|sD|/logphi",m.log(abs(conj))/m.log(phi),"bound",(-K*K*(K+1)*m.log(phi)+K*m.log(m.sqrt(K)*BK))/m.log(phi), "real",real)
