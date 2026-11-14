import sys
from sympy import symbols, QQ, Poly, cyclotomic_poly, factor_list, together, fraction, div, prod, Rational
from sympy.polys.matrices import DomainMatrix
from bsum import b, e_of
tau,X,s=symbols('tau X s')
F=QQ.frac_field(tau,X)
def build(K):
    w=-tau**2; rho=-tau
    alpha=lambda k: rho*w**k
    nu=lambda k: k*(k+1)*alpha(k)/(1-alpha(k))
    psi=lambda N: tau**(3*N)/(1-w**N)**3
    S=lambda a: sum(psi(N) for N in range(1,a+1))
    lam=lambda a: 2*rho**(-a)
    D=Poly(prod(1-w**a*s for a in range(1,K+1)),s,domain=QQ.frac_field(tau))
    xs={a:w**(-a) for a in range(1,K+1)}
    def entry(k):
        P=Poly(s**k,s,domain=QQ.frac_field(tau))
        q,r=div(P,D)
        val=sum(q.as_expr().coeff(s,j)*nu(j) for j in range(0,q.degree()+1)) if not q.is_zero else 0
        if k>=0:
            for a in range(1,K+1):
                den=prod(1-w**(bb-a) for bb in range(1,K+1) if bb!=a)
                A=xs[a]**k/den
                val+=A*lam(a)*(X-S(a))
        return F.from_sympy(together(val))
    M=DomainMatrix([[entry(i+j) for j in range(K)] for i in range(K)],(K,K),F)
    return M.det()
for K in (range(2,int(sys.argv[1])+1) if __name__=="__main__" else []):
    d=F.to_sympy(build(K))
    num,den=fraction(together(d))
    denp=Poly(den,tau)
    # multiplicities of cyclotomic factors in denominator after cancellation, against bound
    cf,facs=factor_list(denp)
    bad=[]; info=[]
    for f,mult in facs:
        fp=Poly(f,tau)
        if fp.degree()==1 and fp.as_expr()==tau: continue
        found=None
        for dd in range(1,4*K+1):
            if Poly(cyclotomic_poly(dd,tau),tau)==fp or Poly(-cyclotomic_poly(dd,tau),tau)==fp: found=dd;break
        if found is None: bad.append((f,mult)); continue
        bd=b(K,found); info.append((found,mult,bd))
        if mult>bd: bad.append((found,mult,bd))
    print(K,"factors(d,mult,bound):",sorted(info),"VIOLATIONS:",bad,flush=True)
