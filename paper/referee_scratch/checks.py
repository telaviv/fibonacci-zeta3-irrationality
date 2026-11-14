from mpmath import mp, mpf, sqrt, log, nprod, nsum, inf, pi
from fractions import Fraction as Fr
from sympy import totient
mp.dps=30
phi=(1+sqrt(5))/2; t=1/phi
E1=nsum(lambda a: -log(1-t**a),[1,inf]); print("E1",E1,"2E1",2*E1)
C0=nprod(lambda i: 1/(1-t**(2*i)),[1,inf]); print("C0",C0)
mu7=Fr(3,4)*Fr(8,9)*Fr(24,25)*Fr(48,49); print("mu7",mu7,float(mu7))
cs=Fr(11,8)*mu7+Fr(1,3); print("c*",cs,float(cs), float(cs-Fr(11,9)), float(Fr(11,8)*mu7-Fr(8,9)))
def aj(j): return sum((u+2)//3 for u in range(1,j+1))
for K in range(1,13):
    s=2*sum(aj(j) for j in range(K)); c={0:0,1:4,2:2}[K%3]
    assert 9*s==K**3+3*K**2-c,(K,s)
print("2sum a_j formula ok")
# c(m), c'(m)
def c0(m): return sum(max(0,m+2-2*j) for j in range(0,m-1))
def c(m):
    if m<6: return c0(m)
    return (m+2)*(m+4)//4 if m%2==0 else (m+3)**2//4
def cp(m): return sum(max(0,m+2-2*j) for j in range(0,m))
print([c(m) for m in range(1,10)],[cp(m) for m in range(1,10)])
for m in range(1,200):
    assert c(m)<=(m+3)**2/4 and 0<=cp(m)-c(m)<=3
    d=c(m)-4*(m-1); assert 0<=d<=max(0,m-5)**2/4,(m,d)
print("c bounds ok")
# I = int_0^1 g(x) x dx, g piecewise linear through (1/m, c(m)/m), g(0)=? limit c(m)/m ~ m/4 -> inf at 0 ; x*g ~ 1/4
# integrate exactly piecewise between 1/(m+1) and 1/m
I=mpf(0)
for m in range(1,20000):
    x1,x2=mpf(1)/(m+1),mpf(1)/m; g1,g2=mpf(c(m+1))/(m+1),mpf(c(m))/m
    # linear g on [x1,x2]; integral of g(x)x
    a=(g2-g1)/(x2-x1); b=g1-a*x1
    I+= a*(x2**3-x1**3)/3 + b*(x2**2-x1**2)/2
I+=mpf(1)/(4*20000); print("I approx",I)
print("sharp const",(12*I+mpf(80)/27)/pi**2)
