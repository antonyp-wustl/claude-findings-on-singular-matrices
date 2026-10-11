"""Numerical evaluation of J_4 (and the J_3 check) for the paper, Section 4.5."""
import numpy as np, math, itertools, sys
LD=np.longdouble
def nodes(n):
    t,w=np.polynomial.legendre.leggauss(n); t=(t+1)/2; w=w/2
    t=t.astype(LD); w=w.astype(LD)
    if MAP=='tan':
        a=np.tan(np.pi*t/2); wa=w*(np.pi/2)/np.cos(np.pi*t/2)**2
    else:
        a=t/(1-t); wa=w/(1-t)**2
    return a,wa
def F(tv,coeffs):  # vol{ sum c_i x_i <= t, x in [0,1]^k }, inclusion-exclusion
    k=len(coeffs); prod=np.ones_like(coeffs[0])
    for c in coeffs: prod=prod*c
    s=np.zeros_like(prod)
    for r in range(k+1):
        for S in itertools.combinations(range(k),r):
            aS=sum((coeffs[i] for i in S), np.zeros_like(prod))
            s+= (-1)**r*np.maximum(tv-aS,0)**k
    return s/(math.factorial(k)*prod)
def J3(n):
    a,w=nodes(n); A,B=np.meshgrid(a,a,indexing='ij'); W=np.outer(w,w)
    al=F(LD(1),[A,B]); al=np.where(A+B<=1,LD(1),al)
    return 6*np.sum(W*al**3)
def J4(n):
    a,w=nodes(n); tot1=LD(0); tot2=LD(0)
    B,C=np.meshgrid(a,a,indexing='ij'); W2=np.outer(w,w)
    for i in range(n):
        A=np.full_like(B,a[i])
        al=F(LD(1),[A,B,C]); al=np.where(A+B+C<=1,LD(1),al)
        tot1+=w[i]*np.sum(W2*al**4)
        be=F(1+C,[A,B,C])-F(C,[A,B,C])
        tot2+=w[i]*np.sum(W2*be**4)
    return tot1,tot2
# Usage: python3 j4_numerics.py [--check3] [--tan] N1 N2 ...  (--tan: substitution a=tan(pi t/2) instead of a=t/(1-t))
#   (N = Gauss-Legendre nodes per axis)
args=sys.argv[1:]
MAP='rational'
if '--tan' in args:
    MAP='tan'; args.remove('--tan')
if args and args[0]=='--check3':
    args=args[1:]
    print('J3 check: exact', 45-15*math.pi**2/4)
    for n in [200,400,800]: print(' nodes=',n,float(J3(n)))
for n in [int(x) for x in args]:
    t1,t2=J4(n); J=8*t1+6*t2
    print(f'n={n}: int alpha^4={float(t1):.8f} int beta^4={float(t2):.8f} J4={float(J):.8f} C4=135*J4/pi^4={float(135*J/math.pi**4):.6f}',flush=True)
