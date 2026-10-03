# Htilde(a,b) = int_0^1 beta(a,b,c)^4 dc for 0<a<=b<=1 ; I_beta = 4 * 2 * int_{a<=b in [0,1]^2} Htilde
import sympy as sp, pickle, time, mpmath as mp
a,b,c=sp.symbols('a b c',positive=True)
subsets=[((),0),(('a',),1),(('b',),1),(('a','b'),2)]
aS_sym={():sp.Integer(0),('a',):a,('b',):b,('a','b'):a+b}
def H_region(a0,b0):
    aS0={():0,('a',):a0,('b',):b0,('a','b'):a0+b0}
    bps=[]
    for S,_ in subsets:
        for v0,v in [(aS0[S]-1,aS_sym[S]-1),(aS0[S],aS_sym[S])]:
            if 0<v0<1: bps.append((v0,v))
    bps.sort(key=lambda t:t[0])
    pts=[(0.0,sp.Integer(0))]+bps+[(1.0,sp.Integer(1))]
    total=0
    for j in range(len(pts)-1):
        lo0,lo=pts[j]; hi0,hi=pts[j+1]; mid0=(lo0+hi0)/2
        num=0
        for S,k in subsets:
            sgn=(-1)**k; s0=aS0[S]; s=aS_sym[S]
            if 1+mid0-s0>0: num+=sgn*(1+c-s)**3
            if 1-s0>0:      num-=sgn*(1-s)**3
            if mid0-s0>0:   num-=sgn*(c-s)**3
        poly=sp.Poly(sp.expand(num**4),c)
        for (k,),co in poly.terms():
            e=k-4
            if j==0:    assert e>=0; F=co*hi**(e+1)/(e+1)
            elif e==-1: F=co*sp.log(hi/lo)
            else:       F=co*(hi**(e+1)-lo**(e+1))/(e+1)
            total+=F
    return total/(6*a*b)**4
out={'R1':H_region(0.2,0.3),'R2':H_region(0.4,0.8)}
pickle.dump(out,open('Hbeta01.pkl','wb'))
# quick numeric check of I_beta = 8 * (int_R1 + int_R2), low precision 2D
mp.mp.dps=20
fR1=sp.lambdify((a,b),out['R1'],'mpmath'); fR2=sp.lambdify((a,b),out['R2'],'mpmath')
I1=mp.quad(lambda x: mp.quad(lambda y: fR1(x,y),[x,1-x]),[0,0.5])
I2=mp.quad(lambda x: mp.quad(lambda y: fR2(x,y),[max(x,1-x),1]),[0,0.5,1])
print('8*(I1+I2) =',mp.nstr(8*(I1+I2),18),'   I_beta (earlier) = 1.5591439930980165793')
