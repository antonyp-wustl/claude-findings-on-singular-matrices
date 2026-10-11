# Symbolic inner integral H(a,b) = int_0^inf alpha_3(a,b,c)^4 dc for I_alpha, per (a,b)-region (a<=b).
import sympy as sp, time, pickle
a,b,c=sp.symbols('a b c',positive=True)
A={'0':sp.Integer(1),'1':1-a,'2':1-b,'12':1-a-b}
sg={'0':1,'1':-1,'2':-1,'12':1}
def H_region(active, order):
    # active: list of keys with A>0 ; order: increasing list of breakpoints (keys) in c (all active ones)
    P0=sum(sg[k]*A[k]**3 for k in active)
    pts=[sp.Integer(0)]+[A[k] for k in order]
    total=0
    for j in range(len(pts)):
        lo=pts[j]; hi=pts[j+1] if j+1<len(pts) else sp.oo
        live=[k for k in active if True]  # terms (A_k - c)_+^3 alive on (lo,hi) iff A_k >= hi
        live=[k for k in order if order.index(k)>=j]  # breakpoints >= hi are alive
        Q=sum(sg[k]*(A[k]-c)**3 for k in live)
        num=sp.expand(P0-Q)
        poly=sp.Poly(sp.expand(num**4),c)
        for (k,),co in poly.terms():
            e=k-4
            if hi==sp.oo:
                assert e<-1; F=-co*lo**(e+1)/(e+1)
            elif j==0:
                assert e>=0; F=co*hi**(e+1)/(e+1)
            elif e==-1: F=co*sp.log(hi/lo)
            else: F=co*(hi**(e+1)-lo**(e+1))/(e+1)
            total+=F
    return total/(6*a*b)**4
t=time.time()
regions={
 'i' : (['0','1','2','12'], ['12','2','1','0']),   # a<=b, a+b<=1
 'ii': (['0','1','2'],      ['2','1','0']),        # a<=b<=1<=a+b
 'iii':(['0','1'],          ['1','0']),            # a<=1<=b
 'iv': (['0'],              ['0']),                # 1<=a<=b
}
out={}
for name,(act,ordr) in regions.items():
    H=H_region(act,ordr)
    out[name]=H
    print(name,'ops:',sp.count_ops(H),' time %.1fs'%(time.time()-t),flush=True)
pickle.dump(out,open('Halpha.pkl','wb'))
# numeric sanity check at a point against direct numeric integration
import mpmath as mp
mp.mp.dps=30
def alpha_num(av,bv,cv):
    f=lambda z: max(z,0)**3
    s=1-f(1-av)-f(1-bv)-f(1-cv)+f(1-av-bv)+f(1-av-cv)+f(1-bv-cv)-f(1-av-bv-cv)
    return s/(6*av*bv*cv)
for name,pt in [('i',(0.2,0.3)),('ii',(0.4,0.8)),('iii',(0.5,2.0)),('iv',(1.5,2.5))]:
    av,bv=[mp.mpf(x) for x in pt]
    val=out[name].subs({a:av,b:bv})
    num=mp.quad(lambda cv: mp.mpf(alpha_num(av,bv,cv))**4,[0,1-av-bv if av+bv<1 else 0.5,1-bv if bv<1 else 0.7,1-av if av<1 else 0.9,1,mp.inf])
    print(name, sp.N(val,20), mp.nstr(num,20))
