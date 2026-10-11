import sympy as sp, pickle, sys, time, mpmath as mp
a=sp.symbols('a',positive=True)
DPS=int(sys.argv[1]); mp.mp.dps=DPS
G=pickle.load(open('Gbeta.pkl','rb'))
tot=mp.mpf(0); t=time.time()
for key,(lo,hi,expr) in G.items():
    f=sp.lambdify(a,expr,modules='mpmath')
    lo_m=mp.mpf(sp.N(lo,DPS+10)); hi_m=mp.mpf(sp.N(hi,DPS+10))
    def g(x):
        d=min(abs(x-lo_m),abs(hi_m-x),abs(x),abs(x-mp.mpf(1)/2),abs(1-x))
        extra=int(8*max(0,-mp.log10(d)))+30 if d>0 else 30
        with mp.workdps(DPS+extra): v=f(mp.mpf(x))
        return v
    val=mp.quad(g,[lo_m,hi_m]); tot+=val
    print(key,mp.nstr(val,DPS-5),' %.1fs'%(time.time()-t),flush=True)
Ib=8*tot
print('I_beta =',mp.nstr(Ib,DPS-5))
print('earlier: 1.5591439930980165793435033...')
open(f'Ib{DPS}.txt','w').write(mp.nstr(Ib,DPS-5))
