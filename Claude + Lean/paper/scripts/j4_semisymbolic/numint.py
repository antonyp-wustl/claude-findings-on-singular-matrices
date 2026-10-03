import sympy as sp, pickle, sys, time, mpmath as mp
a=sp.symbols('a',positive=True)
DPS=int(sys.argv[1]) if len(sys.argv)>1 else 40
mp.mp.dps=DPS
tot=mp.mpf(0); t=time.time()
res={}
for name in ['i','ii','iii','iv']:
    G=pickle.load(open(f'G_{name}.pkl','rb'))
    for key,(lo,hi,expr) in G.items():
        f=sp.lambdify(a,expr,modules='mpmath')
        lo_m=mp.mpf(sp.N(lo,DPS+10)); hi_m=mp.inf if hi==sp.oo else mp.mpf(sp.N(hi,DPS+10))
        def g(x):
            d=min(abs(x-lo_m), abs(hi_m-x) if hi_m!=mp.inf else 1, abs(x), abs(x-0.5), abs(1-x))
            extra=int(8*max(0,-mp.log10(d)))+30 if d>0 else 30
            with mp.workdps(DPS+extra):
                v=f(mp.mpf(x))
            return v
        val=mp.quad(g,[lo_m,hi_m])
        res[(name,key)]=val; tot+=val
        print(name,key,mp.nstr(val,DPS-5),' %.1fs'%(time.time()-t),flush=True)
I=2*tot
print('I_alpha =',mp.nstr(I,DPS-5))
print('previous: 0.61323405860879703879406178...')
pickle.dump({k:str(v) for k,v in res.items()},open(f'Ialpha_dps{DPS}.pkl','wb'))
