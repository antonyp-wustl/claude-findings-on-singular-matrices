import subprocess, sys, itertools
from mpmath import mp, mpf, log
mp.dps=100
def f_exact(th,mode):
    k=len(th); P=mpf(1)
    for t in th: P*=t
    norm=1/(mp.factorial(k)*P)
    subs=[(sum((th[i] for i in S),mpf(0)),(-1)**len(S)) for r in range(k+1) for S in itertools.combinations(range(k),r)]
    sh=th[-1] if mode==1 else mpf(0)
    F0=sum((sg*(sh-t)**k for t,sg in subs if t<=sh),mpf(0))*norm if mode==1 else 0
    kn=sorted(set([mpf(0)]+[t-sh for t,sg in subs if t-sh>0]))
    pw=k+1; tot=mpf(0)
    for j,lo in enumerate(kn):
        c=[mpf(0)]*(k+1)
        for t,sg in subs:
            if t-sh<=lo:
                d=sh-t
                for m in range(k+1): c[m]+=sg*mp.binomial(k,m)*d**(k-m)
        c=[x*norm for x in c]
        if mode==1: c[0]-=F0
        if j==0: c[0]=mpf(0) if mode==1 else c[0]
        if j==len(kn)-1:
            tot+=c[0]**pw*lo**(-k)/k; continue
        hi=kn[j+1]
        p=[mpf(1)]
        for _ in range(pw):
            q=[mpf(0)]*(len(p)+k)
            for a,x in enumerate(p):
                for b,y in enumerate(c): q[a+b]+=x*y
            p=q
        for m,cm in enumerate(p):
            e=m-pw
            if cm==0: continue
            if j==0 and m<pw: continue   # vanish identically
            tot+= cm*log(hi/lo) if e==-1 else cm*(hi**(e+1)-lo**(e+1))/(e+1)
    return tot
def split(v): h=float(v); return h, float(v-mpf(h))
K=int(sys.argv[1]); mode=int(sys.argv[2])
tests=[('0.2','0.3'),('0.1','0.6'),('1e-6','0.4'),('1e-10','1e-9'),('0.33','0.33'),('0.45','0.1'),('0.4999','0.0002'),('0.3','0.35'),('1e-15','0.5')]
worst=0
for a,b in tests:
    th=[mpf(a),mpf(b)]; th.append(1-th[0]-th[1])
    args=[]
    for t in th: args+=[repr(split(t)[0]),repr(split(t)[1])]
    out=subprocess.run(['./j4dd',str(K),str(mode),'eval']+args,capture_output=True,text=True).stdout.split()
    c=mpf(out[0])+mpf(out[1]); r=f_exact(th,mode)
    print([float(t) for t in th],' C-ref rel:',mp.nstr((c-r)/r,3))
