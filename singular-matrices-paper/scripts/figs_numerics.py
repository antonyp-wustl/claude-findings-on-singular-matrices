"""Figures 1, 3, 6, 7, 8 (prob_singular, shares, asymptotic_fit, c3_parts, bins). Run from the paper folder: python3 scripts/figs_numerics.py"""
import json, math, numpy as np
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from sympy import isprime
plt.rcParams.update({'font.family':'serif','mathtext.fontset':'cm','font.size':10,
  'axes.spines.top':False,'axes.spines.right':False,'savefig.bbox':'tight'})
B1,B2,B3,GR='#1f4e79','#c0504d','#e6a532','#7f7f7f'
OUT='fig/'
z3=1.2020569031595942; z2=math.pi**2/6
C3=15*(12-math.pi**2)/(4*z3); C2=12/math.pi**2; kappa=2*z2/z3-1
c3_pred=-2.73807; cgen_pred=-9.68553
c2_exact=-0.5113174472
S={};E={}
for l in open('singular_3x3_counts.csv').read().split()[1:]:
    n,s3,p,x,g=map(int,l.split(',')); S[n]=s3; E[n]=(p,x)
S2={int(k):v for k,v in json.load(open('data/S2_logspaced.json')).items()}
# ---------- Fig 1: singular probability
fig,ax=plt.subplots(figsize=(6,3.6))
N2=np.array(sorted(S2)); p2=np.array([S2[n]/float(n)**4 for n in sorted(S2)])   # float: n**4 overflows int64 for n > 55108
N3=np.array([n for n in sorted(S) if n>=2]); p3=np.array([S[n]/float(n)**9 for n in sorted(S) if n>=2])
ax.loglog(N2,p2,'o',ms=2.2,color=B1,label=r'$2\times2$ exact')
ax.loglog(N3,p3,'s',ms=2.8,color=B2,label=r'$3\times3$ exact')
x=np.logspace(math.log10(3),6,200); ax.loglog(x,C2*np.log(x)/x**2,'-',color=B1,lw=1,alpha=.7,label=r'$\frac{12}{\pi^2}\,\log N/N^{2}$')
x3=np.logspace(math.log10(3),math.log10(150),200); ax.loglog(x3,C3*np.log(x3)/x3**3,'-',color=B2,lw=1,alpha=.7,label=r'$C_3\,\log N/N^{3}$')
ax.set_xlabel(r'$N$ (entries uniform on $\{1,\dots,N\}$)'); ax.set_ylabel(r'$\Pr[\det M=0]$')
ax.legend(frameon=False,fontsize=8.5); ax.grid(alpha=.25,which='both',lw=.4)
fig.savefig(OUT+'prob_singular.pdf')
# ---------- Fig 3: shares up to 100
ns=np.arange(2,101); P=np.array([[E[n][0],E[n][1],S[n]-E[n][0]-E[n][1]] for n in ns],float); P=P/P.sum(1,keepdims=True)
fig,ax=plt.subplots(figsize=(6.2,2.8))
ax.bar(ns,P[:,0],color=B3,label='parallel pair ($N^3A(N)$)',width=1.0,linewidth=0)
ax.bar(ns,P[:,1],bottom=P[:,0],color=B1,label=r'axis planes $ax=by$',width=1.0,linewidth=0)
ax.bar(ns,P[:,2],bottom=P[:,0]+P[:,1],color=B2,label=r'generic planes $ax+by=cz$',width=1.0,linewidth=0)
ax.set_xlabel(r'$N$'); ax.set_ylabel('share of singular matrices'); ax.set_ylim(0,1); ax.set_xlim(1.3,100.7)
ax.legend(frameon=False,fontsize=8,loc='upper center',bbox_to_anchor=(.5,1.17),ncol=3)
fig.savefig(OUT+'shares.pdf')
# ---------- Fig 6: asymptotic fit (3 panels)
fig,axs=plt.subplots(1,3,figsize=(7.4,2.6))
n3=np.array([n for n in sorted(S) if n>=4]); y3=np.array([S[n]/float(n)**6 for n in sorted(S) if n>=4]); res3=y3-C3*np.log(n3)
ax=axs[0]; ax.plot(np.log(n3),y3,'s',ms=2.2,color=B2,label='exact counts')
xx=np.linspace(np.log(4),np.log(110),50); ax.plot(xx,C3*xx+c3_pred,'-',color='k',lw=.9,label=r'$C_3\log N+c_3$')
ax.set_xlabel(r'$\log N$'); ax.set_ylabel(r'$S_3(N)/N^6$'); ax.legend(frameon=False,fontsize=7.5,loc='upper left')
ax.set_title(r'(a) $3\times3$ counts',fontsize=9.5)
ax=axs[1]; pm=np.array([isprime(int(n)) for n in n3])
ax.plot(n3,res3,'-',lw=.4,color=B2)
ax.plot(n3[~pm],res3[~pm],'s',ms=2.2,color=B2,label='composite $N$'); ax.plot(n3[pm],res3[pm],'v',ms=3,color='k',label='prime $N$')
ax.axhline(c3_pred,color='k',lw=.8,ls='--'); ax.text(60,c3_pred+0.07,r'predicted limit $c_3$',fontsize=7.5)
ax.set_ylim(-4.6,-2.5); ax.set_xlabel(r'$N$'); ax.set_ylabel(r'$S_3/N^6-C_3\log N$'); ax.legend(frameon=False,fontsize=7,loc='lower right')
ax.set_title(r'(b) $3\times3$ residual',fontsize=9.5)
ax=axs[2]; n2=np.array([n for n in sorted(S2) if n>=4]); r2=np.array([S2[n]/float(n)**2 for n in sorted(S2) if n>=4])-C2*np.log(n2)
ax.semilogx(n2,r2,'o',ms=1.6,color=B1); ax.axhline(c2_exact,color='k',lw=.8,ls='--'); ax.axvspan(4,100,color=B2,alpha=.08)
ax.text(2e2,c2_exact+0.05,r'exact $c_2$',fontsize=7.5)
ax.set_xlabel(r'$N$'); ax.set_ylabel(r'$S_2/N^2-\frac{12}{\pi^2}\log N$'); ax.set_title(r'(c) $2\times2$ residual',fontsize=9.5)
fig.tight_layout(); fig.savefig(OUT+'asymptotic_fit.pdf')
# ---------- New: explicit and generic parts
fig,axs=plt.subplots(1,2,figsize=(6.8,2.6))
nn=np.arange(10,101)
ex=np.array([sum(E[n])/n**6 for n in nn]); ge=np.array([(S[n]-sum(E[n]))/n**6-C3*math.log(n) for n in nn])
ax=axs[0]; ax.plot(nn,ex,'o',ms=2.2,color=B1); ax.axhline(4*kappa,color='k',ls='--',lw=.8); ax.text(55,4*kappa-0.12,r'$4\kappa=6.9475$',fontsize=8)
ax.set_xlabel(r'$N$'); ax.set_ylabel(r'(parallel + axis)$/N^6$'); ax.set_title('(a) explicit terms (exact limit)',fontsize=9.5)
ax=axs[1]; ax.plot(nn,ge,'o',ms=2.2,color=B2); ax.axhline(cgen_pred,color='k',ls='--',lw=.8); ax.text(55,cgen_pred+0.06,r'predicted $-9.6855$',fontsize=8)
ax.set_xlabel(r'$N$'); ax.set_ylabel(r'generic$/N^6-C_3\log N$'); ax.set_title('(b) generic planes (predicted limit)',fontsize=9.5)
fig.tight_layout(); fig.savefig(OUT+'c3_parts.pdf')
# ---------- New: bin comparison
recs=sorted([json.loads(l) for l in open('data/bincompare.jsonl')],key=lambda r:r['lo'])
lam=np.array([math.sqrt(r['lo']*r['hi']) for r in recs])
fig,ax=plt.subplots(figsize=(6,3.0))
ax.semilogx(lam,[r['d64'] for r in recs],'s',ms=3.5,color=B3,label=r'exact, $N=64$')
ax.semilogx(lam,[r['d80'] for r in recs],'D',ms=3.2,color=B1,label=r'exact, $N=80$')
ax.errorbar(lam,[r['int6'] for r in recs],yerr=[2*r['int6_e'] for r in recs],fmt='o',ms=3,color=B2,label=r'random integer planes, $N=10^6$')
ax.semilogx(lam,[r['haar'] for r in recs],'-',color='k',lw=1,label='Haar-random lattices ($N\\to\\infty$)')
ax.set_xlabel(r'$\lambda=|w|/N^2$ (bin centre)'); ax.set_ylabel(r'$\sum_{P\ \mathrm{in\ bin}} L_PI_P\,/\,N^6$')
ax.legend(frameon=False,fontsize=7.8,loc='lower left'); ax.set_ylim(0,1.95)
fig.savefig(OUT+'bins.pdf')
print('figures written')
