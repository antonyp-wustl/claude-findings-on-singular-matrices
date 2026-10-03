"""Figures 2, 4, 5 (rays2d, cube_section, integrand). Run from the paper folder: python3 scripts/figs_geometry.py"""
import math, numpy as np
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from math import gcd
plt.rcParams.update({'font.family':'serif','mathtext.fontset':'cm','font.size':10,
  'axes.spines.top':False,'axes.spines.right':False,'savefig.bbox':'tight'})
B1,B2,B3,GR='#1f4e79','#c0504d','#e6a532','#7f7f7f'

# Fig 2: 2x2 rays
N=9
fig,ax=plt.subplots(figsize=(3.4,3.4))
pts=[(x,y) for x in range(1,N+1) for y in range(1,N+1)]
for (p,q) in [(p,q) for p in range(1,N+1) for q in range(1,N+1) if gcd(p,q)==1]:
    k=N//max(p,q)
    if k>=3: ax.plot([0,k*p],[0,k*q],color=B1,lw=.8,alpha=.55)
    elif k==2: ax.plot([0,k*p],[0,k*q],color=B1,lw=.5,alpha=.25)
ax.scatter(*zip(*pts),s=9,color='k',zorder=3)
for (p,q) in [(1,1),(1,2),(2,3)]:
    k=N//max(p,q); ax.scatter([j*p for j in range(1,k+1)],[j*q for j in range(1,k+1)],s=22,color=B2,zorder=4)
ax.set_xlim(0,N+.5); ax.set_ylim(0,N+.5); ax.set_aspect('equal')
ax.set_xticks(range(0,N+1,3)); ax.set_yticks(range(0,N+1,3))
ax.set_xlabel('first coordinate'); ax.set_ylabel('second coordinate')
fig.savefig('fig/rays2d.pdf')

# Fig 3: cube section by plane through corner
def section(w):
    # vertices of {x in [0,1]^3 : w.x = 0}
    import itertools
    V=[]
    for i in range(3):
        for c in itertools.product([0,1],repeat=2):
            # edge varying coordinate i
            j,k=[t for t in range(3) if t!=i]
            if abs(w[i])<1e-12: continue
            t=-(w[j]*c[0]+w[k]*c[1])/w[i]
            if -1e-12<=t<=1+1e-12:
                p=[0,0,0]; p[i]=t; p[j]=c[0]; p[k]=c[1]; V.append(tuple(np.round(p,10)))
    V=np.array(sorted(set(V)))
    cen=V.mean(0); n=np.array(w)/np.linalg.norm(w)
    u=np.cross(n,[1,0,0] if abs(n[0])<.9 else [0,1,0]); u/=np.linalg.norm(u); v=np.cross(n,u)
    ang=np.arctan2((V-cen)@v,(V-cen)@u); return V[np.argsort(ang)]
fig=plt.figure(figsize=(6.4,3.2))
for idx,(w,title) in enumerate([((1.0,1.0,-1.0),r'$w=(1,\,1,\,-1)$'),((0.5,0.4,-1.0),r'$w=(0.5,\,0.4,\,-1)$')]):
    ax=fig.add_subplot(1,2,idx+1,projection='3d')
    import itertools
    for a,b in itertools.combinations(itertools.product([0,1],repeat=3),2):
        if sum(x!=y for x,y in zip(a,b))==1: ax.plot(*zip(a,b),color=GR,lw=.7)
    P=section(w); ax.add_collection3d(Poly3DCollection([P],facecolor=B1,alpha=.45,edgecolor=B1))
    ax.scatter([0],[0],[0],color=B2,s=15)
    ax.set_box_aspect((1,1,1)); ax.view_init(22,-58); ax.set_axis_off(); ax.set_title(title,fontsize=9,y=0.93)
fig.subplots_adjust(wspace=0)
fig.savefig('fig/cube_section.pdf')

# Fig 4: integrand area(a,b)^3
def area(a,b):
    X=min(1,1/a); x0=min(max((1-b)/a,0),X); F=lambda x:(x-a*x*x/2)/b
    return x0+F(X)-F(x0)
g=np.linspace(0.005,3,400); Z=np.array([[area(a,b)**3 for a in g] for b in g])
fig,ax=plt.subplots(figsize=(3.9,3.3))
im=ax.imshow(Z,origin='lower',extent=[0,3,0,3],cmap='Blues',vmin=0,vmax=1)
ax.plot([0,1],[1,0],'k-',lw=.8); ax.plot([1,1],[0,3],'k--',lw=.6); ax.plot([0,3],[1,1],'k--',lw=.6)
for (x,y,t) in [(.3,.3,'I'),(.68,.68,'II'),(2,.45,'III'),(.45,2,"III$'$"),(2,2,'IV')]:
    ax.text(x,y,t,ha='center',va='center',fontsize=10,color='k' if t not in('I',) else 'w')
ax.set_xlabel(r'$a$'); ax.set_ylabel(r'$b$'); plt.colorbar(im,ax=ax,fraction=.046,label=r'$\alpha(a,b)^3$')
fig.savefig('fig/integrand.pdf')
