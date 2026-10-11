import numpy as np, math
rng=np.random.default_rng(1)
def hull(P):
    P=sorted(map(tuple,P))
    def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    lo=[];up=[]
    for p in P:
        while len(lo)>=2 and cross(lo[-2],lo[-1],p)<=0: lo.pop()
        lo.append(p)
    for p in reversed(P):
        while len(up)>=2 and cross(up[-2],up[-1],p)<=0: up.pop()
        up.append(p)
    return np.array(lo[:-1]+up[:-1])
def reduce(b1,b2):
    while True:
        if b2@b2<b1@b1: b1,b2=b2,b1
        m=round((b1@b2)/(b1@b1))
        if m==0: return b1,b2
        b2=b2-m*b1
worst=0
for trial in range(3000):
    # random lattice: shortest vector length mu1 in [0.05,1], det ~ 1
    th=rng.uniform(0,np.pi); mu1=10**rng.uniform(-1.5,0)
    v1=mu1*np.array([math.cos(th),math.sin(th)])
    h=1/mu1  # det=1
    s=rng.uniform(-0.5,0.5)*mu1
    v2=s*np.array([math.cos(th),math.sin(th)])+h*np.array([-math.sin(th),math.cos(th)])
    b1,b2=reduce(v1,v2); mu1=math.sqrt(b1@b1); d=abs(b1[0]*b2[1]-b1[1]*b2[0])
    # random convex polygon of diameter up to ~20; sometimes thin / aligned with b1
    kind=trial%3
    if kind==0: P=rng.uniform(-1,1,(8,2))*rng.uniform(1,10)+rng.uniform(-5,5,2)
    elif kind==1:
        L=rng.uniform(1,20); w=rng.uniform(0,0.3)
        u=b1/mu1; n=np.array([-u[1],u[0]])
        # rectangle aligned with b1 passing through a lattice point
        P=np.array([0*u,L*u,L*u+w*n,w*n])
    else:
        P=rng.normal(size=(6,2))*np.array([rng.uniform(1,15),rng.uniform(0.01,2)])
    H=hull(P)
    if len(H)<3: continue
    area=0.5*abs(sum(H[i,0]*H[(i+1)%len(H),1]-H[(i+1)%len(H),0]*H[i,1] for i in range(len(H))))
    D=max(np.linalg.norm(a-b) for a in H for b in H)
    # count lattice points: coefficients range
    Binv=np.linalg.inv(np.array([b1,b2]).T)
    C=Binv@H.T
    lo=np.floor(C.min(axis=1))-1; hi=np.ceil(C.max(axis=1))+1
    ii,jj=np.meshgrid(np.arange(lo[0],hi[0]+1),np.arange(lo[1],hi[1]+1))
    pts=np.outer(ii.ravel(),b1)+np.outer(jj.ravel(),b2)
    inside=np.ones(len(pts),bool)
    for i in range(len(H)):
        a=H[i];b=H[(i+1)%len(H)]
        cr=(b[0]-a[0])*(pts[:,1]-a[1])-(b[1]-a[1])*(pts[:,0]-a[0])
        inside&= cr>=-1e-9
    cnt=inside.sum()
    err=abs(cnt-area/d)
    r=err/((2+2/math.sqrt(3))*D/mu1+1)
    worst=max(worst,r)
print("max |#-area/d| / ((2+2/sqrt3) D/mu1 + 1) =",round(worst,4))
