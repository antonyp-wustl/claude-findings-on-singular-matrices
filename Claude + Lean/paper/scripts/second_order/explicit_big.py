import numpy as np, math, sys
def sieves(M):
    phi=np.arange(M+1,dtype=np.int64)
    for p in range(2,M+1):
        if phi[p]==p: phi[p::p]-=phi[p::p]//p
    mu=np.ones(M+1,dtype=np.int64); isp=np.ones(M+1,bool); isp[:2]=False
    for p in range(2,M+1):
        if isp[p]:
            isp[2*p::p]=False; mu[p::p]*=-1; mu[p*p::p*p]=0
    return phi,mu
def explicit(N,phi,mu):
    m=np.arange(1,N+1,dtype=np.int64)
    # g(m)=sum_{d|m} mu(d)((m/d)^3-(m/d-1)^3): Dirichlet convolution mu * f, f(k)=3k^2-3k+1
    f=3*m*m-3*m+1; g=np.zeros(N+1,dtype=object)
    gg=np.zeros(N+1,dtype=np.float64)
    for d in range(1,N+1):
        if mu[d]: gg[d::d]+=mu[d]*f[:N//d].astype(np.float64)
    q=(N//m).astype(np.float64)
    A=float(np.sum(gg[1:]*q*q))
    h=2*phi[1:N+1].astype(np.float64); h[0]=1
    cvec=2*phi[1:N+1].astype(np.float64); cvec[0]-=1          # c(m)=2phi(m)-[m=1]
    axis=0.0
    # group m by q=floor(N/m)
    mm=1
    while mm<=N:
        qq=N//mm; m2=N//qq
        hs=float(np.sum(h[mm-1:m2]))
        # D(qq,N)=sum_{t<=qq} c(t) floor(qq/t) floor(N/t)
        t=np.arange(1,qq+1)
        D=float(np.sum(cvec[:qq]*(qq//t)*(N//t)))
        axis+=3*hs*qq*N*((qq*N)**2-D)
        mm=m2+1
    return N**3*A, axis
M=int(sys.argv[1]); phi,mu=sieves(M)
kappa=2*(math.pi**2/6)/1.2020569031595942-1
for N in [int(x) for x in sys.argv[2:]]:
    par,ax=explicit(N,phi,mu)
    print(f'N={N}: parallel/N^6={par/N**6:.6f}  axis/N^6={ax/N**6:.6f}  explicit/N^6={(par+ax)/N**6:.6f}  (4kappa={4*kappa:.6f})',flush=True)
