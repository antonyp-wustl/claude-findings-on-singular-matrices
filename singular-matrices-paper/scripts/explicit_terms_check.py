"""Checks Proposition 3.7: A(N)/N^3 -> kappa, axis-plane term/N^6 -> 3*kappa, kappa = 2 zeta(2)/zeta(3) - 1."""
import numpy as np, math
z2=math.pi**2/6; z3=1.2020569031595942
K=2*z2/z3-1
print('2zeta(2)/zeta(3)-1 =',K,'  3/zeta(2)=18/pi^2=',3/z2,'  3/zeta(3)=',3/z3)
M=100000
mu=np.ones(M+1,dtype=np.int64); isp=np.ones(M+1,bool); isp[:2]=False
for p in range(2,M+1):
    if isp[p]:
        isp[2*p::p]=False; mu[p::p]*=-1; mu[p*p::p*p]=0
f=np.arange(M+1,dtype=np.float64); f=f**3-(f-1)**3; f[0]=0
g=np.zeros(M+1)
for d in range(1,M+1):
    if mu[d]!=0: g[d::d]+=mu[d]*f[1:M//d+1]
phi=np.arange(M+1,dtype=np.int64)
for p in range(2,M+1):
    if isp[p]: phi[p::p]-=phi[p::p]//p
h=2*phi.astype(float); h[1]=1
print('avg g(m)/m^2 over m<=M:', (g[1:]/np.arange(1,M+1)**2).mean())
for N in [34,1000,10000,100000]:
    m=np.arange(1,N+1); q=(N//m).astype(float)
    A=np.sum(g[1:N+1]*q**2); ax_main=3*np.sum(h[1:N+1]*q**3)
    print(f'N={N}: A(N)/N^3={A/N**3:.5f}   3*sum h(m)q^3/N^3={ax_main/N**3:.5f}  (Gemini axis formula 3 sum h q^2 /N^3 = {3*np.sum(h[1:N+1]*q**2)/N**3:.4f})')
# full axis term incl. D correction, moderate N
from math import gcd
def D(qq,N):
    u=np.arange(1,qq+1)[:,None]; v=np.arange(1,N+1)[None,:]
    cop=np.gcd(u,v)==1
    return int((np.minimum(qq//u,N//v)**2*cop).sum())
for N in [34,200,600]:
    tot=0
    for mm in range(1,N+1):
        qq=N//mm; tot+=3*h[mm]*qq*N*((qq*N)**2-D(qq,N))
    print(f'N={N}: full axis/N^6={tot/N**6:.4f}  (limit {3*K:.4f})')
