import numpy as np, math
from mpmath import mp, euler, zeta, pi, log, mpf, diff
# K0^(2) = lim_X [ sum_{prim mixed w, |w|<=X} alpha^2/|w|^2 - (J2/zeta2) log X ],  alpha/|w| = 1/max(p,q), both signs of w
def F_all(Y):
    # sum over p,q>=1, p^2+q^2<=Y^2 of 1/max(p,q)^2
    M=int(Y); tot=0.0
    m=np.arange(1,M+1,dtype=np.float64)
    full=2*m*m<=Y*Y
    cnt=np.where(full,2*m-1,0.0)
    # partial: max=m, other coordinate j<=min(m, floor(sqrt(Y^2-m^2)))
    part=~full
    jmax=np.floor(np.sqrt(np.maximum(Y*Y-m*m,0)))
    cntp=2*np.minimum(jmax,m-1)+ ((m*m+m*m)<=Y*Y)  # j<m counted twice (p<q and q<p), j=m once if fits
    cnt=np.where(full,cnt,cntp)
    return float(np.sum(cnt/(m*m)))
def mobius_sieve(n):
    mu=np.ones(n+1,dtype=np.int64); isp=np.ones(n+1,bool); isp[:2]=False
    for p in range(2,n+1):
        if isp[p]:
            isp[2*p::p]=False; mu[p::p]*=-1; mu[p*p::p*p]=0
    return mu
J2=4.0; z2=math.pi**2/6
for X in [1e3,1e4,1e5,1e6]:
    D=int(X); mu=mobius_sieve(D)
    s=0.0
    for d in range(1,D+1):
        if mu[d]: s+=mu[d]/d**2*F_all(X/d)
    K=2*s-(J2/z2)*math.log(X)
    print('X=%.0e  K0 estimate = %.8f'%(X,K),flush=True)
mp.dps=30
Delta2=4*(euler-mpf(1)/2-zeta(2)/2)+2*log(2)-4+pi
c2_exact=(12/pi**2)*(2*euler-mpf(1)/2-diff(zeta,2)/zeta(2))-2
print('Delta2 =',mp.nstr(Delta2,12),'  exact c2 =',mp.nstr(c2_exact,12))
print('framework predicts c2 = K0/2 + Delta2/(2 zeta2): with K0 from last X ->', float(K/2+Delta2/(2*zeta(2))))
