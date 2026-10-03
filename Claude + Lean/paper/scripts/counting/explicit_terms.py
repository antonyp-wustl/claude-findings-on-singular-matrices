"""Exact parallel-pair term N^3 A(N) and axis-plane term of Theorem 3.5 for N <= Nmax.
Usage: python3 explicit_terms.py Nmax > explicit_terms.csv   (columns N,parallel,axis)"""
import sys
from math import gcd
from sympy import totient, mobius, divisors
Nmax=int(sys.argv[1]) if len(sys.argv)>1 else 100
phi=[0]+[int(totient(m)) for m in range(1,Nmax+1)]
g3=[0]+[int(sum(int(mobius(d))*((m//d)**3-(m//d-1)**3) for d in divisors(m))) for m in range(1,Nmax+1)]
h=[0,1]+[2*phi[m] for m in range(2,Nmax+1)]
def D(q,N):
    tot=0
    for u in range(1,q+1):
        for v in range(1,N+1):
            if gcd(u,v)==1: tot+=min(q//u,N//v)**2
    return tot
print('N,parallel,axis')
for N in range(1,Nmax+1):
    A=sum(g3[m]*(N//m)**2 for m in range(1,N+1))
    ax=3*sum(h[m]*(N//m)*N*(((N//m)*N)**2-D(N//m,N)) for m in range(1,N+1))
    print(f'{N},{N**3*A},{ax}',flush=True)
