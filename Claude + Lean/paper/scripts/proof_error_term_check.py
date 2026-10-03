# Sanity check of the proof's error terms:
#   S3 = N^3 A + T1 - T2,  T1 = sum_{adm P} L_P^3,  T2 = sum_{adm P} L_P * par_P
# The proof claims T2 = O(N^6) and T1 = C3 N^6 log N + O(N^6).
import numpy as np, itertools, math, json, sys
C3=15*(12-math.pi**2)/(4*1.2020569031595942)
S3={int(k):v for k,v in json.load(open('../data.json'))['S3'].items()}
def run(N):
    pts=np.array(list(itertools.product(range(1,N+1),repeat=3)),dtype=np.int64)
    M=len(pts)
    c=np.cross(pts[:,None,:],pts[None,:,:]).reshape(-1,3)
    nz=np.any(c!=0,1); c=c[nz]
    c//=np.gcd.reduce(np.abs(c),1)[:,None]
    c*=np.sign(c[np.arange(len(c)),np.argmax(c!=0,1)])[:,None]
    P,inv,I=np.unique(c,axis=0,return_inverse=True,return_counts=True)  # I_P = ordered indep pairs
    L=np.zeros(len(P),dtype=np.int64)
    for i in range(0,len(P),4000):
        L[i:i+4000]=(P[i:i+4000]@pts.T==0).sum(1)
    par=L**2-I
    T1=float((L.astype(float)**3).sum()); T2=float((L*par).astype(float).sum())
    return T1,T2
for N in [int(x) for x in sys.argv[1:]]:
    T1,T2=run(N)
    print(f'N={N}: T1/N^6={T1/N**6:.3f}  T1/N^6 - C3 log N={T1/N**6-C3*math.log(N):.3f}   T2/N^6={T2/N**6:.3f}',flush=True)
