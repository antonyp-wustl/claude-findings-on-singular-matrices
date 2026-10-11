import sys
from mpmath import mp, mpf, tanh, sinh, cosh, pi
mp.dps=40
m=int(sys.argv[1]); h=mpf(1)/2**m
X=[];W=[]
k=0
pts=[]
for sgn in [0]:
    pass
kk=-100000
out=[]
j=0
while True:
    t=j*h; u=pi/2*sinh(t); x=(1+tanh(u))/2; w=h*pi/2*cosh(t)/cosh(u)**2/2
    if w<mpf(10)**-34: break
    out.append((x,w))
    if j>0:
        out.append((1-x,w))   # symmetric node: (1 - tanh)/2
    j+=1
def split(v):
    hi=float(v); lo=float(v-mpf(hi)); return hi,lo
with open(sys.argv[2],'w') as f:
    f.write(f"{len(out)}\n")
    for x,w in out:
        xh,xl=split(x); wh,wl=split(w)
        f.write(f"{xh!r} {xl!r} {wh!r} {wl!r}\n")
print(len(out),'nodes')
