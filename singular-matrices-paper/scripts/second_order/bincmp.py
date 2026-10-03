import subprocess, math, json, sys
z3=1.2020569031595942
def bins(f): return [(float(l.split()[2]),float(l.split()[3]),float(l.split()[4])) for l in open(f) if l.startswith('BIN')]
d64=bins('../../data/bin64.txt'); parts=[bins(f'../../data/bin80{c}.txt') for c in 'abc']
d80=[(parts[0][i][0],parts[0][i][1],sum(p[i][2] for p in parts)) for i in range(len(parts[0]))]
i0,i1=int(sys.argv[1]),int(sys.argv[2])
for i in range(i0,i1):
    lo,hi,v64=d64[i]; v80=d80[i][2]
    ns=int(min(2e7, 1.5e4/lo))
    hb=subprocess.run(['./deltabin',str(ns),str(lo),'9',str(200+i),str(hi)],capture_output=True,text=True).stdout.split('\n')[0]
    HB=float(hb.split('estimate')[1].split('+-')[0])/(2*z3); HBe=float(hb.split('+-')[1].split('(')[0])/(2*z3)
    ip=subprocess.run(['./intplane','1000000',str(lo),str(hi),str(int(min(4e6,4e3/lo))),str(300+i)],capture_output=True,text=True).stdout
    IB=float(ip.split('D_bin =')[1].split('+-')[0]); IBe=float(ip.split('D_bin =')[1].split('+-')[1].split('Delta')[0])
    rec=dict(i=i,lo=lo,hi=hi,d64=v64,d80=v80,haar=HB,haar_e=HBe,int6=IB,int6_e=IBe)
    open('../../data/bincompare.jsonl','a').write(json.dumps(rec)+'\n')
    print(f'[{lo:.2e},{hi:.2e}]  N=64 {v64:.4f}  N=80 {v80:.4f}  int N=1e6 {IB:.4f}+-{IBe:.4f}  Haar {HB:.4f}+-{HBe:.4f}',flush=True)
