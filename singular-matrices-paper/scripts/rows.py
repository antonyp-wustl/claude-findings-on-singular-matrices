"""Rows of the table in Appendix A. Run from the paper folder: python3 scripts/rows.py (writes rows.tex)."""
import math
def fmt(x): return "{:,}".format(x).replace(",", "\\,")
def sci(p):
    if p==1: return "$1$"
    e=math.floor(math.log10(p)); m=p/10**e
    if round(m,3)>=10: m/=10; e+=1
    return f"${m:.3f}\\times10^{{{e}}}$"
L=[]
for l in open('singular_3x3_counts.csv').read().split()[1:]:
    n,s,p,a,g=map(int,l.split(','))
    L.append(f"{n} & {fmt(s)} & {sci(s/n**9)} & {p/s:.3f} & {a/s:.3f} & {g/s:.3f} \\\\")
L[-1]=L[-1][:-2].rstrip()   # no row break after the last row (it would add an empty row)
open('rows.tex','w').write('\n'.join(L))
