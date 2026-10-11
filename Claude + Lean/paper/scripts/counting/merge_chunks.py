"""Sum the chunk outputs of s3all (or s3bin) and join with the explicit terms.
Usage: python3 merge_chunks.py explicit_terms.csv chunk1.txt chunk2.txt ... > singular_3x3_counts.csv
Each chunk file starts with a line 'i0 i1 nlines' (the range of canonical lines it processed)."""
import sys
E={}
for l in open(sys.argv[1]).read().split()[1:]:
    n,p,a=map(int,l.split(',')); E[n]=(p,a)
S={}; ranges=[]; NL=None
for f in sys.argv[2:]:
    L=open(f).read().split('\n')
    i0,i1,nl=map(int,L[0].split()); ranges.append((i0,min(i1,nl))); NL=nl
    for l in L[1:]:
        t=l.split()
        if len(t)==2: S[int(t[0])]=S.get(int(t[0]),0)+int(t[1])
ranges.sort(); pos=0
for a,b in ranges:
    assert a==pos, f'gap or overlap in line ranges at {pos}'; pos=b
assert pos==NL, 'chunks do not cover all lines'
print('N,S3,parallel,axis,generic')
for n in sorted(S):
    p,a=E[n]; print(f'{n},{S[n]},{p},{a},{S[n]-p-a}')
