import sympy as sp, pickle, time, sys, mpmath as mp
sys.path.insert(0,__import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from antider2 import int_log_shift, int_pow
a,b=sp.symbols('a b',positive=True)
H=pickle.load(open('Hbeta01.pkl','rb'))
def split_logs(expr):
    expr=sp.expand(sp.expand_log(expr,force=True))
    logs=sorted(expr.atoms(sp.log),key=str)
    parts={}; rest=expr
    for L in logs:
        co=rest.coeff(L); parts[L]=sp.cancel(sp.together(co)); rest=sp.expand(rest-co*L)
    parts[1]=sp.cancel(sp.together(rest))
    return parts
def laurent_b(R):
    num,den=sp.fraction(sp.cancel(R))
    pb=sp.Poly(den,b); assert len(pb.terms())==1,('nonmonomial den',den)
    (q,),dc=pb.terms()[0]
    P=sp.Poly(sp.expand(num),b)
    return {k-q: sp.cancel(co/dc) for (k,),co in P.terms()}
def antideriv(parts):
    F=[]
    for L,R in parts.items():
        lb=laurent_b(R)
        if L==1 or not L.has(b):
            fac=1 if L==1 else L
            F.append(('plain',None,None,fac*sum(cj*int_pow(j) for j,cj in lb.items())))
        else:
            s=sp.expand(L.args[0]-b)
            pos = (s!=0) and (s.subs(a,sp.Rational(1,3))>0)   # sign for 0<a<1: s=a>0, s=a-1<0
            A=0;B=0
            for j,cj in lb.items():
                Aj,Bj=int_log_shift(j,s,pos); A+=cj*Aj; B+=cj*Bj
            F.append(('log',s,sp.expand(A),B))
    return F
def evalF(F,bval):
    tot=0
    for kind,s,A,B in F:
        if kind=='plain': tot+=B.subs(b,bval); continue
        if sp.simplify(bval+s)==0:
            assert sp.simplify(A.subs(b,bval))==0
            tot+=B.subs(b,bval)
        else:
            tot+=A.subs(b,bval)*sp.log(bval+s)+B.subs(b,bval)
    return tot
t=time.time()
G={}
for nm in ['R1','R2']:
    parts=split_logs(H[nm]); print(nm,'logs:',[k for k in parts],flush=True)
    F=antideriv(parts)
    if nm=='R1':
        G[('R1','lo')]=(sp.Integer(0),sp.Rational(1,2), evalF(F,1-a)-evalF(F,a))
    else:
        G[('R2','A')]=(sp.Integer(0),sp.Rational(1,2), evalF(F,sp.Integer(1))-evalF(F,1-a))
        G[('R2','B')]=(sp.Rational(1,2),sp.Integer(1), evalF(F,sp.Integer(1))-evalF(F,a))
    print(nm,'done %.1fs'%(time.time()-t),flush=True)
pickle.dump(G,open('Gbeta.pkl','wb'))
