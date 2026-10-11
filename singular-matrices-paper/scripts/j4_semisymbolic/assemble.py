import sympy as sp, pickle, sys, time
a,b,u=sp.symbols('a b u',positive=True)
Lg=sp.Symbol('Lg')   # placeholder for log(u-b)
Li2=lambda z: sp.polylog(2,z)
def int_pow(m): return sp.log(b) if m==-1 else b**(m+1)/(m+1)
def int_over_umb(k):   # returns (coef of Lg, rest)
    if k>=0: return (-u**k, -sum(u**j*b**(k-j)/(k-j) for j in range(k)))
    K=-k; return (-u**(-K), sum(u**(j-K-1)*int_pow(-j) for j in range(1,K+1)))
def int_log(m):        # int b^m log(u-b) db = A*Lg + B
    if m==-1: return (sp.Integer(0), sp.log(u)*sp.log(b)-Li2(b/u))
    cA,rest=int_over_umb(m+1)
    return (b**(m+1)/(m+1)+cA/(m+1), rest/(m+1))
def laurent_b(R):
    num,den=sp.fraction(sp.cancel(R))
    pb=sp.Poly(den,b); assert len(pb.terms())==1
    (q,),dc=pb.terms()[0]
    P=sp.Poly(sp.expand(num),b)
    return {k-q: sp.cancel(co/dc) for (k,),co in P.terms()}
def antideriv(parts):
    """returns dict: kind -> (A_expr, B_expr, uval); total F = sum A*log(u-b) + B"""
    out=[]
    for L,R in parts.items():
        lb=laurent_b(R)
        if L==1 or (L!=1 and not L.has(b)):
            fac=1 if L==1 else L
            out.append(('plain',0,fac*sum(cj*int_pow(j) for j,cj in lb.items()),None))
        else:
            arg=L.args[0]
            uval=sp.simplify(arg+b)          # log(uval - b)
            A=0;B=0
            for j,cj in lb.items():
                Aj,Bj=int_log(j); A+=cj*Aj; B+=cj*Bj
            out.append(('log',A.subs(u,uval),B.subs(u,uval),uval))
    return out
def evalF(F,bval,singular_ok=True):
    tot=0
    for kind,A,B,uval in F:
        if kind=='plain': tot+=B.subs(b,bval); continue
        if sp.simplify(bval-uval)==0:
            Au=sp.simplify(A.subs(b,bval)); assert Au==0, ('nonvanishing log coefficient',Au)
            tot+=B.subs(b,bval)
        else:
            tot+=A.subs(b,bval)*sp.log(uval-bval)+B.subs(b,bval)
    return tot
def limit_inf(F):
    tot=0
    for kind,A,B,uval in F:
        assert kind=='plain'
        tot+=sp.limit(B,b,sp.oo)
    return tot
if __name__=='__main__':
    name=sys.argv[1]
    parts=pickle.load(open(f'parts_{name}.pkl','rb'))
    t=time.time(); F=antideriv(parts); print('antiderivative built %.1fs'%(time.time()-t),flush=True)
    G={}
    if name=='i':
        G['lo']= (sp.Integer(0),sp.Rational(1,2), evalF(F,1-a)-evalF(F,a))
    elif name=='ii':
        G['A']= (sp.Integer(0),sp.Rational(1,2), evalF(F,sp.Integer(1))-evalF(F,1-a))
        G['B']= (sp.Rational(1,2),sp.Integer(1), evalF(F,sp.Integer(1))-evalF(F,a))
    elif name=='iii':
        G['A']= (sp.Integer(0),sp.Integer(1), limit_inf(F)-evalF(F,sp.Integer(1)))
    elif name=='iv':
        G['A']= (sp.Integer(1),sp.oo, limit_inf(F)-evalF(F,a))
    print('G built %.1fs'%(time.time()-t),flush=True)
    pickle.dump(G,open(f'G_{name}.pkl','wb'))
