import sympy as sp, pickle, time, sys
a,b,c=sp.symbols('a b c',positive=True)
H=pickle.load(open('Halpha.pkl','rb'))
def split_logs(expr):
    expr=sp.expand(sp.expand_log(expr,force=True))
    logs=sorted(expr.atoms(sp.log),key=str)
    parts={}
    rest=expr
    for L in logs:
        co=rest.coeff(L)
        parts[L]=sp.cancel(sp.together(co))
        rest=sp.expand(rest-co*L)
    parts[1]=sp.cancel(sp.together(rest))
    return parts
t=time.time()
name=sys.argv[1]
parts=split_logs(H[name])
for k,v in parts.items():
    num,den=sp.fraction(v)
    print(name,'log factor',k,' num deg (a,b)=',sp.Poly(num,a,b).total_degree(),' den=',sp.factor(den),flush=True)
pickle.dump(parts,open(f'parts_{name}.pkl','wb'))
print('time',time.time()-t)
