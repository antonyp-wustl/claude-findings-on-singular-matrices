import sympy as sp
a,b=sp.symbols('a b',positive=True)
def int_pow(m): return sp.log(b) if m==-1 else b**(m+1)/(m+1)
def int_log_shift(m,s,s_positive):
    """int b^m log(b+s) db = A*log(b+s) + B ; s is a sympy expr (may be 0), s_positive: sign of s in region"""
    if s==0:
        if m==-1: return (sp.Integer(0), sp.log(b)**2/2)
        return (b**(m+1)/(m+1), -b**(m+1)/(m+1)**2)
    if m==-1:
        if s_positive: return (sp.Integer(0), sp.log(s)*sp.log(b)-sp.polylog(2,-b/s))
        else:          return (sp.Integer(0), sp.log(b)**2/2+sp.polylog(2,-s/b))
    k=m+1
    A=(b**k-(-s)**k)/k
    if k>=1:
        B=-sum((-s)**j*b**(k-j)/(k-j) for j in range(k))/k
    else:
        K=-k
        B=sum((-1)**(K-j)*s**(j-K-1)*int_pow(-j) for j in range(1,K+1))/K
    return (A,B)
if __name__=='__main__':
    sp_,sn_=sp.Symbol('sp',positive=True),sp.Symbol('sn',negative=True)
    for s,pos in [(0,True),(sp_,True),(sn_,False)]:
        for m in range(-4,10):
            A,B=int_log_shift(m,s,pos)
            F=A*sp.log(b+s)+B
            d=sp.diff(F,b)-b**m*sp.log(b+s)
            d=d.replace(lambda e: isinstance(e,sp.polylog) and e.args[0]==1, lambda e: -sp.log(1-e.args[1]))
            d=sp.simplify(sp.expand_log(sp.expand(d),force=True))
            if d!=0:
                # numeric spot check (branch issues with symbolic simplify)
                import random
                vals={b:sp.Rational(7,5)}; 
                if s!=0: vals[s.free_symbols.pop()]= (sp.Rational(3,10) if pos else -sp.Rational(3,10))
                dv=sp.N(d.subs(vals),30)
                assert abs(dv)<1e-25,(s,m,d,dv)
    print('shift antiderivatives verified')
