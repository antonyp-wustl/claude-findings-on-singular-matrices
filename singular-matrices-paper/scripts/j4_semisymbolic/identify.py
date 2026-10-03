"""Check the closed forms of I_alpha, I_beta and J_4 (main.tex, label prop:J4) against the stored digits, and re-run PSLQ.
Usage: python3 identify.py      (reads I_alpha_150digits.txt and I_beta_110digits.txt)"""
import os, mpmath as mp
here=os.path.dirname(os.path.abspath(__file__))
mp.mp.dps=160
Ia=mp.mpf(open(os.path.join(here,'I_alpha_150digits.txt')).read().strip())
Ib=mp.mpf(open(os.path.join(here,'I_beta_110digits.txt')).read().strip())
pi2,z3,l2=mp.pi**2,mp.zeta(3),mp.log(2)
Ia_cf=mp.mpf(2200223)/38880+mp.mpf(1351)/648*pi2-mp.mpf(116389)/216*z3+mp.mpf(333724)/405*l2
Ib_cf=mp.mpf(7271461)/87480-mp.mpf(4789)/1458*pi2+mp.mpf(4985)/54*z3-mp.mpf(31184)/135*l2
J4=mp.mpf(1387213)/1458-mp.mpf(736)/243*pi2-mp.mpf(101434)/27*z3+mp.mpf(421696)/81*l2
print('I_alpha - closed form =',mp.nstr(Ia-Ia_cf,3))
print('I_beta  - closed form =',mp.nstr(Ib-Ib_cf,3))
print('8 I_alpha + 6 I_beta - J4 closed form =',mp.nstr(8*Ia_cf+6*Ib_cf-J4,3))
print('J4 =',mp.nstr(J4,30),'  C4 = 135 J4/pi^4 =',mp.nstr(135*J4/mp.pi**4,20),'  p4(0) = J4/2 =',mp.nstr(J4/2,20))
for name,x,d in [('I_alpha',Ia,140),('I_beta',Ib,100)]:
    with mp.workdps(d):
        print('PSLQ',name,'[x,1,pi^2,zeta3,log2]:',mp.pslq([x,1,pi2,z3,l2],maxcoeff=10**12,maxsteps=10**6))
