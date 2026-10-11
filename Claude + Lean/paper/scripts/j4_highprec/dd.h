#include <math.h>
typedef struct { double hi, lo; } dd;
static inline dd two_sum(double a,double b){double s=a+b;double bb=s-a;double e=(a-(s-bb))+(b-bb);dd r={s,e};return r;}
static inline dd quick_two_sum(double a,double b){double s=a+b;double e=b-(s-a);dd r={s,e};return r;}
static inline dd two_prod(double a,double b){double p=a*b;double e=fma(a,b,-p);dd r={p,e};return r;}
static inline dd ddd(double a){dd r={a,0};return r;}
static inline dd dd_add(dd a,dd b){dd s=two_sum(a.hi,b.hi);dd t=two_sum(a.lo,b.lo);s.lo+=t.hi;s=quick_two_sum(s.hi,s.lo);s.lo+=t.lo;return quick_two_sum(s.hi,s.lo);}
static inline dd dd_neg(dd a){dd r={-a.hi,-a.lo};return r;}
static inline dd dd_sub(dd a,dd b){return dd_add(a,dd_neg(b));}
static inline dd dd_mul(dd a,dd b){dd p=two_prod(a.hi,b.hi);p.lo+=a.hi*b.lo+a.lo*b.hi;return quick_two_sum(p.hi,p.lo);}
static inline dd dd_muld(dd a,double b){dd p=two_prod(a.hi,b);p.lo+=a.lo*b;return quick_two_sum(p.hi,p.lo);}
static inline dd dd_div(dd a,dd b){double q1=a.hi/b.hi;dd r=dd_sub(a,dd_muld(b,q1));double q2=r.hi/b.hi;r=dd_sub(r,dd_muld(b,q2));double q3=r.hi/b.hi;dd q=quick_two_sum(q1,q2);return dd_add(q,ddd(q3));}
static inline dd dd_divd(dd a,double b){return dd_div(a,ddd(b));}
static inline int dd_lt(dd a,dd b){return a.hi<b.hi||(a.hi==b.hi&&a.lo<b.lo);}
static inline int dd_le(dd a,dd b){return !dd_lt(b,a);}
static inline int dd_gt0(dd a){return a.hi>0||(a.hi==0&&a.lo>0);}
static inline dd dd_powi(dd a,int n){ if(n==0) return ddd(1); int neg=n<0; if(neg)n=-n; dd r=ddd(1),b=a; while(n){ if(n&1) r=dd_mul(r,b); b=dd_mul(b,b); n>>=1;} return neg?dd_div(ddd(1),r):r;}
static const dd DD_LN2={6.931471805599452862e-01,2.319046813846299558e-17};
static dd dd_exp(dd a){ // a moderate
  double k=floor(a.hi/DD_LN2.hi+0.5); dd r=dd_sub(a,dd_muld(DD_LN2,k));
  // r in [-0.35,0.35]; scale down by 2^8
  r.hi=ldexp(r.hi,-8); r.lo=ldexp(r.lo,-8);
  dd s=ddd(1),t=ddd(1); for(int i=1;i<=22;i++){ t=dd_divd(dd_mul(t,r),(double)i); s=dd_add(s,t);} 
  for(int i=0;i<8;i++) s=dd_mul(s,s);
  s.hi=ldexp(s.hi,(int)k); s.lo=ldexp(s.lo,(int)k); return s;}
static dd dd_log(dd a){ dd y=ddd(log(a.hi)); for(int i=0;i<2;i++){ dd e=dd_exp(dd_neg(y)); y=dd_add(y,dd_sub(dd_mul(a,e),ddd(1))); } return y; }
static inline dd dd_abs(dd a){return (a.hi<0)?dd_neg(a):a;}
