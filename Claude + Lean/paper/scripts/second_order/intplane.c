// Random primitive generic normals w=(w1,w2,-w3), lambda=|w|/N^2 sampled log-uniformly in [l1,l2], direction uniform.
// Points of [1,N]^3 on w.x=0 enumerated via a Gauss-reduced basis of the plane lattice (int128 arithmetic).
// Output: D_bin = (3 pi/(2 zeta3)) dlog * E[lam^3 F]   and   Delta-type value  3 pi dlog E[lam^3 (F - M^3 1{lam<1})]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
typedef long long ll; typedef __int128 i128;
static inline uint64_t rotl(const uint64_t x,int k){return (x<<k)|(x>>(64-k));}
typedef struct{uint64_t s[4];} rng;
static inline uint64_t nxt(rng*r){uint64_t*s=r->s;const uint64_t res=rotl(s[1]*5,7)*9,t=s[1]<<17;s[2]^=s[0];s[3]^=s[1];s[1]^=s[2];s[0]^=s[3];s[2]^=t;s[3]=rotl(s[3],45);return res;}
static inline double U(rng*r){return (nxt(r)>>11)*0x1.0p-53;}
static inline double gauss(rng*r){double u1=U(r),u2=U(r); if(u1<1e-300)u1=1e-300; return sqrt(-2*log(u1))*cos(2*M_PI*u2);}
static ll gcdll(ll a,ll b){if(a<0)a=-a;if(b<0)b=-b;while(b){ll t=a%b;a=b;b=t;}return a;}
static ll egcd(ll a,ll b,ll*x,ll*y){ ll x0=1,y0=0,x1=0,y1=1; while(b){ ll q=a/b,t=a-q*b; a=b;b=t; t=x0-q*x1;x0=x1;x1=t; t=y0-q*y1;y0=y1;y1=t;} *x=x0;*y=y0; return a; }
static double A2(double s,double t){ double p1=1-s>0?(1-s)*(1-s):0,p2=1-t>0?(1-t)*(1-t):0,p3=1-s-t>0?(1-s-t)*(1-s-t):0; return (1-p1-p2+p3)/(2*s*t);}
static inline i128 dot(const i128*a,const i128*b){return a[0]*b[0]+a[1]*b[1]+a[2]*b[2];}
static inline i128 rdiv(i128 a,i128 b){ // round(a/b), b>0
  i128 q=a/b, r=a-q*b; if(2*r>b) q++; else if(2*r<-b) q--; return q; }
static inline ll floordiv(ll a,ll b){ ll q=a/b; if((a%b!=0)&&((a<0)!=(b<0))) q--; return q; }
static inline ll ceildiv(ll a,ll b){ return -floordiv(-a,b); }
typedef struct{ll a,b,c;} trip;
static int cmpt(const void*x,const void*y){const trip*p=x,*q=y; if(p->a!=q->a) return p->a<q->a?-1:1; if(p->b!=q->b) return p->b<q->b?-1:1; if(p->c!=q->c) return p->c<q->c?-1:1; return 0;}
int main(int argc,char**argv){
  ll N=atoll(argv[1]); double l1=atof(argv[2]), l2=atof(argv[3]); long ns=atol(argv[4]); unsigned long long seed=strtoull(argv[5],0,10);
  double dlog=log(l2)-log(l1);
  double s1=0,s1q=0,s2=0,s2q=0,s3=0,s3q=0,sl=0; long acc=0, rej=0;
  #pragma omp parallel reduction(+:s1,s1q,s2,s2q,s3,s3q,sl,acc,rej)
  { rng r; int tid=0;
    #ifdef _OPENMP
    #include <omp.h>
    tid=omp_get_thread_num();
    #endif
    r.s[0]=seed*0x9E3779B97F4A7C15ULL+tid*7919+3; r.s[1]=0xBF58476D1CE4E5B9ULL^(seed*31+tid); r.s[2]=0x94D049BB133111EBULL+tid*101; r.s[3]=0x2545F4914F6CDD1DULL*(tid+11);
    for(int i=0;i<20;i++) nxt(&r);
    long cap=1<<20; trip*pts=malloc(sizeof(trip)*cap);
    #pragma omp for schedule(dynamic,1000)
    for(long it=0;it<ns;it++){
      ll w1,w2,w3; double lam;
      while(1){ double g1=fabs(gauss(&r)),g2=fabs(gauss(&r)),g3=fabs(gauss(&r)); double nn=sqrt(g1*g1+g2*g2+g3*g3);
        double lt=exp(log(l1)+dlog*U(&r)); double R=lt*(double)N*(double)N;
        w1=llround(g1/nn*R); w2=llround(g2/nn*R); w3=llround(g3/nn*R);
        if(w1<1||w2<1||w3<1){rej++;continue;}
        lam=sqrt((double)w1*w1+(double)w2*w2+(double)w3*w3)/((double)N*N);
        if(gcdll(gcdll(w1,w2),w3)!=1){rej++;continue;} break; }
      // basis of {x: w1 x1 + w2 x2 - w3 x3 = 0}
      ll s,t; ll g=egcd(w1,w2,&s,&t);   // s w1 + t w2 = g
      i128 b1[3]={(i128)(w2/g),(i128)(-(w1/g)),0}, b2[3]={(i128)w3*s,(i128)w3*t,(i128)g};
      // reduce s modulo w2/g first (keeps entries small), then one safe reduction step of b2 by b1
      { ll m2=w2/g, m1=w1/g; ll k=floordiv(s+m2/2,m2); s-=k*m2; t+=k*m1;
        b2[0]=(i128)w3*s; b2[1]=(i128)w3*t; b2[2]=g; }
      { i128 q=rdiv(dot(b1,b2),dot(b1,b1)); for(int k=0;k<3;k++) b2[k]-=q*b1[k]; }
      // Gauss reduction
      for(int iter=0;iter<200;iter++){
        i128 n1=dot(b1,b1), n2=dot(b2,b2);
        if(n2<n1){ for(int k=0;k<3;k++){i128 tt=b1[k];b1[k]=b2[k];b2[k]=tt;} continue; }
        i128 q=rdiv(dot(b1,b2),n1);
        if(q==0) break;
        for(int k=0;k<3;k++) b2[k]-=q*b1[k];
      }
      ll B1[3]={(ll)b1[0],(ll)b1[1],(ll)b1[2]}, B2[3]={(ll)b2[0],(ll)b2[1],(ll)b2[2]};
      // enumerate m B1 + n B2 in [1,N]^3. |n| <= sqrt3 N |B1| / |w|
      double nb1=sqrt((double)B1[0]*B1[0]+(double)B1[1]*B1[1]+(double)B1[2]*B1[2]);
      double wn=lam*(double)N*N;
      ll nmax=(ll)ceil(sqrt(3.0)*(double)N*nb1/wn)+1;
      long L=0;
      for(ll n=-nmax;n<=nmax;n++){
        ll mlo=-(1LL<<62), mhi=(1LL<<62); int ok=1;
        for(int k=0;k<3;k++){
          ll c=n*B2[k];  // need 1 <= m*B1[k] + c <= N
          if(B1[k]==0){ if(c<1||c>N){ok=0;break;} continue; }
          ll lo,hi;
          if(B1[k]>0){ lo=ceildiv(1-c,B1[k]); hi=floordiv(N-c,B1[k]); }
          else { lo=ceildiv(N-c,B1[k]); hi=floordiv(1-c,B1[k]); }
          if(lo>mlo) mlo=lo; if(hi<mhi) mhi=hi;
        }
        if(!ok||mlo>mhi) continue;
        for(ll m=mlo;m<=mhi;m++){
          ll x=m*B1[0]+n*B2[0], y=m*B1[1]+n*B2[1], z=m*B1[2]+n*B2[2];
          ll gg=gcdll(gcdll(x,y),z);
          if(L<cap){ pts[L].a=x/gg; pts[L].b=y/gg; pts[L].c=z/gg; } L++;
        }
      }
      long long par=0;
      if(L>0){ long Lc=L<cap?L:cap; qsort(pts,Lc,sizeof(trip),cmpt);
        long run=1; for(long i=1;i<=Lc;i++){ if(i<Lc && cmpt(&pts[i],&pts[i-1])==0) run++; else { par+=(long long)run*run; run=1; } } }
      double F=(double)L*((double)L*L-(double)par);
      double M=A2((double)w1/w3,(double)w2/w3)*(double)N*(double)N/(double)w3;
      double v1=lam*lam*lam*F, v2=lam*lam*lam*(F-(lam<1?M*M*M:0));
      double v3=lam*lam*lam*(F-3*M*M*((double)L-M)-(lam<1?M*M*M:0)); s1+=v1; s1q+=v1*v1; s2+=v2; s2q+=v2*v2; s3+=v3; s3q+=v3*v3; sl+=(double)L-M; acc++;
    }
    free(pts); }
  double z3=1.2020569031595942;
  double m1=s1/acc, e1=sqrt((s1q/acc-m1*m1)/acc), m2=s2/acc, e2=sqrt((s2q/acc-m2*m2)/acc);
  double f1=3*M_PI/(2*z3)*dlog, f2=3*M_PI*dlog;
  double m3=s3/acc, e3=sqrt((s3q/acc-m3*m3)/acc);
  printf("N=%lld lam in [%.4g,%.4g]: D_bin = %.5f +- %.5f   Delta-part plain = %.5f +- %.5f   control = %.5f +- %.5f   mean(L-M)=%.4f (n=%ld)\n",N,l1,l2,f1*m1,f1*e1,f2*m2,f2*e2,f2*m3,f2*e3,sl/acc,acc);
  return 0; }
