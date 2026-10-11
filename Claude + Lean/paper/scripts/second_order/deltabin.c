// Monte Carlo for Delta = int_0^inf lam^2 dlam int_{S^2} du [ E_Haar F(Lambda, S_{u,lam}) - alpha(u)^3 lam^-3 1{lam<1} ]
// F = L*(L^2 - par), S_{u,lam} = lam^{-1/2} (u^perp ∩ (0,1]^3).  Lambda Haar-random unimodular lattice in the plane.
// Plain estimator (no control variate): prints the stratum estimate of int lam^2 E[F] dlam du. For strata below lam=1 subtract J*log(hi/lo).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
static inline uint64_t rotl(const uint64_t x,int k){return (x<<k)|(x>>(64-k));}
typedef struct{uint64_t s[4];} rng;
static inline uint64_t nxt(rng*r){uint64_t*s=r->s;const uint64_t res=rotl(s[1]*5,7)*9,t=s[1]<<17;s[2]^=s[0];s[3]^=s[1];s[1]^=s[2];s[0]^=s[3];s[2]^=t;s[3]=rotl(s[3],45);return res;}
static inline double U(rng*r){return (nxt(r)>>11)*0x1.0p-53;}
static inline double gauss(rng*r){double u1=U(r),u2=U(r); if(u1<1e-300)u1=1e-300; return sqrt(-2*log(u1))*cos(2*M_PI*u2);}
static double A2(double s,double t){ double p1=1-s>0?(1-s)*(1-s):0,p2=1-t>0?(1-t)*(1-t):0,p3=1-s-t>0?(1-s-t)*(1-s-t):0; return (1-p1-p2+p3)/(2*s*t);}
static inline long gcdl(long a,long b){if(a<0)a=-a;if(b<0)b=-b;while(b){long t=a%b;a=b;b=t;}return a;}
// simple hash for directions
typedef struct{long long key; int cnt; int stamp;} slot;
#define HB 16
#define HS (1<<HB)
int main(int argc,char**argv){
  long nsamp=atol(argv[1]); double L0=atof(argv[2]); int stratum=atoi(argv[3]); unsigned long long seed=strtoull(argv[4],0,10);
  double lo=L0, hi=atof(argv[5]);
  int NB=20; // diagnostic bins in log lambda
  double sum=0,sum2=0; double bsum[64]={0},bsum2[64]={0}; long bcnt[64]={0}; double sL=0;
  #pragma omp parallel reduction(+:sum,sum2,sL)
  {
    rng r; int tid=0;
    #ifdef _OPENMP
    #include <omp.h>
    tid=omp_get_thread_num();
    #endif
    r.s[0]=seed*0x9E3779B97F4A7C15ULL+tid*1234567+1; r.s[1]=0xBF58476D1CE4E5B9ULL^(seed+tid); r.s[2]=0x94D049BB133111EBULL+tid; r.s[3]=0x2545F4914F6CDD1DULL*(tid+7);
    for(int i=0;i<20;i++) nxt(&r);
    slot*T=calloc(HS,sizeof(slot)); int stamp=0;
    double lb[64]={0},lb2[64]={0}; long lc[64]={0};
    #pragma omp for schedule(dynamic,1000)
    for(long it=0;it<nsamp;it++){
      // direction in orthant (+,+,-)
      double g1=fabs(gauss(&r)),g2=fabs(gauss(&r)),g3=fabs(gauss(&r)); double nn=sqrt(g1*g1+g2*g2+g3*g3);
      double u1=g1/nn,u2=g2/nn,u3=-g3/nn;
      double alpha=A2(u1/(-u3),u2/(-u3))/(-u3);
      // lambda uniform in [lo,hi]
      double lam=exp(log(lo)+(log(hi)-log(lo))*U(&r));
      double sc=1.0/sqrt(lam);          // box side
      double A=alpha/lam;
      // frame
      double q=sqrt(u1*u1+u2*u2); double f1[3]={u2/q,-u1/q,0}; double f2[3]={u2*f1[2]-u3*f1[1], u3*f1[0]-u1*f1[2], u1*f1[1]-u2*f1[0]};
      // Haar lattice: x=sin(phi), phi in [-pi/6,pi/6]; y=sqrt(1-x^2)/U ; rotation th in [0,pi)
      double x=sin((U(&r)-0.5)*M_PI/3); double y=sqrt(1-x*x)/(1-U(&r)); double th=M_PI*U(&r);
      double sy=sqrt(y); double b1x=1/sy,b1y=0,b2x=x/sy,b2y=sy;
      double c=cos(th),s=sin(th);
      double v1x=c*b1x-s*b1y,v1y=s*b1x+c*b1y,v2x=c*b2x-s*b2y,v2y=s*b2x+c*b2y;
      double D=sqrt(3.0)*sc+1e-9;
      long L=0; long long par=0; stamp++; if(stamp==0x7fffffff){memset(T,0,HS*sizeof(slot));stamp=1;}
      long nmax=(long)floor(D/sy);
      for(long n=-nmax;n<=nmax;n++){
        double rem=D*D-(double)n*n*y; if(rem<0) continue; double hw=sqrt(rem)*sy;
        long m0=(long)ceil(-n*x-hw), m1=(long)floor(-n*x+hw);
        for(long m=m0;m<=m1;m++){
          if(m==0&&n==0) continue;
          double px=m*v1x+n*v2x, py=m*v1y+n*v2y;
          double X=px*f1[0]+py*f2[0], Y=px*f1[1]+py*f2[1], Z=px*f1[2]+py*f2[2];
          if(X<=0||Y<=0||Z<=0||X>sc||Y>sc||Z>sc) continue;
          L++;
          long g=gcdl(m,n); long a=m/g,b=n/g;
          long long key=((long long)(a+1000000000LL))*2000000001LL+(b+1000000000LL);
          uint64_t h=((uint64_t)key*0x9E3779B97F4A7C15ULL)>>(64-HB);
          while(1){ slot*sl=&T[h]; if(sl->stamp!=stamp){sl->stamp=stamp;sl->key=key;sl->cnt=1;par+=1;break;}
                    if(sl->key==key){par+=2*sl->cnt+1;sl->cnt++;break;} h=(h+1)&(HS-1);} }
      }
      double F=(double)L*((double)L*L-(double)par);
      double val;
      val=lam*lam*lam*F; val*=3*M_PI*(log(hi)-log(lo));     // 6 orthants * area(pi/2) * (hi-lo) [uniform lambda density]
      sum+=val; sum2+=val*val; sL+=(L-A);
      int bi=(int)floor((log(lam)-log(lo))/(log(hi)-log(lo))*NB); if(bi<0)bi=0; if(bi>=NB)bi=NB-1;
      lb[bi]+=lam*lam*(stratum==0?(F-3*A*A*(L-A)-A*A*A):F); lb2[bi]+=lam; lc[bi]++;
    }
    #pragma omp critical
    for(int i=0;i<NB;i++){bsum[i]+=lb[i];bsum2[i]+=lb2[i];bcnt[i]+=lc[i];}
    free(T);
  }
  double mean=sum/nsamp, se=sqrt((sum2/nsamp-mean*mean)/nsamp);
  printf("stratum %d lam in [%g,%g]: estimate %.6f +- %.6f   (mean L-A = %.4f)\n",stratum,lo,hi,mean,se,sL/nsamp);
  printf("  binned h(lam) = E[lam^2 (F - ...)] averaged over u:\n");
  for(int i=0;i<NB;i++) if(bcnt[i]) printf("    lam~%.4f  h=%.4f  (n=%ld)\n",bsum2[i]/bcnt[i],3*M_PI*bsum[i]/bcnt[i],bcnt[i]);
  return 0; }
