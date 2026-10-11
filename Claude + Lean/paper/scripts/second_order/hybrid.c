// Hybrid estimate of the generic-plane total G(N) = sum_{generic planes} L_P I_P   (I_P = L_P^2 - par_P)
// orthant w=(w1,w2,-w3), w_i>=1 ; planes = 3 x orthant sum.
// exact for |w|<=W0 ; MC (log-uniform |w|, control variate M^3 with exactly known stratum sums) for W0<|w|<=3N^2.
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
static inline i128 dot(const i128*a,const i128*b){return a[0]*b[0]+a[1]*b[1]+a[2]*b[2];}
static inline i128 rdiv(i128 a,i128 b){ i128 q=a/b, r=a-q*b; if(2*r>b) q++; else if(2*r<-b) q--; return q; }
static inline ll floordiv(ll a,ll b){ ll q=a/b; if((a%b!=0)&&((a<0)!=(b<0))) q--; return q; }
static inline ll ceildiv(ll a,ll b){ return -floordiv(-a,b); }
static double fval(ll a,ll b,ll c){ // alpha^3/|w|^3 for w=(a,b,-c)   (int128 to avoid overflow)
  i128 A=a,B=b,C=c; i128 t1=C-A>0?(C-A)*(C-A):0, t2=C-B>0?(C-B)*(C-B):0, t3=C-A-B>0?(C-A-B)*(C-A-B):0;
  double n=(double)(C*C-t1-t2+t3); double ar=n/(2.0*(double)a*(double)b); return ar*ar*ar/((double)c*c*c); }
// F = L (L^2 - par) for plane w1 x + w2 y = w3 z in [1,N]^3
static double planeF(ll N,ll w1,ll w2,ll w3,ll *Lout){
  ll s,t; ll g=egcd(w1,w2,&s,&t);
  i128 b1[3]={(i128)(w2/g),(i128)(-(w1/g)),0}, b2[3];
  { ll m2=w2/g, m1=w1/g; ll k=floordiv(s+m2/2,m2); s-=k*m2; t+=k*m1; b2[0]=(i128)w3*s; b2[1]=(i128)w3*t; b2[2]=g; }
  { i128 q=rdiv(dot(b1,b2),dot(b1,b1)); for(int k=0;k<3;k++) b2[k]-=q*b1[k]; }
  for(int iter=0;iter<200;iter++){ i128 n1=dot(b1,b1), n2=dot(b2,b2);
    if(n2<n1){ for(int k=0;k<3;k++){i128 tt=b1[k];b1[k]=b2[k];b2[k]=tt;} continue; }
    i128 q=rdiv(dot(b1,b2),n1); if(q==0) break; for(int k=0;k<3;k++) b2[k]-=q*b1[k]; }
  ll B1[3]={(ll)b1[0],(ll)b1[1],(ll)b1[2]}, B2[3]={(ll)b2[0],(ll)b2[1],(ll)b2[2]};
  double nb1=sqrt((double)B1[0]*B1[0]+(double)B1[1]*B1[1]+(double)B1[2]*B1[2]);
  double wn=sqrt((double)w1*w1+(double)w2*w2+(double)w3*w3);
  ll nmax=(ll)ceil(sqrt(3.0)*(double)N*nb1/wn)+1;
  ll L=0; double par=0;
  for(ll n=-nmax;n<=nmax;n++){
    ll mlo=-(1LL<<62), mhi=(1LL<<62); int ok=1;
    for(int k=0;k<3;k++){ ll c=n*B2[k];
      if(B1[k]==0){ if(c<1||c>N){ok=0;break;} continue; }
      ll lo,hi; if(B1[k]>0){ lo=ceildiv(1-c,B1[k]); hi=floordiv(N-c,B1[k]); } else { lo=ceildiv(N-c,B1[k]); hi=floordiv(1-c,B1[k]); }
      if(lo>mlo) mlo=lo; if(hi<mhi) mhi=hi; }
    if(!ok||mlo>mhi) continue;
    for(ll m=mlo;m<=mhi;m++){ ll x=m*B1[0]+n*B2[0], y=m*B1[1]+n*B2[1], z=m*B1[2]+n*B2[2];
      L++; if(gcdll(gcdll(x,y),z)==1){ ll mx=x>y?x:y; if(z>mx) mx=z; double k=(double)(N/mx); par+=k*k; } }
  }
  *Lout=L; return (double)L*((double)L*(double)L-par);
}

static int *MU=NULL; static ll *MERT=NULL; static ll MUN=0;
static void init_mu(ll n){ MUN=n; MU=malloc(sizeof(int)*(n+1)); MERT=malloc(sizeof(ll)*(n+1)); char*comp=calloc(n+1,1);
  for(ll i=0;i<=n;i++) MU[i]=1; MU[0]=0;
  for(ll p=2;p<=n;p++) if(!comp[p]){ for(ll k=2*p;k<=n;k+=p) comp[k]=1; for(ll k=p;k<=n;k+=p) MU[k]=-MU[k]; for(ll k=p*p;k<=n;k+=p*p) MU[k]=0; }
  MERT[0]=0; for(ll i=1;i<=n;i++) MERT[i]=MERT[i-1]+MU[i]; free(comp); }
// number of points of [1,Y]^3 on w1 x + w2 y = w3 z
static ll countY(ll Y, ll w1,ll w2,ll w3, ll g, ll a, ll b, ll inv){
  ll cnt=0;
  for(ll z=1;z<=Y;z++){
    ll rhs=w3*z; if(rhs%g) continue; ll r=rhs/g;           // a x + b y = r
    ll lo=ceildiv(r-b*Y,a); if(lo<1) lo=1; ll hi=floordiv(r-b,a); if(hi>Y) hi=Y; if(hi<lo) continue;
    ll x0; if(b==1) x0=0; else { x0=(ll)(((i128)(r%b)*inv)%b); }
    cnt+= floordiv(hi-x0,b)-floordiv(lo-1-x0,b);
  }
  return cnt; }
// F via counting: L=Count(N), par = sum_k (2k-1) Prim(N/k), Prim(Y)=sum_d mu(d) Count(Y/d); Count needed only at floor(N/m)
static double planeF_count(ll N,ll w1,ll w2,ll w3,ll *Lout){
  ll g=gcdll(w1,w2), a=w1/g, b=w2/g; ll inv=0; if(b>1){ ll x,y; egcd(((a%b)+b)%b,b,&x,&y); inv=((x%b)+b)%b; }
  // distinct values v=floor(N/m): store Count in table indexed: v<=sqrtN -> small[v], else big[N/v]
  ll sq=(ll)sqrt((double)N); while((sq+1)*(sq+1)<=N) sq++; while(sq*sq>N) sq--;
  ll *small=malloc(sizeof(ll)*(sq+2)), *big=malloc(sizeof(ll)*(sq+2));
  for(ll v=1;v<=sq;v++) small[v]=countY(v,w1,w2,w3,g,a,b,inv);
  for(ll m=1;m<=sq;m++){ ll v=N/m; big[m]=(v<=sq)?small[v]:countY(v,w1,w2,w3,g,a,b,inv); }
  #define CNT(v) ((v)<=0?0:((v)<=sq?small[(v)]:big[N/(v)]))
  // Prim(Y) for Y=floor(N/k): sum_d mu(d) Count(floor(Y/d)) grouped in blocks
  double par=0; ll L=CNT(N);
  for(ll k=1;k<=N;){ ll q=N/k, k2=N/q;            // all k in [k,k2] have floor(N/k)=q
    // Prim(q)
    ll pr=0; for(ll d=1;d<=q;){ ll t=q/d, d2=q/t; pr+=(MERT[d2]-MERT[d-1])*CNT(t); d=d2+1; }
    double wgt=(double)k2*k2-(double)(k-1)*(k-1);
    par+=wgt*(double)pr; k=k2+1; }
  free(small); free(big);
  *Lout=L; return (double)L*((double)L*L-par); }

int main(int argc,char**argv){
  ll N=atoll(argv[1]); int W0=atoi(argv[2]); long nmc=atol(argv[3]); unsigned long long seed=strtoull(argv[4],0,10);
  init_mu(N+5);
  double z3=1.2020569031595942, C3=15*(12-M_PI*M_PI)/(4*z3), K0=-7.98209;
  // ---- exact part |w|<=W0 ; also exact control sums S(X) for X<=XMAX via direct enumeration
  int XMAX=2000; long X2=(long)XMAX*XMAX;
  double *bin=calloc(X2+1,sizeof(double));     // primitive orthant f binned by |w|^2 (direct, with gcd)
  double exactF=0, exactM=0;
  #pragma omp parallel
  { double *loc=calloc(X2+1,sizeof(double));
    #pragma omp for schedule(dynamic) reduction(+:exactF,exactM)
    for(int c=1;c<=XMAX;c++) for(int a=1;(long)a*a+(long)c*c<=X2;a++) for(int b=1;(long)a*a+(long)b*b+(long)c*c<=X2;b++){
      if(gcdll(gcdll(a,b),c)!=1) continue;
      long r2=(long)a*a+(long)b*b+(long)c*c; double f=fval(a,b,c); loc[r2]+=f;
      if(r2<=(long)W0*W0){ ll L; double Mexp=cbrt(f)*(double)N*N; exactF+= (Mexp>2000? planeF_count(N,a,b,c,&L) : planeF(N,a,b,c,&L)); exactM+=f*pow((double)N,6); } }
    #pragma omp critical
    for(long i=0;i<=X2;i++) bin[i]+=loc[i];
    free(loc); }
  for(long i=1;i<=X2;i++) bin[i]+=bin[i-1];
  #define SEX(X) ( (X)<=XMAX ? bin[(long)floor((X)*(X)+1e-9)] : (C3*log(X)+K0+8.4/(X))/6.0 )
  // ---- MC strata on (W0, 3N^2]
  double Rmax=3.0*(double)N*N; int NS=14; double lo0=log((double)W0), hi0=log(Rmax);
  double total=exactF, var=0;
  for(int st=0;st<NS;st++){
    double R1=exp(lo0+(hi0-lo0)*st/NS), R2=exp(lo0+(hi0-lo0)*(st+1)/NS), dl=log(R2/R1);
    double ctrl=(SEX(R2)-SEX(R1))*pow((double)N,6);     // sum of M^3 over primitive orthant w in (R1,R2]
    double s=0,s2=0; long acc=0; long nst=(long)(nmc*fmin(1.0,sqrt(R1/((double)N*N)))); if(nst<600) nst=600;
    #pragma omp parallel reduction(+:s,s2,acc)
    { rng r; int tid=0;
      #ifdef _OPENMP
      #include <omp.h>
      tid=omp_get_thread_num();
      #endif
      r.s[0]=seed*0x9E3779B97F4A7C15ULL+tid*7919+st*104729+3; r.s[1]=0xBF58476D1CE4E5B9ULL^(seed*31+tid+st); r.s[2]=0x94D049BB133111EBULL+tid*101+st; r.s[3]=0x2545F4914F6CDD1DULL*(tid+11+st);
      for(int i=0;i<20;i++) nxt(&r);
      #pragma omp for schedule(dynamic,200)
      for(long it=0;it<nst;it++){
        ll w1,w2,w3; double R;
        while(1){ double g1=fabs(gauss(&r)),g2=fabs(gauss(&r)),g3=fabs(gauss(&r)); double nn=sqrt(g1*g1+g2*g2+g3*g3);
          double Rt=exp(log(R1)+dl*U(&r));
          w1=llround(g1/nn*Rt); w2=llround(g2/nn*Rt); w3=llround(g3/nn*Rt);
          if(w1<1||w2<1||w3<1) continue;
          R=sqrt((double)w1*w1+(double)w2*w2+(double)w3*w3); if(R<=R1||R>R2) continue;
          if(gcdll(gcdll(w1,w2),w3)!=1) continue; break; }
        ll L; double fv=fval(w1,w2,w3); double Mexp=cbrt(fv)*(double)N*N; double F= (Mexp>30000? planeF_count(N,w1,w2,w3,&L) : planeF(N,w1,w2,w3,&L)); double M3=fv*pow((double)N,6);
        double v=R*R*R*(F-M3); s+=v; s2+=v*v; acc++; } }
    double mean=s/acc, se=sqrt((s2/acc-mean*mean)/acc);
    double fac=(1.0/z3)*(M_PI/2)*dl;     // sum_{w in stratum} g ~ (1/zeta3)(pi/2) dlog E[R^3 g]
    total+=ctrl+fac*mean; var+=fac*fac*se*se;
    fprintf(stderr,"stratum %2d R in [%.3g,%.3g]: ctrl/N^6=%.5f  corr/N^6=%.5f +- %.5f\n",st,R1,R2,ctrl/pow(N,6),fac*mean/pow(N,6),fac*se/pow(N,6));
  }
  double G=3*total/pow((double)N,6), eG=3*sqrt(var)/pow((double)N,6);
  printf("N=%lld W0=%d nmc=%ld : generic/N^6 = %.5f +- %.5f   c_gen(N) = generic/N^6 - C3 log N = %.5f +- %.5f   (exact part/N^6 = %.5f)\n",N,W0,nmc,G,eG,G-C3*log((double)N),eG,3*exactF/pow(N,6));
  return 0; }
