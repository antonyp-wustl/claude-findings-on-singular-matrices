// S_3(N) for all N <= NMAX in one pass.
// S_3(N) = sum over lines l (primitive v in [1,N]^3) of k(2kN^3 - k^2 + Q_l(N)),
//   k = floor(N/max v), Q_l(N) = sum over planes P through l of m_P(N)^2,
//   m_P(N) = # points of [1,N]^3 in P off l.  Points are processed in shells of increasing max entry.
// Lines are taken up to coordinate permutation (v1<=v2<=v3) with orbit weights.
// Work split: line index range [i0,i1) given on command line, partial sums written to a file.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#define NBIN 24
#define LMIN (log(1e-5))
#define LMAX (log(4.0))
typedef long long ll; typedef unsigned long long ull;
static int NMAX;
static inline int gcd(int a,int b){ if(a<0)a=-a; if(b<0)b=-b; if(!a) return b; if(!b) return a;
  int sh=__builtin_ctz(a|b); a>>=__builtin_ctz(a);
  do{ b>>=__builtin_ctz(b); if(a>b){int t=a;a=b;b=t;} b-=a; }while(b); return a<<sh; }
typedef struct { unsigned key; unsigned short cnt; unsigned short stamp; } slot;
int main(int argc,char**argv){
  NMAX=atoi(argv[1]); long i0=atol(argv[2]), i1=atol(argv[3]); const char*outf=argv[4];
  int N=NMAX; long np=(long)N*N*N;
  // points sorted by max entry
  int *P=malloc(sizeof(int)*3*np); int *shellEnd=malloc(sizeof(int)*(N+2)); long idx=0;
  for(int n=1;n<=N;n++){
    for(int x=1;x<=n;x++)for(int y=1;y<=n;y++)for(int z=1;z<=n;z++){ if(x<n&&y<n&&z<n) continue; P[3*idx]=x;P[3*idx+1]=y;P[3*idx+2]=z; idx++; }
    shellEnd[n]=idx; }
  // canonical lines
  long nl=0; int *L=malloc(sizeof(int)*4*(long)N*N*N/2+16);
  for(int c=1;c<=N;c++)for(int b=1;b<=c;b++)for(int a=1;a<=b;a++){
    if(gcd(gcd(a,b),c)!=1) continue;
    int w=(a<b&&b<c)?6:((a==b&&b==c)?1:3);
    L[4*nl]=a;L[4*nl+1]=b;L[4*nl+2]=c;L[4*nl+3]=w; nl++; }
  if(i1>nl) i1=nl;
  // accumulators per N (use __int128 for safety)
  __int128 *S=calloc(N+1,sizeof(__int128)); double BIN[NBIN]={0};
  int HB=1; while((1L<<HB) < 2*np) HB++; long HS=1L<<HB; ull HM=HS-1;
  #pragma omp parallel
  {
    slot *T=calloc(HS,sizeof(slot)); unsigned short stamp=0;
    __int128 *Sl=calloc(N+1,sizeof(__int128));
    ll *Qn=malloc(sizeof(ll)*(N+1)); long *used=malloc(sizeof(long)*np); double *Bl=calloc(NBIN,sizeof(double));
    #pragma omp for schedule(dynamic,1)
    for(long li=i0;li<i1;li++){
      int v1=L[4*li],v2=L[4*li+1],v3=L[4*li+2],wt=L[4*li+3];
      int vmax=v3; stamp++; if(stamp==0){ memset(T,0,HS*sizeof(slot)); stamp=1; }
      ll Q=0; long nused=0;
      // m2=(0,v3,-v2), m3=(-v3,0,v1)
      for(int n=1;n<=N;n++){
        long s0=(n==1)?0:shellEnd[n-1], s1=shellEnd[n];
        for(long t=s0;t<s1;t++){
          int x=P[3*t],y=P[3*t+1],z=P[3*t+2];
          int p=v3*y-v2*z, q=v1*z-v3*x;
          if(p==0&&q==0) continue;           // on the line
          int g=gcd(p,q); p/=g; q/=g;
          if(p<0||(p==0&&q<0)){p=-p;q=-q;}
          unsigned key=((unsigned)(p+32768)<<16)|(unsigned)(q+32768);
          ull h=((ull)key*0x9E3779B97F4A7C15ULL)>>(64-HB);
          while(1){ slot*s=&T[h];
            if(s->stamp!=stamp){ s->stamp=stamp; s->key=key; s->cnt=1; Q+=1; used[nused++]=h; break; }
            if(s->key==key){ Q+=2*(ll)s->cnt+1; s->cnt++; break; }
            h=(h+1)&HM; }
        }
        Qn[n]=Q;
      }
      for(int n=vmax;n<=N;n++){ ll k=n/vmax; ll N3=(ll)n*n*n;
        Sl[n]+=(__int128)wt*k*(2*k*N3-k*k+Qn[n]); }
      { ll k=N/vmax;
        for(long t=0;t<nused;t++){ slot*s=&T[used[t]]; int p=(int)(s->key>>16)-32768, q=(int)(s->key&0xffff)-32768; ll m=s->cnt;
          // normal w ∝ (p, q, -(p v1 + q v2)/v3) ; scale by v3 and make primitive
          ll w1=(ll)p*v3, w2=(ll)q*v3, w3=-((ll)p*v1+(ll)q*v2);
          ll g=gcd(gcd((int)llabs(w1),(int)llabs(w2)),(int)llabs(w3)); w1/=g; w2/=g; w3/=g;
          if(w1==0||w2==0||w3==0) continue;           // axis plane: excluded (generic only)
          double lam=sqrt((double)(w1*w1+w2*w2+w3*w3))/((double)N*N);
          int bi=(int)floor((log(lam)-LMIN)/(LMAX-LMIN)*NBIN); if(bi<0) bi=0; if(bi>=NBIN) bi=NBIN-1;
          Bl[bi]+=(double)wt*k*m*(m+k); } }
    }
    #pragma omp critical
    { for(int n=0;n<=N;n++) S[n]+=Sl[n]; for(int i=0;i<NBIN;i++) BIN[i]+=Bl[i]; }
    free(T); free(Sl); free(Qn);
  }
  FILE*f=fopen(outf,"w");
  fprintf(f,"%ld %ld %ld\n",i0,i1,nl);
  for(int n=1;n<=N;n++){ __int128 v=S[n]; char buf[64]; int p=63; buf[p]=0; int neg=v<0; if(neg)v=-v; do{buf[--p]='0'+(int)(v%10); v/=10;}while(v); if(neg)buf[--p]='-'; fprintf(f,"%d %s\n",n,buf+p); }
  for(int i=0;i<NBIN;i++) fprintf(f,"BIN %d %.6e %.6e %.10e\n",i,exp(LMIN+(LMAX-LMIN)*i/NBIN),exp(LMIN+(LMAX-LMIN)*(i+1)/NBIN),BIN[i]/pow((double)N,6)); fclose(f);
  printf("lines total %ld, processed [%ld,%ld)\n",nl,i0,i1); return 0;
}
