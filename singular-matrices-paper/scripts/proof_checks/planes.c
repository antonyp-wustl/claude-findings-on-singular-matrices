#include "common.h"
/* Enumerate all admissible planes for given N via pairs of box points.
   For each, compute L_P, #(Lambda_w ∩ K_w) (cnt0), par_P, mu1, mu2, M_w. Print stats. */
#define OFF (1L<<20)
static uint64_t *tab; static uint64_t tabmask;
static uint64_t pack(long a,long b,long c){ return ((uint64_t)(a+OFF)<<42)|((uint64_t)(b+OFF)<<21)|(uint64_t)(c+OFF); }
static void unpack(uint64_t k,long*a,long*b,long*c){ *c=(long)(k&((1UL<<21)-1))-OFF; *b=(long)((k>>21)&((1UL<<21)-1))-OFF; *a=(long)(k>>42)-OFF; }
static long nplanes=0;
static void insert(uint64_t k){ uint64_t h=(k*0x9E3779B97F4A7C15ULL)>>20; h&=tabmask;
  while(tab[h]){ if(tab[h]==k) return; h=(h+1)&tabmask; } tab[h]=k; nplanes++; }
int main(int argc,char**argv){
  int N=atoi(argv[1]); int logsz=atoi(argv[2]); int dump = argc>3 ? atoi(argv[3]) : 0;
  tabmask=(1UL<<logsz)-1; tab=calloc(1UL<<logsz,8);
  int NP=N*N*N; int *X=malloc(NP*4),*Y=malloc(NP*4),*Z=malloc(NP*4);
  long *kN=malloc(sizeof(long)*NP);
  int p=0; long A=0;
  for(int x=1;x<=N;x++)for(int y=1;y<=N;y++)for(int z=1;z<=N;z++){ X[p]=x;Y[p]=y;Z[p]=z;
    long g=gcdl(gcdl(x,y),z); long mx=x; if(y>mx)mx=y; if(z>mx)mx=z; kN[p]=N/(mx/g); A+=kN[p]; p++; }
  for(int i=0;i<NP;i++) for(int j=i+1;j<NP;j++){
    long a=(long)Y[i]*Z[j]-(long)Z[i]*Y[j], b=(long)Z[i]*X[j]-(long)X[i]*Z[j], c=(long)X[i]*Y[j]-(long)Y[i]*X[j];
    if(a==0&&b==0&&c==0) continue;
    long g=gcdl(gcdl(a,b),c); a/=g;b/=g;c/=g;
    if(a<0||(a==0&&b<0)||(a==0&&b==0&&c<0)){a=-a;b=-b;c=-c;}
    insert(pack(a,b,c));
  }
  double N2=(double)N*N, N6=pow(N,6), sq3=sqrt(3.0);
  double sumL3=0,sumM3=0,sumLpar=0,sumLI=0,sumE1=0,sumE3=0,sumdiff=0,sumabsdiff=0,sumM2E=0,sumE3act=0;
  double maxw=0, minmu1ratio=1e9, maxEratio=0, maxEratio1=0, maxcnt0ratio=0, maxparratio=0, maxmu2=0, maxmu1hermite=0, maxEoverM=0;
  long arg_maxE[3]={0,0,0};
  FILE *fd = dump? fopen("planes_dump.txt","w"):NULL;
  for(uint64_t h=0;h<=tabmask;h++){ if(!tab[h]) continue;
    long a,b,c; unpack(tab[h],&a,&b,&c); long w[3]={a,b,c};
    int k=0; for(int i=1;i<3;i++) if(labs(w[i])>labs(w[k])) k=i;
    int ii=(k+1)%3, jj=(k+2)%3;
    long L=0,cnt0=0; long par=0;
    for(long u=0;u<=N;u++) for(long v=0;v<=N;v++){
      long s=-(w[ii]*u+w[jj]*v); if(s%w[k]) continue; long t=s/w[k]; if(t<0||t>N) continue;
      cnt0++;
      if(u>=1&&v>=1&&t>=1){ L++; long r[3]; r[ii]=u; r[jj]=v; r[k]=t;
        par += kN[(r[0]-1)*N*N+(r[1]-1)*N+(r[2]-1)]; }
    }
    double nw=sqrt((double)(a*a+b*b+c*c));
    double mu1,mu2; minima(a,b,c,&mu1,&mu2,NULL,NULL);
    double M = N2*areaOmega(-(double)w[ii]/w[k], -(double)w[jj]/w[k])/fabs((double)w[k]);
    double E = L - M;
    sumL3 += (double)L*L*L; sumM3 += M*M*M; sumLpar += (double)L*par; sumLI += (double)L*((double)L*L-par);
    sumE1 += pow(N,5)/(nw*nw*mu1); sumE3 += pow(N,3)/(mu1*mu1*mu1);
    sumdiff += (double)L*L*L - M*M*M; sumabsdiff += fabs((double)L*L*L - M*M*M);
    sumM2E += M*M*fabs(E); sumE3act += fabs(E*E*E);
    if(nw/N2>maxw) maxw=nw/N2;
    double r1 = mu1*sq3*N/nw; if(r1<minmu1ratio) minmu1ratio=r1;
    double er = fabs(E)*mu1/N; if(er>maxEratio){maxEratio=er; arg_maxE[0]=a;arg_maxE[1]=b;arg_maxE[2]=c;}
    double er1 = fabs(E)/(N/mu1+1); if(er1>maxEratio1) maxEratio1=er1;
    double cr = fabs(cnt0 - M)/(sq3*N/mu1+1); if(cr>maxcnt0ratio) maxcnt0ratio=cr;
    double pr = par*mu1/((double)L*sq3*N); if(pr>maxparratio) maxparratio=pr;
    if(mu2/(sq3*N)>maxmu2) maxmu2=mu2/(sq3*N);
    double hr = mu1/pow(4.0/3.0,0.25)/sqrt(nw); if(hr>maxmu1hermite) maxmu1hermite=hr;
    if(fd) fprintf(fd,"%ld %ld %ld %ld %ld %ld %.6f %.6f %.6f\n",a,b,c,L,cnt0,par,M,mu1,mu2);
  }
  if(fd) fclose(fd);
  /* S3 check */
  double S3 = (double)N*N*N*(double)A + sumLI;
  printf("N=%d planes=%ld A=%ld S3=%.0f\n",N,nplanes,A,S3);
  printf(" max|w|/N^2=%.4f (<=3)  min mu1*sqrt3N/|w|=%.4f (>=1)  max mu2/(sqrt3N)=%.4f (<=1) max mu1/((4/3)^.25|w|^.5)=%.4f (<=1)\n",maxw,minmu1ratio,maxmu2,maxmu1hermite);
  printf(" max |E|mu1/N=%.4f at w=(%ld,%ld,%ld); max |E|/(N/mu1+1)=%.4f; max |cnt0-M|/(sqrt3N/mu1+1)=%.4f; max par*mu1/(L sqrt3 N)=%.4f (<=1)\n",maxEratio,arg_maxE[0],arg_maxE[1],arg_maxE[2],maxEratio1,maxcnt0ratio,maxparratio);
  printf(" /N^6: sumL3=%.4f sumM3_adm=%.4f sumLpar=%.4f sum(L3-M3)=%.4f sum|L3-M3|=%.4f sumM2|E|=%.4f sum|E|^3=%.4f  sumN5/(|w|^2mu1)=%.4f sumN3/mu1^3=%.4f\n",
     sumL3/N6,sumM3/N6,sumLpar/N6,sumdiff/N6,sumabsdiff/N6,sumM2E/N6,sumE3act/N6,sumE1/N6,sumE3/N6);
  return 0;
}
