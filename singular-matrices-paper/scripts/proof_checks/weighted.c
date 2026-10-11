#include "common.h"
/* S(X) = sum_{w primitive, |w|<=X} alpha(w^)^3/|w|^3 at checkpoints; uses permutation symmetry */
int main(int argc,char**argv){
  int X=atoi(argv[1]);
  int nck = argc-2; double ck[64]; for(int i=0;i<nck;i++) ck[i]=atof(argv[i+2]);
  /* bin by |w| with fine radial bins of width 1/8 for cumulative sum */
  int NB = 8*X+8; double *B=calloc(NB,sizeof(double)); double *Bcone=calloc(NB,sizeof(double));
  long X2=(long)X*X;
  for(long a=1;a<=X;a++) for(long c=-1;c>=-X;c--){ long s2=a*a+c*c; if(s2>X2) break;
    for(long b=c;b<=a;b++){ long n2=s2+b*b; if(n2>X2) continue;
      if(gcdl(gcdl(a,b),c)!=1) continue;
      int perms = (a==b||b==c)?3:6;
      double al = alpha_w((double)a,(double)b,(double)c);
      double nw=sqrt((double)n2);
      double v = perms*al*al*al/(nw*nw*nw);
      int bin=(int)(nw*8); B[bin]+=v;
    } }
  B[8] += 6.0; /* ±e_i, |w|=1, alpha=1 */
  double z3=1.2020569031595942, J=45-15*M_PI*M_PI/4, C=J/z3;
  double cum=0; int ci=0;
  /* cumulative: S(x) for x at bin edges */
  for(int i=0;i<NB;i++){ cum+=B[i]; double x=(i+1)/8.0;
    while(ci<nck && ck[ci] < x+1e-9 && ck[ci] >= x-0.125+1e-9){ printf("X=%8.1f S(X)=%.6f S-C*logX=%.6f\n",ck[ci],cum,cum-C*log(ck[ci])); ci++; } }
  return 0;
}
