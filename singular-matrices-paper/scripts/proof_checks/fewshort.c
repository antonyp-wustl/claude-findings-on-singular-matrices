#include "common.h"
/* Lemma fewshort: count primitive w, |w|<=R, mu1(w)<=t. Uses symmetry: mu1 invariant under signed permutations. */
int main(int argc,char**argv){
  int R=atoi(argv[1]);
  int TB=2000; /* bins of t: t in [0, tmax], resolution */
  double tmax = 1.1*pow(4.0/3.0,0.25)*sqrt(R)+2;
  int RB=64; /* radial checkpoints: R_i = R*(i+1)/RB */
  long *H = calloc((size_t)RB*TB, sizeof(long)); /* H[r][tb] counts */
  long R2=(long)R*R;
  for(long c=0;c<=R;c++) for(long b=0;b<=c;b++){ long s2=b*b+c*c; if(s2>R2) break;
    for(long a=0;a<=b;a++){ long n2=s2+a*a; if(n2>R2) break; if(n2==0) continue;
      if(gcdl(gcdl(a,b),c)!=1) continue;
      /* orbit size under signed permutations */
      int nz = (a==0)+(b==0)+(c==0); long signs = 1L<<(3-nz);
      long perms = (a==b && b==c)?1:((a==b||b==c)?3:6);
      long wgt = signs*perms;
      double mu1,mu2; minima(a,b,c,&mu1,&mu2,NULL,NULL);
      double nw = sqrt((double)n2);
      int rb = (int)ceil(nw/R*RB)-1; if(rb<0)rb=0;
      int tb = (int)floor(mu1/tmax*TB); if(tb>=TB) tb=TB-1;
      H[(size_t)rb*TB+tb] += wgt;
    }
  }
  /* cumulative in r and t */
  for(int r=0;r<RB;r++){ for(int tb=1;tb<TB;tb++) H[(size_t)r*TB+tb]+=H[(size_t)r*TB+tb-1];
    if(r>0) for(int tb=0;tb<TB;tb++) H[(size_t)r*TB+tb]+=H[(size_t)(r-1)*TB+tb]; }
  /* report max over checkpoints of count(<=Rr, mu1<= t)/(Rr^2 t^2) for t>=1 (t at bin upper edges) */
  double best=0, bR=0, bt=0;
  int rlist[4]={RB/8-1,RB/4-1,RB/2-1,RB-1};
  for(int r=0;r<RB;r++){ double Rr = (double)R*(r+1)/RB;
    for(int tb=0;tb<TB;tb++){ double t=(tb+1)*tmax/TB; /* upper edge; count is #mu1< t (approx <=) */
      if(t<1) continue; if(t>Rr) break;
      double rat = H[(size_t)r*TB+tb]/(Rr*Rr*t*t); if(rat>best){best=rat;bR=Rr;bt=t;} } }
  printf("R=%d: max_{R'<=R, 1<=t<=R'} count/(R'^2 t^2) = %.4f at R'=%.1f t=%.3f\n",R,best,bR,bt);
  for(int q=0;q<4;q++){ int r=rlist[q]; double Rr=(double)R*(r+1)/RB; printf("  R'=%.0f:",Rr);
    double ts[8]={1.0001,1.5,2,3,5,8,0.5*sqrt(Rr),sqrt(Rr)};
    for(int k=0;k<8;k++){ double t=ts[k]; int tb=(int)floor(t/tmax*TB)-1; if(tb<0)tb=0; if(tb>=TB)tb=TB-1;
      double tt=(tb+1)*tmax/TB; printf(" t=%.2f:%.3f",tt,H[(size_t)r*TB+tb]/(Rr*Rr*tt*tt)); }
    printf("\n"); }
  return 0;
}
