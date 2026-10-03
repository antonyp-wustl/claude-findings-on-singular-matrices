// K0_gen(X) = 6 * sum_{w=(a,b,-c) primitive, a,b,c>=1, |w|<=X} f(w) - C3 log X,
// f = (area{ax+by<=c in [0,1]^2})^3 / c^3 = n^3/(8 a^3 b^3 c^3), n = c^2-(c-a)_+^2-(c-b)_+^2+(c-a-b)_+^2
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc,char**argv){
  int X=atoi(argv[1]); long X2=(long)X*X;
  double *bin=calloc(X2+1,sizeof(double));
  #pragma omp parallel
  { double *loc=calloc(X2+1,sizeof(double));
    #pragma omp for schedule(dynamic)
    for(int c=1;c<=X;c++){
      for(int a=1;(long)a*a+(long)c*c<=X2;a++){
        for(int b=1;(long)a*a+(long)b*b+(long)c*c<=X2;b++){
          long t1=c-a>0?(long)(c-a)*(c-a):0, t2=c-b>0?(long)(c-b)*(c-b):0, t3=c-a-b>0?(long)(c-a-b)*(c-a-b):0;
          double n=(double)((long)c*c-t1-t2+t3);
          double ar=n/(2.0*a*b), f=ar*ar*ar/((double)c*c*c);
          loc[(long)a*a+(long)b*b+(long)c*c]+=f;
        } } }
    #pragma omp critical
    for(long i=0;i<=X2;i++) bin[i]+=loc[i];
    free(loc); }
  for(long i=1;i<=X2;i++) bin[i]+=bin[i-1];   // cumulative
  // mobius
  int *mu=malloc(sizeof(int)*(X+1)); char *comp=calloc(X+1,1);
  for(int i=0;i<=X;i++) mu[i]=1;
  for(int p=2;p<=X;p++) if(!comp[p]){ for(int k=2*p;k<=X;k+=p) comp[k]=1; for(int k=p;k<=X;k+=p) mu[k]=-mu[k]; for(long k=(long)p*p;k<=X;k+=(long)p*p) mu[k]=0; }
  double C3=15*(12-M_PI*M_PI)/(4*1.2020569031595942854);
  // report K0 estimate for several X' <= X
  int Xs[]={X/8,X/4,X/2,X};
  for(int t=0;t<4;t++){ int Y=Xs[t]; double s=0;
    for(int d=1;d<=Y;d++) if(mu[d]){ long r2=(long)floor(((double)Y/d)*((double)Y/d)+1e-9); s+=mu[d]/((double)d*d*d)*bin[r2]; }
    printf("X=%d  K0_gen estimate = %.10f\n",Y,6*s-C3*log((double)Y)); }
  return 0; }
