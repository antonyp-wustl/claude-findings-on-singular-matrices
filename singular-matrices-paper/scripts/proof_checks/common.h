#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
static long gcdl(long a, long b){ if(a<0)a=-a; if(b<0)b=-b; while(b){long t=a%b;a=b;b=t;} return a; }
static long egcd(long a, long b, long *x, long *y){
  long old_r=a, r=b, old_s=1, s=0, old_t=0, t=1;
  while(r!=0){ long q=old_r/r, tmp;
    tmp=old_r-q*r; old_r=r; r=tmp;
    tmp=old_s-q*s; old_s=s; s=tmp;
    tmp=old_t-q*t; old_t=t; t=tmp; }
  if(old_r<0){old_r=-old_r; old_s=-old_s; old_t=-old_t;}
  *x=old_s; *y=old_t; return old_r;
}
/* successive minima of w^perp ∩ Z^3 (w primitive), also returns det check */
static void minima(long a, long b, long c, double *mu1, double *mu2, long *v1o, long *v2o){
  long v1[3], v2[3];
  long g = gcdl(a,b);
  if(g==0){ v1[0]=1;v1[1]=0;v1[2]=0; v2[0]=0;v2[1]=1;v2[2]=0; }
  else { long x,y; egcd(a,b,&x,&y);
    v1[0]=b/g; v1[1]=-a/g; v1[2]=0; v2[0]=c*x; v2[1]=c*y; v2[2]=-g; }
  for(;;){
    long n1 = v1[0]*v1[0]+v1[1]*v1[1]+v1[2]*v1[2];
    long n2 = v2[0]*v2[0]+v2[1]*v2[1]+v2[2]*v2[2];
    if(n2<n1){ long t; for(int i=0;i<3;i++){t=v1[i];v1[i]=v2[i];v2[i]=t;} long tn=n1;n1=n2;n2=tn; }
    long d = v1[0]*v2[0]+v1[1]*v2[1]+v1[2]*v2[2];
    if(2*labs(d)<=n1) break;
    long m = llround((double)d/(double)n1);
    for(int i=0;i<3;i++) v2[i]-=m*v1[i];
  }
  *mu1 = sqrt((double)(v1[0]*v1[0]+v1[1]*v1[1]+v1[2]*v1[2]));
  *mu2 = sqrt((double)(v2[0]*v2[0]+v2[1]*v2[1]+v2[2]*v2[2]));
  if(v1o){for(int i=0;i<3;i++){v1o[i]=v1[i];v2o[i]=v2[i];}}
}
static int clip(const double *px, const double *py, int n, double A, double B, double C, double *qx, double *qy){
  int m=0;
  for(int i=0;i<n;i++){
    int j=(i+1)%n;
    double si = A*px[i]+B*py[i]-C, sj = A*px[j]+B*py[j]-C;
    if(si<=0){ qx[m]=px[i]; qy[m]=py[i]; m++; }
    if((si<0 && sj>0) || (si>0 && sj<0)){
      double t = si/(si-sj);
      qx[m]=px[i]+t*(px[j]-px[i]); qy[m]=py[i]+t*(py[j]-py[i]); m++;
    }
  }
  return m;
}
static double areaOmega(double a, double b){
  double px[16]={0,1,1,0}, py[16]={0,0,1,1}, qx[16], qy[16];
  int n=4;
  n = clip(px,py,n, -a,-b,0, qx,qy);
  n = clip(qx,qy,n, a,b,1, px,py);
  double s=0; for(int i=0;i<n;i++){int j=(i+1)%n; s+=px[i]*py[j]-px[j]*py[i];}
  return fabs(s)/2;
}
/* alpha(w/|w|) for integer (or real) w */
static double alpha_w(double w0, double w1, double w2){
  double w[3]={w0,w1,w2}; int k=0;
  for(int i=1;i<3;i++) if(fabs(w[i])>fabs(w[k])) k=i;
  int i=(k+1)%3, j=(k+2)%3;
  double a=-w[i]/w[k], b=-w[j]/w[k];
  double nrm=sqrt(w0*w0+w1*w1+w2*w2);
  return areaOmega(a,b)*nrm/fabs(w[k]);
}
