#include "common.h"
/* Lemma regular: sample pairs u,v with small |u-v|, compute |alpha(u)-alpha(v)| * delta / |u-v|,
   delta = min distance from E along the segment (approx by endpoints minus |u-v|). Report max. */
static double rnd(){ return (rand()+0.5)/((double)RAND_MAX+1); }
static double distE(const double*u){ double m=1e9; for(int i=0;i<3;i++){ double d2p=0,d2m=0;
  for(int j=0;j<3;j++){ double e=(i==j); d2p+=(u[j]-e)*(u[j]-e); d2m+=(u[j]+e)*(u[j]+e);} 
  if(sqrt(d2p)<m)m=sqrt(d2p); if(sqrt(d2m)<m)m=sqrt(d2m);} return m; }
int main(){
  srand(12345); double best=0, bestd=0; double bu[3],bv[3];
  double worst_by_scale[8]={0}; 
  for(long it=0;it<20000000;it++){
    double u[3],v[3];
    /* choose u: half uniform on sphere, half concentrated near e3 at scale 10^-k */
    if(it%2==0){ double z=2*rnd()-1, ph=2*M_PI*rnd(), r=sqrt(1-z*z); u[0]=r*cos(ph);u[1]=r*sin(ph);u[2]=z; }
    else { int k=1+rand()%6; double eps=pow(10.0,-k)*rnd(); double ph=2*M_PI*rnd(); u[0]=eps*cos(ph);u[1]=eps*sin(ph);u[2]=1; 
      double n=sqrt(u[0]*u[0]+u[1]*u[1]+1); for(int i=0;i<3;i++)u[i]/=n; }
    double h = pow(10.0,-1-6*rnd()) ; double dir[3]={2*rnd()-1,2*rnd()-1,2*rnd()-1};
    for(int i=0;i<3;i++) v[i]=u[i]+h*dir[i]; double n=sqrt(v[0]*v[0]+v[1]*v[1]+v[2]*v[2]); for(int i=0;i<3;i++)v[i]/=n;
    double duv=sqrt((u[0]-v[0])*(u[0]-v[0])+(u[1]-v[1])*(u[1]-v[1])+(u[2]-v[2])*(u[2]-v[2]));
    double delta = fmin(distE(u),distE(v)) - duv; if(delta<=0) continue;
    double r = fabs(alpha_w(u[0],u[1],u[2])-alpha_w(v[0],v[1],v[2]))*delta/duv;
    if(r>best){best=r;bestd=delta;for(int i=0;i<3;i++){bu[i]=u[i];bv[i]=v[i];}}
  }
  printf("max |alpha(u)-alpha(v)|*delta/|u-v| = %.4f (delta=%.3g) at u=(%.4g,%.4g,%.4g)\n",best,bestd,bu[0],bu[1],bu[2]);
  /* also: sup of alpha */
  double amax=0; for(long it=0;it<2000000;it++){ double z=2*rnd()-1, ph=2*M_PI*rnd(), r=sqrt(1-z*z); double a=alpha_w(r*cos(ph),r*sin(ph),z); if(a>amax)amax=a; }
  printf("max alpha sampled = %.4f (sqrt2=%.4f, bound 3pi)\n",amax,sqrt(2));
  return 0;
}
