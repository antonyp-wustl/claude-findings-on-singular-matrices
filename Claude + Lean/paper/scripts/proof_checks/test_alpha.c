#include "common.h"
int main(){
  printf("alpha(e3)=%.6f (1)\n", alpha_w(0,0,1));
  printf("alpha(1,1,-1)=%.6f (%.6f)\n", alpha_w(1,1,-1), sqrt(3)/2);
  printf("alpha(1,-1,0)=%.6f (%.6f)\n", alpha_w(1,-1,0), sqrt(2));
  printf("alpha(1,1,1)=%.6f (0)\n", alpha_w(1,1,1));
  printf("alpha(1,1,0)=%.6f (0)\n", alpha_w(1,1,0));
  /* J via quadrature in spherical coords: integrate alpha^3 over sphere */
  int n=4000; double J=0;
  for(int it=0;it<n;it++){ double th=M_PI*(it+0.5)/n; double st=sin(th), ct=cos(th);
    for(int ip=0;ip<2*n;ip++){ double ph=M_PI*(ip+0.5)/n;
      double al=alpha_w(st*cos(ph), st*sin(ph), ct); J+=al*al*al*st; } }
  J*= (M_PI/n)*(M_PI/n);
  printf("J quad = %.6f ; claimed 45-15pi^2/4 = %.6f\n", J, 45-15*M_PI*M_PI/4);
  return 0;
}
