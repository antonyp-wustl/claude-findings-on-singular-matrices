#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static ll fdiv(ll a, ll b){ ll q=a/b; if((a%b!=0)&&((a<0)!=(b<0))) q--; return q; }
static ll cdiv(ll a, ll b){ return -fdiv(-a,b); }
static ll gcdl(ll a, ll b){ if(a<0)a=-a; if(b<0)b=-b; while(b){ll t=a%b;a=b;b=t;} return a; }
static ll inv(ll a, ll m){ /* a mod m inverse, gcd=1 */ ll g=m, x=0, x1=1, aa=((a%m)+m)%m; ll b=aa;
  ll old_r=b, r=m, old_s=1, s=0; while(r){ ll q=old_r/r, t=old_r-q*r; old_r=r; r=t; t=old_s-q*s; old_s=s; s=t; }
  return ((old_s%m)+m)%m; }
int N;
/* count (x,y,z) in [1,N]^3 with p x + q y + r z = 0 */
static ll L(ll p, ll q, ll r){
  if(r==0){ if(q!=0){ ll t=q; q=r; r=t; } else if(p!=0){ ll t=p; p=r; r=t; } else return (ll)N*N*N; }
  /* now r != 0 */
  if(q==0){ /* p x + r z = 0, y free */
    ll cnt=0; for(ll x=1;x<=N;x++){ ll n=-p*x; if(n%r==0){ ll z=n/r; if(z>=1&&z<=N) cnt++; } } return cnt*N; }
  ll g=gcdl(q,r); ll qp=q/g, rp=r/g;
  if(rp<0){ qp=-qp; rp=-rp; g=-g; } /* now equation: qp y + rp z = n/g with g possibly negative */
  ll m=rp, iq = (m==1)?0:inv(qp,m);
  ll cnt=0;
  for(ll x=1;x<=N;x++){
    ll n=-p*x; if(n%g!=0) continue; ll np=n/g;
    ll lo,hi; ll A=np-(ll)N*rp, B=np-rp;  /* qp*y in [A,B] */
    if(qp>0){ lo=cdiv(A,qp); hi=fdiv(B,qp);} else { lo=cdiv(B,qp); hi=fdiv(A,qp);} 
    if(lo<1)lo=1; if(hi>N)hi=N; if(lo>hi) continue;
    if(m==1){ cnt+=hi-lo+1; continue; }
    ll y0=((np%m+m)%m)*iq%m;
    cnt+= fdiv(hi-y0,m)-fdiv(lo-1-y0,m);
  }
  return cnt;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); int M=N*N*N; int *P=malloc(sizeof(int)*3*M); int k=0;
  for(int a=1;a<=N;a++)for(int b=1;b<=N;b++)for(int c=1;c<=N;c++){P[3*k]=a;P[3*k+1]=b;P[3*k+2]=c;k++;}
  ll total=0;
  #pragma omp parallel for schedule(dynamic,16) reduction(+:total)
  for(int i=0;i<M;i++){
    ll x1=P[3*i],y1=P[3*i+1],z1=P[3*i+2]; ll s=0;
    for(int j=i+1;j<M;j++){
      ll x2=P[3*j],y2=P[3*j+1],z2=P[3*j+2];
      ll p=y1*z2-z1*y2, q=z1*x2-x1*z2, r=x1*y2-y1*x2;
      ll gg=gcdl(gcdl(p,q),r); if(gg>1){p/=gg;q/=gg;r/=gg;}
      s+=L(p,q,r);
    }
    total+=2*s+(ll)N*N*N;
  }
  printf("%d %lld\n",N,total); return 0;
}
