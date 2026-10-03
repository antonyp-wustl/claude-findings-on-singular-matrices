#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dd.h"
static int K, MODE; static int DBG=0;
static double binom[5][5];
static void pmul(const dd*a,int da,const dd*b,int db,dd*c){for(int i=0;i<=da+db;i++)c[i]=ddd(0);for(int i=0;i<=da;i++)for(int j=0;j<=db;j++)c[i+j]=dd_add(c[i+j],dd_mul(a[i],b[j]));}
static int cmpdd(const void*x,const void*y){dd a=*(dd*)x,b=*(dd*)y;return dd_lt(a,b)?-1:(dd_lt(b,a)?1:0);}
static dd pint(const dd*c,int deg,int p,dd lo,dd hi){dd s=ddd(0);for(int m=0;m<=deg;m++){int e=m-p; if(c[m].hi==0&&c[m].lo==0)continue; dd term;
   if(e==-1) term=dd_mul(c[m],dd_log(dd_div(hi,lo))); else term=dd_divd(dd_mul(c[m],dd_sub(dd_powi(hi,e+1),dd_powi(lo,e+1))),(double)(e+1)); s=dd_add(s,term);} return s;}

static dd F_direct(const dd*tS,const int*sg,int ns,int k,dd norm,dd shift,dd s){ // F(shift+s)
  dd x=dd_add(shift,s), acc=ddd(0);
  for(int S=0;S<ns;S++) if(dd_le(tS[S],x)){ dd t=dd_powi(dd_sub(x,tS[S]),k); acc= sg[S]>0?dd_add(acc,t):dd_sub(acc,t);} 
  return dd_mul(acc,norm);
}
static const dd GLX={0.5773502691896257,3.3450280739356345e-17};
static dd f_theta(const dd*th){
  int k=K, ns=1<<k; dd P=ddd(1); for(int i=0;i<k;i++)P=dd_mul(P,th[i]);
  double kf=1; for(int i=2;i<=k;i++)kf*=i;
  dd norm=dd_div(ddd(1),dd_muld(P,kf));
  dd tS[8]; int sg[8];
  for(int S=0;S<ns;S++){dd t=ddd(0);int c=0;for(int i=0;i<k;i++)if(S>>i&1){t=dd_add(t,th[i]);c++;} tS[S]=t; sg[S]=(c&1)?-1:1;}
  int pw=k+1;
  dd shift=(MODE==1)?th[k-1]:ddd(0);
  dd kn[10]; int nk=0; kn[nk++]=ddd(0);
  for(int S=0;S<ns;S++){dd v=dd_sub(tS[S],shift); if(dd_gt0(v)) kn[nk++]=v;}
  qsort(kn,nk,sizeof(dd),cmpdd);
  dd F0=ddd(0);
  if(MODE==1){ for(int S=0;S<ns;S++) if(dd_le(tS[S],shift)){ dd d=dd_sub(shift,tS[S]); dd t=dd_powi(d,k); F0= sg[S]>0?dd_add(F0,t):dd_sub(F0,t);} F0=dd_mul(F0,norm);}
  dd total=ddd(0);
  for(int j=0;j<nk;j++){
    dd lo=kn[j]; int last=(j+1==nk); dd hi= last?ddd(0):kn[j+1];
    if(!last && dd_le(hi,lo)) continue;
    dd c[4]={{0,0},{0,0},{0,0},{0,0}};
    for(int S=0;S<ns;S++) if(dd_le(dd_sub(tS[S],shift),lo)){ dd d=dd_sub(shift,tS[S]);
       for(int m=0;m<=k;m++){ dd t=dd_muld(dd_powi(d,k-m),binom[k][m]); c[m]= sg[S]>0?dd_add(c[m],t):dd_sub(c[m],t);} }
    for(int m=0;m<=k;m++) c[m]=dd_mul(c[m],norm);
    if(MODE==1){ c[0]=dd_sub(c[0],F0); if(j==0) c[0]=ddd(0); }
    if(!last && j>0 && (dd_sub(hi,lo).hi <= 0.25*lo.hi)){ // short relative to position: expand around lo
       dd L=dd_sub(hi,lo), r=dd_div(L,lo);
       dd b[4]={{0,0},{0,0},{0,0},{0,0}};
       for(int S=0;S<ns;S++) if(dd_le(dd_sub(tS[S],shift),lo)){ dd d=dd_sub(dd_add(shift,lo),tS[S]);
          for(int m=0;m<=k;m++){ dd t=dd_muld(dd_powi(d,k-m),binom[k][m]); b[m]= sg[S]>0?dd_add(b[m],t):dd_sub(b[m],t);} }
       for(int m=0;m<=k;m++) b[m]=dd_mul(b[m],norm);
       if(MODE==1) b[0]=dd_sub(b[0],F0);
       dd g1[40],g2[40]; int dg=k; memcpy(g1,b,sizeof(dd)*(k+1));
       for(int t=1;t<pw;t++){pmul(g1,dg,b,k,g2);dg+=k;memcpy(g1,g2,sizeof(dd)*(dg+1));}
       // integral_0^L sum_j g_j sigma^j (lo+sigma)^(-pw) dsigma = lo^(-pw) sum_j g_j L^(j+1) sum_n C(-pw,n) r^n/(j+n+1)
       dd acc=ddd(0); dd Lp=L;
       for(int jj=0;jj<=dg;jj++){ dd inner=ddd(0), cr=ddd(1);
          for(int n=0;n<400;n++){ dd term=dd_divd(cr,(double)(jj+n+1)); inner=dd_add(inner,term);
             if(fabs(term.hi)<1e-36*fabs(inner.hi)) break;
             cr=dd_divd(dd_muld(dd_mul(cr,r),-(double)(pw+n)),(double)(n+1)); }
          acc=dd_add(acc,dd_mul(dd_mul(g1[jj],Lp),inner)); Lp=dd_mul(Lp,L); }
       acc=dd_mul(acc,dd_powi(lo,-pw));
       if(DBG) fprintf(stderr,"  interval %d [%.6g,%.6g] series contrib %.30g\n",j,lo.hi,hi.hi,acc.hi+acc.lo);
       total=dd_add(total,acc); continue; }
    if(last){ dd v=c[0]; total=dd_add(total, dd_divd(dd_mul(dd_powi(v,pw),dd_powi(lo,-k)),(double)k)); continue; }
    dd p1[40],p2[40]; int d1=k; memcpy(p1,c,sizeof(dd)*(k+1));
    for(int t=1;t<pw;t++){pmul(p1,d1,c,k,p2);d1+=k;memcpy(p1,p2,sizeof(dd)*(d1+1));}
    if(j==0){ dd s=ddd(0); for(int m=pw;m<=d1;m++){ int e=m-pw; s=dd_add(s,dd_divd(dd_mul(p1[m],dd_powi(hi,e+1)),(double)(e+1))); } total=dd_add(total,s); }
    else { dd pv=pint(p1,d1,pw,lo,hi); if(DBG) fprintf(stderr,"  interval %d [%.6g,%.6g] poly contrib %.30g\n",j,lo.hi,hi.hi,pv.hi+pv.lo); total=dd_add(total,pv);}
  }
  return total;
}
static dd *X,*W; static int NN;
int main(int argc,char**argv){
  K=atoi(argv[1]); MODE=atoi(argv[2]); const char*nodefile=argv[3];
  for(int n=0;n<5;n++)for(int r=0;r<=n;r++){double b=1;for(int i=0;i<r;i++)b=b*(n-i)/(i+1);binom[n][r]=b;}
  if(strcmp(nodefile,"eval")==0){ DBG=1; dd th[3]; for(int i=0;i<K;i++){ th[i].hi=atof(argv[4+2*i]); th[i].lo=atof(argv[5+2*i]); }
     dd v=f_theta(th); printf("%.40g %.40g\n",v.hi,v.lo); return 0; }
  FILE*f=fopen(nodefile,"r"); int n; fscanf(f,"%d",&n); X=malloc(sizeof(dd)*n);W=malloc(sizeof(dd)*n);
  for(int i=0;i<n;i++) fscanf(f,"%lf %lf %lf %lf",&X[i].hi,&X[i].lo,&W[i].hi,&W[i].lo); fclose(f); NN=n;
  dd total=ddd(0);
  if(K==2){ double cuts[3]={0,0.5,1};
    for(int c=0;c<2;c++){ dd a=ddd(cuts[c]), len=ddd(cuts[c+1]-cuts[c]);
      for(int i=0;i<NN;i++){ dd t1=dd_add(a,dd_mul(len,X[i])); dd th[2]={t1,dd_sub(ddd(1),t1)}; total=dd_add(total,dd_mul(dd_mul(W[i],len),f_theta(th))); } }
  } else {
    double G[2]={1.0/3,1.0/3}; // centroid (exact enough? use dd below)
    dd Gd[2]; Gd[0]=dd_div(ddd(1),ddd(3)); Gd[1]=Gd[0];
    dd V[3][2]={{{1,0},{0,0}},{{0,0},{1,0}},{{0,0},{0,0}}};
    dd M[3][2]={{{0,0},{0.5,0}},{{0.5,0},{0,0}},{{0.5,0},{0.5,0}}};
    dd Q[3][2]; for(int i=0;i<3;i++){int j=(i+1)%3,k2=(i+2)%3; for(int d=0;d<2;d++) Q[i][d]=dd_muld(dd_add(M[j][d],M[k2][d]),0.5);}
    dd cells[12][3][2]; int nc=0;
    for(int i=0;i<3;i++) for(int t=1;t<=2;t++){ int j=(i+t)%3;
       dd *pt1[3]={Gd,M[j],Q[i]}; dd *pt2[3]={V[i],M[j],Q[i]};
       for(int q=0;q<3;q++)for(int d=0;d<2;d++){cells[nc][q][d]=pt1[q][d];} nc++;
       for(int q=0;q<3;q++)for(int d=0;d<2;d++){cells[nc][q][d]=pt2[q][d];} nc++; }
    dd area=ddd(0);
    for(int c=0;c<nc;c++){
      dd *A=cells[c][0],*B=cells[c][1],*C=cells[c][2];
      dd e1x=dd_sub(B[0],A[0]),e1y=dd_sub(B[1],A[1]),e2x=dd_sub(C[0],B[0]),e2y=dd_sub(C[1],B[1]);
      dd det=dd_abs(dd_sub(dd_mul(e1x,e2y),dd_mul(e1y,e2x)));
      dd *acc=malloc(sizeof(dd)*NN), *ar=malloc(sizeof(dd)*NN);
      #pragma omp parallel for schedule(dynamic)
      for(int i=0;i<NN;i++){ dd u=X[i]; dd s=ddd(0), sa=ddd(0);
        for(int jj=0;jj<NN;jj++){ dd v=X[jj]; dd uv=dd_mul(u,v);
          dd x=dd_add(A[0],dd_add(dd_mul(u,e1x),dd_mul(uv,e2x))); dd y=dd_add(A[1],dd_add(dd_mul(u,e1y),dd_mul(uv,e2y)));
          dd z=dd_sub(dd_sub(ddd(1),x),y); if(!dd_gt0(x)||!dd_gt0(y)||!dd_gt0(z)) continue;
          dd th[3]={x,y,z}; dd wt=dd_mul(dd_mul(dd_mul(W[i],W[jj]),u),det);
          { double a0=x.hi,a1=y.hi,a2=z.hi, mn=fmin(a0,fmin(a1,a2)), mx=fmax(a0,fmax(a1,a2)), md=a0+a1+a2-mn-mx;
            if(mn<1e-30 || mn*md<1e-36) { sa=dd_add(sa,wt); continue; } }
          dd fv=f_theta(th); if(isnan(fv.hi)||isinf(fv.hi)||fabs(fv.hi)>50){ static int cnt=0; if(cnt++<5) fprintf(stderr,"bad f at %.3e %.3e %.3e wt %.3e\n",th[0].hi,th[1].hi,th[2].hi,wt.hi); fv=ddd(0);} s=dd_add(s,dd_mul(wt,fv)); sa=dd_add(sa,wt);} acc[i]=s; ar[i]=sa; }
      for(int i=0;i<NN;i++){ total=dd_add(total,acc[i]); area=dd_add(area,ar[i]); }
      free(acc); free(ar); }
    fprintf(stderr,"area-0.5 = %.3e\n", dd_sub(area,ddd(0.5)).hi);
  }
  printf("K=%d MODE=%d nodes=%d : %.40g %.40g\n",K,MODE,NN,total.hi,total.lo); return 0;
}
