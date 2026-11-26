// A_X: arrival carries at boundary b (cell b-1 = 0) for passes that, after their last visit to >= b+X, move left to b.
#include <bits/stdc++.h>
using namespace std;
int W[6][2]={{1,1},{1,1},{1,0},{9,1},{1,0},{0,1}};
int Mv[6][2]={{1,1},{1,-1},{-1,-1},{0,-1},{1,-1},{1,1}};
int Q[6][2]={{1,5},{2,2},{3,4},{9,4},{5,1},{0,4}};
int main(int argc,char**argv){ int X=atoi(argv[1]); int KEEP=atoi(argv[2]);
 set<pair<int,string>> A; long sims=0, pruned=0, loops=0, halts=0;
 // enumerate words u[0..X-1], u[0]=1, no 00
 vector<int> u(X); 
 function<void(int)> rec=[&](int i){
  if(i==X){
   int moves[5][3]={{1,1,1},{2,0,1},{2,1,0},{3,1,1},{4,1,0}}; // (s,r,write) left moves at cell X
   int nst[5]={2,3,4,4,1};
   for(int k=0;k<5;k++){
    if(moves[k][0]==2 && moves[k][1]==0 && u[X-1]==0) continue;
    vector<int> t(u.begin(),u.end()); t.push_back(moves[k][2]);
    int p=X-1, q=nst[k]; sims++; bool done=false;
    for(int n=0;n<100000;n++){
     if(p==0){ string w; for(int j=0;j<KEEP && j<=X;j++) w.push_back('0'+t[j]); A.insert({q,w}); done=true; break; }
     if(p==X+1 || p>X){ pruned++; done=true; break; }
     if(p==X){ /* head back at b+X: violates last-visit assumption */ pruned++; done=true; break; }
     int a=t[p]; if(q==3&&a==0){ halts++; done=true; break; }
     t[p]=W[q][a]; p+=Mv[q][a]; q=Q[q][a];
    }
    if(!done) loops++;
   }
   return; }
  for(int v=0;v<2;v++){ if(i==0 && v==0) continue; if(i>0 && v==0 && u[i-1]==0) continue; u[i]=v; rec(i+1); }
 };
 rec(0);
 printf("X=%d KEEP=%d sims %ld pruned %ld loops %ld halts %ld arrivals %zu\n",X,KEEP,sims,pruned,loops,halts,A.size());
 FILE*o=fopen(("arr_"+to_string(X)+"_"+to_string(KEEP)+".txt").c_str(),"w"); for(auto&a:A) fprintf(o,"%d %s\n",a.first,a.second.c_str()); fclose(o);
}
