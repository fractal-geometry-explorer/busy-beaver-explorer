// Hierarchical memoized iteration of the L-event map.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128;
static int W[6][2],D[6][2],NS[6][2];
static string RS, RS2; static bool JUMP=false;
enum {OK=0, EXIT=1, HALT=2, SPECIAL=3};
static long long simsteps=0, simevents=0;
// event on window x (unknown to the left). returns status, x updated in place if OK
int event(string &x){
  static vector<unsigned char> tape; 
  int l=x.size(); int n=l+RS.size()+64;
  tape.assign(n,0);
  for(int i=0;i<l;i++)tape[i]=x[i]-'0';
  for(size_t i=0;i<RS.size();i++)tape[l+i]=RS[i]-'0';
  int pos=l+RS.size(), hi=pos, st=1, arr=0; long long t=0;
  simevents++;
  if(JUMP){ pos=l+RS.size()-12; st=2;
    while(1){
      int r=tape[pos]; int ns=NS[st][r];
      if(ns<0){simsteps+=t; return HALT;}
      tape[pos]=W[st][r]; pos+=D[st][r]; st=ns; t++;
      if(pos<0){simsteps+=t; return EXIT;}
      if(pos>=(int)(l+RS.size())) break;
      if(t>100000000) {fprintf(stderr,"long jump\n"); exit(7);}
    }
    simsteps+=t;
    if(st!=0) return SPECIAL;
  } else {
  while(1){
    int r=tape[pos]; int ns=NS[st][r];
    if(ns<0){simsteps+=t; return HALT;}
    tape[pos]=W[st][r]; pos+=D[st][r]; st=ns; t++;
    if(pos<0){simsteps+=t; return EXIT;}
    if(pos>hi){hi=pos; if(st==1){ if(++arr==3)break; }}
    if(pos>=n-2){simsteps+=t; return SPECIAL;}
  }
  simsteps+=t;
  if(pos!=(int)(l+RS2.size())) return SPECIAL;
  }
  for(size_t i=0;i<RS2.size();i++) if(tape[l+i]!=RS2[i]-'0') return SPECIAL;
  for(int i=0;i<l;i++) x[i]='0'+tape[i];
  return OK;
}
struct Res{ u128 c; string x; int st; };
static vector<unordered_map<string,Res>> memo; static size_t memobytes=0, memocap=0; static long long clears=0;
static int L0;
static long long base_limit=100000000;
Res G(int lev, const string &x0){
  auto it=memo[lev].find(x0); if(it!=memo[lev].end()) return it->second;
  Res R; R.c=0; R.x=x0;
  if(lev==0){
    long long k=0;
    while(1){ string y=R.x; int s=event(y); if(s!=OK){R.st=s;break;} R.x=y; R.c++; if(++k>base_limit){fprintf(stderr,"base loop\n");exit(5);} }
  } else {
    int lb=L0<<(lev-1); int la=x0.size()-lb;
    while(1){
      string b=R.x.substr(la);
      Res r=G(lev-1,b);
      R.c+=r.c; R.x.replace(la,lb,r.x);
      if(r.st!=EXIT){R.st=r.st;break;}
      string y=R.x; int s=event(y);
      if(s!=OK){R.st=s;break;}
      R.x=y; R.c++;
    }
  }
  if(memocap && memobytes>memocap){ for(auto&m:memo){ unordered_map<string,Res>().swap(m);} memobytes=0; clears++; }
  memo[lev][x0]=R; memobytes += 2*x0.size()+96;
  return R;
}
string u2s(u128 v){ if(!v)return "0"; string s; while(v){s+=char('0'+v%10); v/=10;} reverse(s.begin(),s.end()); return s;}
int main(int argc,char**argv){
  const char*M="1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC";
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*g=M+7*s+3*r; if(g[0]=='-'){NS[s][r]=-1;continue;} W[s][r]=g[0]-'0';D[s][r]=g[1]=='R'?1:-1;NS[s][r]=g[2]-'A';}
  bool odd=getenv("ODD")!=nullptr;
  RS = odd? "11101111111010111010111" : "11111010111010111";
  RS2= odd? "11111011111010111010111010111" : "11111010111010111010111";
  if(getenv("JUMP")){ JUMP=true; RS="111111111010111111111010100000010111"; RS2="111111111010111111111010101011101110"; }
  L0 = argc>1?atoi(argv[1]):8;
  if(getenv("MEMCAP")) memocap=(size_t)atoll(getenv("MEMCAP"));
  string L; cin>>L;
  int levels=1; while((L0<<(levels-1)) < (int)L.size()+64) levels++;
  memo.resize(levels);
  int top=L0<<(levels-1);
  string x=string(top-L.size(),'0')+L;
  Res r=G(levels-1,x);
  const char*nm[]={"OK","EXIT","HALT","SPECIAL"};
  printf("status %s after %s standard events; window %d; simevents %lld simsteps %lld\n",nm[r.st],u2s(r.c).c_str(),top,simevents,simsteps);
  size_t tot=0; for(auto&m:memo)tot+=m.size(); printf("memo %zu\n",tot);
  string y=r.x; size_t p=y.find('1'); printf("L %s\n", p==string::npos?"":y.substr(p).c_str());
}
