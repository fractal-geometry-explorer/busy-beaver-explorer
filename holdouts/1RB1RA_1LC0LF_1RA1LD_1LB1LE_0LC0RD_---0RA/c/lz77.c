// 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA: the LZ77 size of a word of the run (a lower bound for any grammar).
//
// Reads a word in the format of `wrun wordat V` (runs "a3 b1 c2 ...", a = cbb) on stdin, expands it to tokens b, c
// and prints its number of tokens n and z, the number of phrases of its greedy LZ77 parsing with self-reference
// (each phrase is the longest prefix of the rest that also starts at an earlier position, or one new letter).
// z is a lower bound for the size of every straight-line program (context-free grammar with one word as its
// language) for the word (Rytter 2003, Charikar et al. 2005): every description of the word by hash-consed shared
// pieces, as Hashlife or a rope with memoised sub-words would keep, has at least z pieces.
//
// Method: suffix array by prefix doubling with radix sort, then for each phrase start i the previous and next
// smaller suffix-array values around the rank of i (Kasai-Kaerkkaeinen-Puglisi), compared letter by letter.
//
// usage:  wrun wordat V | lz77
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long L;
static char *s; static L n;
static void die(const char *m){ fprintf(stderr,"%s\n",m); exit(1); }
int main(void){
  L cap=1<<20; s=malloc(cap); n=0; int ch; char kind=0; L cnt=0;
  for(;;){ ch=getchar();
    if(ch>='0'&&ch<='9'){ cnt=cnt*10+(ch-'0'); continue; }
    if(kind){ const char *e = kind=='a'?"cbb":kind=='b'?"b":"c"; L el=strlen(e);
      while(n+cnt*el+1>cap){ cap*=2; s=realloc(s,cap); if(!s) die("memory"); }
      for(L r=0;r<cnt;r++) for(L t=0;t<el;t++) s[n++]=e[t];
      kind=0; cnt=0; }
    if(ch==EOF) break;
    if(ch=='a'||ch=='b'||ch=='c') kind=(char)ch;
  }
  if(n==0) die("empty word");
  L *sa=malloc(n*sizeof(L)), *rk=malloc(n*sizeof(L)), *tmp=malloc(n*sizeof(L)), *sa2=malloc(n*sizeof(L)), *cntv;
  L K = n+2 > 256 ? n+2 : 256; cntv=calloc(K,sizeof(L));
  if(!sa||!rk||!tmp||!sa2||!cntv) die("memory");
  for(L i=0;i<n;i++) rk[i]=(unsigned char)s[i];
  for(L h=1;;h<<=1){
    // sort by (rk[i], rk[i+h] or -1): radix on the second key, then the first
    L m = 0; for(L i=0;i<n;i++) if(rk[i]+2>m) m=rk[i]+2;
    memset(cntv,0,m*sizeof(L));
    for(L i=0;i<n;i++){ L k2 = i+h<n ? rk[i+h]+1 : 0; cntv[k2]++; }
    for(L k=1;k<m;k++) cntv[k]+=cntv[k-1];
    for(L i=n-1;i>=0;i--){ L k2 = i+h<n ? rk[i+h]+1 : 0; sa2[--cntv[k2]]=i; }
    memset(cntv,0,m*sizeof(L));
    for(L i=0;i<n;i++) cntv[rk[i]]++;
    for(L k=1;k<m;k++) cntv[k]+=cntv[k-1];
    for(L j=n-1;j>=0;j--){ L i=sa2[j]; sa[--cntv[rk[i]]]=i; }
    tmp[sa[0]]=0;
    for(L j=1;j<n;j++){ L a=sa[j-1], b=sa[j];
      L a2 = a+h<n ? rk[a+h] : -1, b2 = b+h<n ? rk[b+h] : -1;
      tmp[b]=tmp[a]+((rk[a]!=rk[b]||a2!=b2)?1:0); }
    memcpy(rk,tmp,n*sizeof(L));
    if(rk[sa[n-1]]==n-1) break;
  }
  // PSV / NSV of SA values, indexed by text position (KKP3 style with a stack over SA order)
  L *psv=malloc(n*sizeof(L)), *nsv=malloc(n*sizeof(L)), *st=sa2; L top=0;
  for(L j=0;j<n;j++){ L v=sa[j];
    while(top>0 && st[top-1]>v){ nsv[st[top-1]]=v; top--; }
    psv[v] = top>0 ? st[top-1] : -1; st[top++]=v; }
  while(top>0){ nsv[st[top-1]]=-1; top--; }
  L z=0, i=0, longest=0;
  while(i<n){ L best=0;
    for(int t=0;t<2;t++){ L j = t ? nsv[i] : psv[i]; if(j<0) continue; L l=0; while(i+l<n && s[j+l]==s[i+l]) l++; if(l>best) best=l; }
    if(best>longest) longest=best;
    i += best>0 ? best : 1; z++; }
  printf("tokens %ld  lz77 phrases %ld  longest phrase %ld\n",(long)n,(long)z,(long)longest);
  return 0;
}
