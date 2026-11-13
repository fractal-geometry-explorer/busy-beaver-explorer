/* Direct simulation from a given tape: fromtape MACHINE TAPE POS STATE MAXSTEPS
   TAPE is a 0/1 string (blank beyond it), POS the head's index in it, STATE a letter.
   Prints "halt S" (S = steps, the halting transition counted) or "nohalt MAXSTEPS". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv){
  if(argc < 6){ fprintf(stderr, "usage: fromtape MACHINE TAPE POS STATE MAXSTEPS\n"); return 2; }
  const char *m = argv[1]; int w[6][2], d[6][2], ns[6][2];
  for(int s = 0; s < 6; s++) for(int y = 0; y < 2; y++){
    const char *t = m + 7 * s + 3 * y;
    if(t[2] == '-'){ ns[s][y] = -1; w[s][y] = 0; d[s][y] = 0; continue; }
    w[s][y] = t[0] - '0'; d[s][y] = t[1] == 'R' ? 1 : -1; ns[s][y] = t[2] - 'A';
  }
  long long n = strlen(argv[2]), size = 4 * n + (1 << 22), off = size / 2;
  unsigned char *c = calloc(size, 1);
  for(long long i = 0; i < n; i++) c[off + i] = argv[2][i] - '0';
  long long p = off + atoll(argv[3]); int s = argv[4][0] - 'A';
  long long maxs = atoll(argv[5]);
  for(long long k = 0; k < maxs; k++){
    if(p <= 0 || p >= size - 1){ fprintf(stderr, "tape margin reached\n"); return 1; }
    int y = c[p];
    if(ns[s][y] < 0){ printf("halt %lld\n", k + 1); return 0; }
    c[p] = w[s][y]; p += d[s][y]; s = ns[s][y];
  }
  printf("nohalt %lld\n", maxs); return 0;
}
