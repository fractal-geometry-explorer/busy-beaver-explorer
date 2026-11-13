"""Decode the output of runs.c (E L) for 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF into block lengths: words 100
between separators 1010 (`b` marks a lone 10).  usage: python3 blocks.py RUNS_OUTPUT"""
import sys
# parse runs.c lines for M1: tape from lo: runs alternate starting with symbol v0. Convert to cell string pieces and
# tokenize a=100, separators: count a's between occurrences of '10' pairs ("b").
for line in open(sys.argv[1]):
    p=line.split()
    if p[0] in ('END','HALT'): print(line.strip()); continue
    v=int(p[1][0]); runs=list(map(int,p[2:]))
    s=''.join(str(v if i%2==0 else 1-v)*r for i,r in enumerate(runs))
    # s starts with head cell 0; tokenize from index 1
    i=1; blocks=[]; cur=0; seps=0
    while i<len(s):
        if s.startswith('1010',i): blocks.append(cur); cur=0; i+=4; continue
        if s.startswith('100',i): cur+=1; i+=3; continue
        if s.startswith('10',i): blocks.append(cur); blocks.append('b'); cur=0; i+=2; continue
        blocks.append(f'?{s[i:i+6]}'); i+=1
    blocks.append(cur)
    print(p[0], blocks[:40])
