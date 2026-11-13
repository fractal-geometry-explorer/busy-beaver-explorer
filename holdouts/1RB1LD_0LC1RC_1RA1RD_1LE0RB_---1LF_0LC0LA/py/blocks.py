# read tok output lines with no words (pure rle) and print block-length lists: runs of 1s between zeros, rle'd
import sys,re
for line in sys.stdin:
    t=line.split()
    if not t or not t[0].isdigit(): continue
    toks=t[2:]
    s=''
    for x in toks:
        if x.endswith('>'): s+='|'; continue
        if '^' in x: c,n=x.split('^'); s+=c*int(n)
        else: s+=x
    # split by '0'
    parts=s.split('0')
    lens=[]
    for p in parts:
        lens.append(str(len(p.replace('|','')))+('*' if '|' in p else ''))
    out=[];i=0
    while i<len(lens):
        j=i
        while j<len(lens) and lens[j]==lens[i]: j+=1
        out.append(lens[i] if j-i==1 else f"{lens[i]}x{j-i}"); i=j
    print(t[0],t[1],' '.join(out))
