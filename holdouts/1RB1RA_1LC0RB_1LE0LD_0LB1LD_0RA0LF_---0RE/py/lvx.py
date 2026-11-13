r"""Read the `LV` lines of c/hsim2.cpp (run with LEVELS=1): for each level the size b of the block (01111)^b (words
already copied out as `010` are counted; the line is taken while the block is being rewritten, so b can be a few
words short) and the tape T to its left.

usage: LEVELS=1 ./hsim2 MACHINE 30 1e30 SECONDS 1000000000000 | grep '^LV\|^END\|^HALT' > lv.txt
       python3 holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/py/lvx.py lv.txt
"""
import re,sys
def comp(s):
    # compress runs of 100 / 110011 / 001111 for display
    for w in ('100','110011','111100','01111'):
        s=re.sub('((?:%s){8,})'%w, lambda m:' (%s)^%d '%(w,len(m.group(1))//len(w)), s)
    return s
for line in open(sys.argv[1]):
    if not line.startswith('LV'): print(line.strip()[:120]); continue
    hd,l,r=line.rstrip('\n').split('|'); f=hd.split()
    ex=lambda part: ''.join(b*int(c) for b,c in (x.split(':') for x in part.split()))
    s=(ex(l)+ex(r)).strip('0'); s='0'+s
    m=max(re.finditer(r'(?:01111){20,}',s), key=lambda m:len(m.group(0)))
    n=len(m.group(0))//5
    rest=s[m.end():]
    j=len(re.match(r'(?:010)*',rest).group(0))//3
    T=s[:m.start()]
    print(f"step~{f[1]}  b={n+j} (n={n}, copied {j})  T = {comp(T)}   after: {rest[3*j:3*j+30]}")
