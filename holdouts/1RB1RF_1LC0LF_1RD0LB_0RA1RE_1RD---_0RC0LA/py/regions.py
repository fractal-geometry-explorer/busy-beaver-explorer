"""Summarise tapes printed by `tools/c/tmrun MACHINE STEPS every N`: for each line, the steps, the length of the
written tape and how many blocks of 1s of each length it holds.

usage: tmrun MACHINE 1600000000 every 400000000 > every.txt; python3 regions.py every.txt
"""
import re,collections,sys
for l in open(sys.argv[1]):
    p=l.split()
    if not p[0].isdigit() or len(p)<10: continue
    s=''
    for t in p[1:]:
        t=re.sub(r'[A-F]?[<>][A-F]?','',t)
        if not t: continue
        if '^' in t: c,k=t.split('^'); s+=c*int(k)
        else: s+=t
    s=s.strip('0')
    bl=[len(x) for x in re.split('0+',s)]
    c=collections.Counter(bl)
    print(p[0],len(s),' '.join(f'{k}:{v}' for k,v in sorted(c.items())))
