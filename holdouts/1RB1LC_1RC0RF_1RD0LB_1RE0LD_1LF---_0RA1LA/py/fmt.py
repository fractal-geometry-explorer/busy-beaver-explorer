import sys,re
for line in sys.stdin:
    l=line.split()
    if len(l)<4: print(line.strip()); continue
    s=re.sub(r'(1110){2,}',lambda m:' (1110)^%d '%(len(m.group(0))//4),l[3]); print(l[0],l[1],l[2],s)
