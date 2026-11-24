import re,sys
def trim(src,target):
    L=src.split('\n')
    pos=[i for i,l in enumerate(L) if '"%s"'%target in l]
    if not pos: raise SystemExit('target not found')
    p=pos[0]
    # module blocks at column 0
    mods=[];stack=[]
    for i,l in enumerate(L):
        m=re.match(r'Module (\w+)\s*\.',l)
        if m: stack.append((m.group(1),i))
        m=re.match(r'End (\w+)\s*\.',l)
        if m and stack and stack[-1][0]==m.group(1):
            n,s=stack.pop()
            if not stack: mods.append((s,i))
    keep=[True]*len(L)
    inmod=[m for m in mods if m[0]<=p<=m[1]]
    if inmod:
        for s,e in mods:
            if (s,e)==inmod[0]: continue
            if 'TM_from_str "' in '\n'.join(L[s:e+1]) and s>min(x[0] for x in mods if 'TM_from_str "' in '\n'.join(L[x[0]:x[1]+1])) -1:
                # only drop modules that come after the first machine module (keep templates)
                if not re.search(r'Hypothesis|Section',"\n".join(L[s:e+1])):
                    for k in range(s,e+1): keep[k]=False
    else:
        i=0
        while i<len(L):
            if re.match(r'Definition tm\w* *:= *(Eval compute in )?\(?TM_from_str "',L[i]) and i!=p:
                j=i
                while j<len(L) and not L[j].startswith('Qed.'): j+=1
                if not any(k in pos for k in range(i,j+1)):
                    for k in range(i,j+1): keep[k]=False
                i=j+1
            else: i+=1
    return '\n'.join(l for l,k in zip(L,keep) if k)
