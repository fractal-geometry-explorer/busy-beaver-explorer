import sys,re
src=open(sys.argv[1]).read()
# split into sentences at top-level blocks: crude line-based state machine
out=[];mode=None;buf=[]
for line in src.split('\n'):
    if mode is None:
        m=re.match(r'(Definition|Fixpoint|Inductive|Record)\b',line)
        if m: mode='def'; buf=[line]
        if mode=='def' and line.rstrip().endswith('.') and not line.rstrip().endswith('..'):
            out.append('\n'.join(buf)); mode=None
        continue
    buf.append(line)
    if line.strip()=='' : pass
    if re.search(r'\.\s*$',line) and not line.strip().startswith('(*'):
        out.append('\n'.join(buf)); mode=None
print('\n'.join(out))
