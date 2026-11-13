"""tokenize tmrun 'at' / records lines: python3 tokl.py LOG WORDS(a=10,c=110) [prefix-filter]"""
import sys,re
def cells_of(body):
    c=[];head=None
    for k in body.split():
        if '>' in k:
            head=(k[0],len(c)); k=k[2:]
            if not k: continue
        if '^' in k: a,b=k.split('^'); c+=[int(a)]*int(b)
        else: c+= [int(ch) for ch in k]
    return c,head
def tokenize(cells, words):
    ws=sorted(words.items(), key=lambda kv:-len(kv[1]))
    s=''.join(map(str,cells)); out=[]; i=0
    while i<len(s):
        for name,w in ws:
            if s.startswith(w,i): out.append(name); i+=len(w); break
        else: out.append(s[i]); i+=1
    # run-length
    res=[]; j=0
    while j<len(out):
        k=j
        while k<len(out) and out[k]==out[j]: k+=1
        res.append(out[j]+(f"^{k-j}" if k-j>1 else '')); j=k
    return ' '.join(res)
if __name__=='__main__':
    words=dict(kv.split('=') for kv in sys.argv[2].split(','))
    pre=sys.argv[3] if len(sys.argv)>3 else ''
    for line in open(sys.argv[1]):
        t=line.split(None,1)
        if len(t)<2 or not t[0].isdigit(): continue
        body=t[1].strip()
        parts=body.split()
        # records format: STEP SIDE WIDTH tape ; at format: STEP tape
        if parts[0] in ('L','R'): side=parts[0]; body=' '.join(parts[2:])
        if pre and not body.startswith(pre): continue
        c,h=cells_of(body)
        print(t[0], h[0] if h else '', tokenize(c,words))
