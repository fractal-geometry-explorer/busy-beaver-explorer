import sys,re
sys.setrecursionlimit(100000)
# Replay an abstract halting path on a concrete tape.  When the abstract side takes the branch "this class count was exactly T",
# trim the concrete run to that count (a cousin tape with a shorter run).  Any other disagreement is a real loss of the abstraction.
m=sys.argv[1]; tr=sys.argv[2]; mir='mirror' in sys.argv[3:]
T={}
for i,row in enumerate(m.split('_')):
    for b in range(2):
        x=row[3*b:3*b+3]
        if x[0]!='-': T[(i,b)]=(int(x[0]),(1 if x[1]=='R' else -1)*(-1 if mir else 1),ord(x[2])-65)
def pcls(s):
    if s.startswith('>='):
        a,b=s[2:].split('%'); M,r=b.split('='); return ('ge',int(a),int(M),int(r))
    return ('ex',int(s))
def parse(v):
    items=[]; toks=v.split(); i=0; tail=toks[-1]; toks=toks[:-1]
    while i<len(toks):
        t=toks[i]
        if t.startswith('['):
            runs=[]; t=t[1:]
            while True:
                if t.startswith(']'): rep=pcls(t[2:]); break
                s,c=t.split('^'); runs.append((int(s),pcls(c))); i+=1; t=toks[i]
            items.append((runs,rep)); i+=1
        else:
            s,c=t.split('^'); items.append(([(int(s),pcls(c))],('ex',1))); i+=1
    return items,tail
def incls(n,c): return n==c[1] if c[0]=='ex' else (n>=c[1] and n%c[2]==c[3])
def match(items,tail,cells):
    # cells: list of 0/1/None(wildcard, unknown), then implicit unknown beyond
    from functools import lru_cache
    L=len(cells)
    def cell(p): return cells[p] if p<L else None
    @lru_cache(maxsize=None)
    def mi(ii,pos):
        if ii==len(items):
            if tail=='ANY': return True
            return all(c in (0,None) for c in cells[pos:])
        runs,rep=items[ii]; return mp(ii,0,0,pos)
    @lru_cache(maxsize=None)
    def mp(ii,ri,copies,pos):
        runs,rep=items[ii]
        if ri==len(runs):
            done=copies+1
            if incls(done,rep) and mi(ii+1,pos): return True
            if pos>=L+2: return incls(done,rep) or rep[0]=='ge'   # everything beyond is unknown
            if rep[0]=='ex' and done>=rep[1]: return False
            return mp(ii,0,done,pos)
        s,c=runs[ri]; n=0
        while True:
            x=cell(pos+n)
            if x is not None and x!=s: break
            n+=1
            if incls(n,c) and mp(ii,ri+1,copies,pos+n): return True
            if pos+n>L+ (c[1] if c[0]=='ex' else c[1]+c[2])+2: break
        return False
    return mi(0,0)
T2=int([a for a in sys.argv if a.startswith('T2=')][0][3:]); E1=int([a for a in sys.argv if a.startswith('E1=')][0][3:])
lines=[l for l in open(tr) if ' reads ' in l]
left=[]; right=[]   # stack side (end = nearest), abstract side (index 0 = nearest); None = unknown
q=None; step=0; trims=0; trimlog=[]
def word(runs):
    w=[]
    for s,c in runs:
        if c[0]!='ex': return None
        w+= [s]*c[1]
    return w
for li,l in enumerate(lines):
    mm=re.search(r' ([A-F]) reads (\d) \| (.*)',l); Q=ord(mm.group(1))-65; h=int(mm.group(2)); items,tail=parse(mm.group(3))
    if q is None: q=Q; head=h
    if Q!=q: print('state mismatch at',step); break
    if head is None: head=h
    if head==h:
        # cousin trims: an exact-count pattern whose concrete run is longer than the abstract count
        pos=0
        prevhas = li>0 and '>=' in lines[li-1]
        for runs,rep in items:
            if len(runs)==1:
                s_,c=runs[0]
                if c[0]!='ex': break
                n=0
                while pos+n<len(right) and right[pos+n]==s_: n+=1
                if n>c[1] and c[1]==E1-1 and prevhas:
                    saved=list(right); del right[pos+c[1]:pos+n]
                    if match(items,tail,tuple(right)): trims+=1; trimlog.append((step,n,c[1],mm.group(3)))
                    else: right[:]=saved
                    break
                if n<c[1]: break
                pos+=c[1]; continue
            w=word(runs)
            if w is None or rep[0]!='ex': break
            n=0
            while right[pos+n*len(w):pos+(n+1)*len(w)]==w: n+=1
            if n>rep[1] and rep[1]==T2-1 and prevhas:
                saved=list(right); del right[pos+rep[1]*len(w): pos+n*len(w)]
                if match(items,tail,tuple(right)): trims+=1; trimlog.append((step,n,rep[1],mm.group(3)))
                else: right[:]=saved
                break
            if n<rep[1]: break
            pos+=rep[1]*len(w)
    bad = head!=h or not match(items,tail,tuple(right))
    if bad:
        print('LOSS at trace step',step,'of',len(lines),'(after',trims,'trims).  state','ABCDEF'[q],'head cell',head,'trace reads',h)
        print('  abstract side :',mm.group(3))
        print('  concrete side :',''.join('.' if c is None else str(c) for c in right[:150]))
        print('  stack side    :',''.join('.' if c is None else str(c) for c in left[-100:]))
        print('  previous abstract side:',re.search(r'\| (.*)',lines[li-1]).group(1) if li else '')
        break
    if (q,h) not in T: print('trace replays to a halt after',step,'steps,',trims,'trims'); print('  concrete side :',''.join('.' if c is None else str(c) for c in right[:150])); print('  stack side    :',''.join('.' if c is None else str(c) for c in left[-100:])); break
    w,d,q2=T[(q,h)]
    if d>0: left.append(w); head= right.pop(0) if right else None
    else: right.insert(0,w); head= left.pop() if left else None
    q=q2; step+=1

for t in trimlog[-12:]: print('  trim at step',t[0],': run of',t[1],'copies cut to',t[2],'|',t[3][:90])
