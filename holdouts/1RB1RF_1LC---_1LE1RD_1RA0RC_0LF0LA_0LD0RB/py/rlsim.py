"""A run-length simulator for any two-symbol machine: the tape is a list of tokens [word, count] (count copies of
word side by side); when the head meets a token whose word it crosses in one go, coming out on the far side in the
state it went in with, the whole token is crossed in one move (count times the steps of one copy).  Otherwise one
copy is split off (rotating the rest, so a crossing at another phase can still apply) and run cell by cell.

Exact: the tape, state and step count are those of the plain machine at the end of every move (checked by
`accel.py check` against bbtools.machine for millions of steps, and by a random test, `accel.py fuzz`).

`canon(tok, word)` re-tokenises a tape into maximal runs of `word` and single cells."""
import bisect

def parse(m):
    t={}
    for i,g in enumerate(m.split('_')):
        for b in (0,1):
            s=g[3*b:3*b+3]
            t[(i,b)]=None if s[2]=='-' else (int(s[0]),1 if s[1]=='R' else -1,ord(s[2])-65)
    return t

class Sim:
    def __init__(self, mstr, tokens, state, head=0):
        self.t = parse(mstr)
        self.tok = [list(x) for x in tokens]   # [word, count]
        self.q = state
        self.h = head          # index of token under head; if token is a run with count>1 head is at its left edge (dir decides)
        self.off = 0           # offset within token word when count==1
        self.steps = 0
        self.halted = False
        self.cc = {}
    def cross(self, w, q, d):
        key=(w,q,d)
        if key in self.cc: return self.cc[key]
        c=[int(x) for x in w]; i=0 if d==1 else len(c)-1; n=0; r=None
        while 0<=i<len(c):
            tr=self.t[(q,c[i])]
            if tr is None: r=None; break
            c[i],mv,q=tr; i+=mv; n+=1
            if n>100*len(c): r=None; break
        else:
            r=(q,''.join(map(str,c)),1 if i>=len(c) else -1,n)
        self.cc[key]=r
        return r
    def explode(self, i, d):
        """split token i so that the cell the head enters (from dir d) is a single-cell token. returns new index of that cell"""
        w,n=self.tok[i]
        if n==1 and len(w)==1: return i
        cells=[[ch,1] for ch in w]
        if n==1:
            self.tok[i:i+1]=cells
            return i if d==1 else i+len(w)-1
        if d==1:
            self.tok[i:i+1]=[[w[0],1],[w[1:]+w[0],n-1]]+cells[1:]
            return i
        else:
            self.tok[i:i+1]=cells[:-1]+[[w[-1]+w[:-1],n-1],[w[-1],1]]
            return i+len(w)
    def run(self, maxsteps, stop=None, d=None):
        """d: direction the head 'faces' when at token h (needed to know entry side). We store head as (h, d_enter)."""
        tok=self.tok
        while self.steps<maxsteps:
            h=self.h
            if h<0:
                tok.insert(0,['0',1]); h=0; self.lins=getattr(self,'lins',0)+1
            elif h>=len(tok):
                tok.append(['0',1])
            w,n=tok[h]
            dd=self.dir
            if not (n==1 and len(w)==1):
                r=self.cross(w,self.q,dd)
                if r is not None and r[0]==self.q and r[2]==dd:
                    tok[h]=[r[1],n]
                    self.steps+=n*r[3]
                    self.h=h+dd
                    continue
                done=False
                for mult in (2,3,4):
                    if n>=2*mult:
                        r=self.cross(w*mult,self.q,dd)
                        if r is not None and r[0]==self.q and r[2]==dd:
                            k,rem=divmod(n,mult)
                            if rem==0: tok[h]=[r[1],k]; self.h=h+dd
                            elif dd==1: tok[h:h+1]=[[r[1],k],[w,rem]]; self.h=h+1
                            else: tok[h:h+1]=[[w,rem],[r[1],k]]; self.h=h
                            self.steps+=k*r[3]
                            done=True; break
                if done: continue
                h=self.explode(h,dd)
            tr=self.t[(self.q,int(tok[h][0]))]
            if tr is None:
                self.halted=True; self.steps+=1; self.h=h; return 'halt'
            b,mv,q=tr
            tok[h][0]=str(b); self.q=q; self.dir=mv; self.h=h+mv; self.steps+=1
            if stop and stop(self): return 'stop'
        return 'max'

def canon(tok, word='001', minrun=2):
    """re-tokenize: maximal runs of `word` (>=minrun copies) become [word,n]; everything else single cells."""
    starts=[];p=0
    for w,n in tok: starts.append(p); p+=len(w)*n
    total=p
    def seg(pos):
        i=bisect.bisect_right(starts,pos)-1
        return i
    def ch(pos):
        i=seg(pos); w,n=tok[i]; return w[(pos-starts[i])%len(w)]
    L=len(word)
    out=[];pos=0
    while pos<total:
        # count copies of word at pos
        k=0;q=pos
        while q+L<=total:
            i=seg(q); w,n=tok[i]; segend=starts[i]+len(w)*n
            o=(q-starts[i])%len(w)
            rot=(w[o:]+w[:o])
            if len(w)==L and rot==word and segend-q>=2*L:
                m=(segend-q)//L
                k+=m; q+=m*L; continue
            if all(ch(q+j)==word[j] for j in range(L)):
                k+=1; q+=L; continue
            break
        if k>=minrun:
            out.append([word,k]); pos=q
        else:
            out.append([ch(pos),1]); pos+=1
    return out

def tostr(tok, word='001',name='a'):
    """compact display: runs of word as aN, cells grouped into strings"""
    s=[];cur=''
    for w,n in tok:
        if n==1 and len(w)==1: cur+=w
        else:
            if cur: s.append(cur); cur=''
            s.append(f'{name}{n}' if w==word else f'({w})^{n}')
    if cur: s.append(cur)
    return ' '.join(s)

def head_first(tok):
    w,n=tok[0]
    if n>1 or len(w)>1:
        return [[c,1] for c in w]+([[w,n-1]] if n>1 else [])+tok[1:]
    return tok
