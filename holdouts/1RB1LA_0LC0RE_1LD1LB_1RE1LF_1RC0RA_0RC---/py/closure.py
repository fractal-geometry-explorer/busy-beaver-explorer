"""The search for a closed digit language of 1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC--- (it has NOT found one).

A digit word is `B d1 ... dk END` (B the blank left end, END the last run), each digit (wall, run class); the first
digit is marked `^` so the left end is told apart.  Run classes: exact 0 .. E-1, and >= E by residue mod MO.  The
language is "every n-gram of the padded word is in P".  Starting from one early sample, the search takes every
place a sweep can happen in a word of the language (a stop digit, its carry chain of up to two S3 digits, more
digits to the left while the symbolic run touches them, up to 6), runs the machine symbolically on that window
(`digits.py`, `symtm`, runs as variables of the class), reads the result back as digits, adds the n-grams of the
result to P, and repeats until nothing is new (closed) or a window fails: `deep` (the run keeps touching the
context), `unparsed` (the result is not in the wall vocabulary), `reparse` (the result changes the parse of the
untouched digits).  Chains longer than two are assumed to behave like the seqtm rules of lean/Sweeps.lean.

    python3 py/closure.py ngram N [E MO]      n-gram search (default E=2, MO=4); prints each iteration and the failures
    python3 py/closure.py kinv SWEEPS          the mod-4 relation K between neighbouring digits, counted on the run

Results (Notes for later in the README): N=2,3 with classes 0,1,2+ and N=2,3 with mod-4 classes all fail; the
vocabulary below (with the compounds T0 = S[0]S0, T1 = S[0]S1) reaches 536 bigrams before windows with an X6 or X5
next to an S1 of run 0 appear, which the real run never shows.
"""
import sys, itertools, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
import digits
from digits import symtm, direct_samples, Spec, M2
SHAPES={'S0': [(1, 3)], 'S1': [(2, 1)], 'S2': [(1, 4)], 'S3': [(1, 1), (1, 1)], 'S': [(1, 1)],
        'X6': [(1, 6)], 'X5': [(1, 5)], 'T0':[(1,1),(1,3)], 'T1':[(1,1),(2,1)]}
SP=Spec(M2,(1,2),SHAPES,'101','C',0)
digits.SPEC=SP
from bbtools.symtm import Rep, Lin
E=int(sys.argv[3]) if len(sys.argv)>3 else 2
MO=int(sys.argv[4]) if len(sys.argv)>4 else 4
def cls_of(v): return v if v<E else ('b',v%MO)
def base_of(c):
    if not isinstance(c,tuple): return c,None
    j=c[1]; b=E+((j-E)%MO); return b,MO
W=tuple(int(x) for x in SP.runw)
def run_toks(k,var=None):
    if var: return [Rep(W,Lin(k,{var[0]:var[1]}))]
    return [Rep(W,Lin(k))] if k>=1 else []
SP.run_toks=run_toks
MEMO={}
def runwin(ctx, digs, last):
    c=SP.build(ctx, digs, last, 'E')
    try: c=symtm.run(SP.m,c,SP.sample,max_moves=200000,rotate=True)
    except symtm.TouchContext: return ('touch',)
    except symtm.NeedSplit as e: return ('split',str(e))
    except symtm.Halted as e: return ('halt',str(e))
    except RuntimeError as e: return ('limit',str(e))
    vs=[v[0] for _,_,v in digs if v]+([last[1][0]] if last[1] else [])
    it=SP.interpret(c,vs)
    if it is None: return ('unparsed',' '.join(map(str,c.left)))
    nctx,nd,nl,nend,st=it
    def cl(l):
        k,t=l
        if not t: return {cls_of(k)}
        assert all(a>=0 for a in t.values()), l
        out=set()
        coefs=[a for a in t.values() if a]
        # values k + sum a_i v_i : enumerate small combos
        for vals in itertools.product(range(MO+E+2),repeat=len(coefs)):
            out.add(cls_of(k+sum(a*v for a,v in zip(coefs,vals))))
        return out
    return ('ok',nctx,[(sh,cl(l)) for sh,l in nd],cl(nl))
def strip(d): return d if d=='B' or d[0]=='END' else (d[0].rstrip('^'),d[1])
def mark(seq):
    out=[]
    for i,d in enumerate(seq):
        if d!='B' and d[0]!='END':
            d=strip(d)
            if i>0 and seq[i-1]=='B': d=(d[0]+'^',d[1])
        out.append(d)
    return out
def evalwin(ctx, digs, lastc):
    digs=[strip(d) for d in digs]
    key=(ctx,tuple(digs),lastc)
    if key in MEMO: return MEMO[key]
    def inst(c,name):
        b,m=base_of(c); return (b,(name,m) if m else None)
    todo=[[inst(c,'v%d'%i) for i,(sh,c) in enumerate(digs)]+[inst(lastc,'z')]]
    outs=[]; res=None
    while todo:
        runs=todo.pop()
        d=[(sh,b,v) for (sh,_),(b,v) in zip(digs,runs[:-1])]
        r=runwin(ctx,d,runs[-1])
        if r[0]=='split':
            done=False
            for i,(b,v) in enumerate(runs):
                if v is not None and b<20:
                    a=list(runs); a[i]=(b,None); bb=list(runs); bb[i]=(b+v[1],v)
                    todo+=[a,bb]; done=True; break
            if not done: res=r; break
            continue
        if r[0]!='ok': res=r+(tuple(d),runs[-1]); break
        outs.append(r[1:])
    if res is None: res=('ok',outs)
    MEMO[key]=res; return res
def rep(c): return base_of(c)[0]
def canon2(ds):
    ds=[strip(x) for x in ds]
    d=[(sh,rep(c)) for sh,c in ds]
    try: out=SP.canon_digits(d)
    except AssertionError: return None
    if [x[1] for x in out]!=[x[1] for x in d][:len(out)] and len(out)==len(d): pass
    # classes: if same shapes/len keep original classes
    if len(out)==len(d) and all(o[1]==x[1] for o,x in zip(out,d)): return [(o[0],c) for o,(_,c) in zip(out,ds)]
    # shapes regrouped: map each output digit's run to an input class with the same start position
    pos=[];p=0
    cells=[]
    for sh,k in d: cells.append((p,sh,k)); p+=1
    res=[]
    # runs nonzero must be carried over in order
    nz_in=[c for (sh,c),(_,k) in zip(ds,d) if k!=0]
    nz_out=[k for _,k in out if k!=0]
    if [x[1] for x in d if x[1]!=0]!=nz_out: return None
    it=iter(nz_in)
    for sh,k in out: res.append((sh,next(it) if k!=0 else 0))
    return res  # reparse with merged runs: report
PROV={}
SEED=None
def pad(w,n): return ['B']*(n-1)+w
def grams(w,n):
    w=mark(pad(w,n)); return {tuple(w[i:i+n]) for i in range(len(w)-n+1)}
def main(n=2, jmax=2, init_steps=20000, maxwin=6, maxit=300):
    samples=[]
    for step,cells in direct_samples(SP, init_steps):
        a=SP.parse_cells(cells)
        if a: samples.append(a)
    ctx,digs,last,end=samples[-1]
    w0=['B']+[(sh,cls_of(k)) for sh,k in digs]+[('END',cls_of(last))]
    P=grams(w0,n); fails={}
    print('init',w0)
    for it in range(1,maxit+1):
        new=set(); ext={}
        for g in P: ext.setdefault(g[1:],set()).add(g[0])
        def lefts(seq):
            if seq[0]=='B': return set()
            return ext.get(tuple(seq[:n-1]),set())
        def emit(ctxseq, win, e, results):
            for (nctx,nd,nl) in results:
                for combo in itertools.product(*[sorted(s,key=str) for _,s in nd]):
                    body=[(sh,c) for (sh,_),c in zip(nd,combo)]
                    real=[x for x in ctxseq if x!='B']
                    c2=canon2(real+body)
                    if c2 is not None and c2[:len(real)]!=[strip(x) for x in real] and ctxseq[0]=='B':
                        k=sum(1 for x in ctxseq if x=='B'); ctxseq2=['B']*k
                        for lc in nl:
                            seg=mark(['B']*(n-1)+c2+[('END',lc)])
                            for i in range(len(seg)-n+1):
                                g=tuple(seg[i:i+n])
                                if g not in P: new.add(g); PROV.setdefault(g,(ctxseq,win,e,body,lc))
                        continue
                    if c2 is None or c2[:len(real)]!=[strip(x) for x in real]:
                        fails.setdefault('reparse',[]).append((ctxseq,win,e,body)); continue
                    for lc in nl:
                        seg=mark(list(ctxseq)+c2[len(real):]+[('END',lc)])
                        for i in range(len(seg)-n+1):
                            g=tuple(seg[i:i+n])
                            if g not in P:
                                new.add(g); PROV.setdefault(g,(ctxseq,win,e,body,lc))
        def need_ctx(seq, win, e):
            if len(seq)>=n-1 or (seq and seq[0]=='B'): return [seq]
            out=[]
            for p in lefts(seq+win+[('END',e)]): out+=need_ctx([p]+seq,win,e)
            return out
        def attempt(left, win, e):
            if left[-1]=='B': r=evalwin(False,win,e)
            else:
                r=evalwin(True,win,e)
                if r[0] in ('touch','unparsed'):
                    if len(win)>=maxwin: fails.setdefault('deep',[]).append((left,win,e)); return
                    if len(left)>=2: attempt(left[:-1],[left[-1]]+win,e)
                    else:
                        for p in lefts(left+win+[('END',e)]): attempt([p],[left[-1]]+win,e)
                    return
            if r[0]!='ok': fails.setdefault(r[0],[]).append((left,win,e,r[1:])); return
            if n==1: emit([],win,e,r[1]); return
            for c in need_ctx(left[-(n-1):], win, e):
                c=c[-(n-1):]
                if len(c)<n-1: c=['B']*(n-1-len(c))+c
                emit(c, win, e, r[1])
        seen=set()
        for g in [g for g in P if g[-1][0]=='END']:
            e=g[-1][1]
            stack=[(list(g[:-1]),[])]
            while stack:
                left,chain=stack.pop()
                if not left:
                    for p in lefts(chain+[('END',e)]): stack.append(([p],chain))
                    continue
                d=left[-1]
                key=(tuple(left),tuple(chain),e)
                if key in seen: continue
                seen.add(key)
                if d=='B':
                    if chain: attempt(left, chain, e)
                    continue
                if d[0]=='S3':
                    if len(chain)<jmax: stack.append((left[:-1],[d]+chain))
                    continue
                rest=left[:-1]
                if not rest:
                    for p in lefts(left+chain+[('END',e)]): attempt([p],[d]+chain,e)
                else: attempt(rest,[d]+chain,e)
        print('iter',it,'P',len(P),'new',len(new),'memo',len(MEMO),'fails',{k:len(v) for k,v in fails.items()},flush=True)
        if not new or fails: break
        P|=new
    return P,fails
PH={'S0':0,'S1':1,'S2':2,'S3':3}
def kinv(sweeps):
    """Count K = phase(y) + run(x) + [x in S2,S3] mod 4 over neighbouring digits y x (both S0..S3), and
    last run - phase(last digit) mod 4, at every sample of the digit run from blank tape."""
    from collections import Counter
    sp=digits.Spec(M2,(1,2),{k:v for k,v in SHAPES.items() if k in ('S0','S1','S2','S3','S','X5','X6')},'101','C',0)
    for step,cells in direct_samples(sp, 3000):
        a=sp.parse_cells(cells)
        if a: st=(a[0],list(a[1]),a[2],a[3]); break
    C=Counter()
    for i in range(sweeps):
        d=st[1]
        for (y,ry),(x,rx) in zip(d,d[1:]):
            if y in PH and x in PH: C[(PH[y]+rx+(PH[x]>=2))%4]+=1
        if d and d[-1][0] in PH: C[('last-phase', (st[2]-PH[d[-1][0]])%4)]+=1
        r=sp.sweep(st,carry=('S3',)); st=r[1]
    for k,v in sorted(C.items(),key=str): print(k,v)
if __name__=="__main__":
    if sys.argv[1]=='kinv': kinv(int(float(sys.argv[2])))
    else:
        P,fails=main(int(sys.argv[2]))
        print('closed' if not fails else 'NOT closed')
        for k,v in fails.items():
            print(k,len(v))
            for x in v[:12]: print('  ',str(x)[:300])
