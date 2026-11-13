"""The digit model of 1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA: an exact simulator at sample points.

At each sample point (A on the last 1 at the right end) the tape is 0^inf, then digits `(110)^r W` (a run of r
words 110, then a wall W), then the last run `(110)^last`, then `10 1 A> 1`.  Walls: W0 = 11110, W1 = 1100,
W2 = 1100 110 11110, W3 = 1100 1100, T = 1110, U = 11000, S = 10 (the 10 at the left end is a digit S with run 0).
`sweep` maps one sample to the next: it finds the carry chain (the W3 digits next to the end), runs the machine
SYMBOLICALLY (tools/py/bbtools/symtm.py) on a window holding the chain and the stop digit (more digits if the run
needs them, the rest of the tape an unknown context), with runs longer than 7 as variables, reads the end back as
digits, and caches the rule by the window's shape.  Every number it prints is a machine run, not a model guess.

usage: python3 digits.py check STEPS                compare with a direct run from blank tape up to STEPS
       python3 digits.py far STEPS SWEEPS [EVERY]    from the last sample before STEPS, SWEEPS sweeps more
"""
import os, sys, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
from bbtools import symtm
from bbtools.symtm import Rep, Lin, Blank, Ctx, Config
from bbtools.machine import Machine, STATES
def lits(s): return [int(c) for c in s]
def bw(b): return '1'*b[0]+'0'*b[1]
class Spec:
    def __init__(s, machine, runblock, shapes, endcells, state, headsym, pairs=False, big=6, ends=None):
        s.m=Machine.parse(machine); s.runblock=runblock; s.runw=bw(runblock)
        s.shapes=shapes  # name -> list of blocks (ordered by parse priority: longer first)
        s.order=sorted(shapes.items(), key=lambda kv:-len(kv[1]))
        s.ends=ends or {'E':endcells}  # name -> cells string (left of head, after last run)
        s.Q=STATES.index(state); s.hs=headsym; s.pairs=pairs; s.big=big
        s.memo={}; s.stats={'sym':0,'hit':0}
    # ---- runs
    def run_toks(s, k, var=None):
        """count k (int) or var-based: count = 2*var+k (pairs) / var+k"""
        w=tuple(lits(s.runw))
        if s.pairs:
            out=lits(s.runw*(k%2)); 
            if var: out.append(Rep(w+w,Lin(var)+k//2))
            elif k>=2: out.append(Rep(w+w,Lin(k//2)))
            return out
        if var: return [Rep(w,Lin(var)+k)]
        return [Rep(w,Lin(k))] if k>=1 else []
    def sample(s, c):
        if c.steps.is_zero() or c.state!=s.Q: return False
        r=symtm.canon(c.right)
        if s.hs==0: return r==[Blank()] or r==[0,Blank()]
        return r==[1,Blank()]
    def head_right(s):
        return [Blank()] if s.hs==0 else [1,Blank()]
    def build(s, ctx, digits, last, end):
        """digits: list of (shape, k, var) ; last: (k,var). ctx True: Ctx L at left; else Blank."""
        left=[Ctx('L')] if ctx else [Blank()]
        for sh,k,v in digits:
            left+=s.run_toks(k,v)+lits(''.join(bw(b) for b in s.shapes[sh]))
        left+=s.run_toks(*last)+lits(s.ends[end])
        return Config(left,s.Q,s.head_right())
    # ---- parsing
    def parse_blocks(s, b):
        out=[]; k=0; i=0
        while i<len(b):
            x=b[i]
            if x[0]=='R': k+=x[1]; i+=1; continue
            for name,bl in s.order:
                bl = [('R', 1) if x == s.runblock else x for x in bl]
                if tuple(b[i:i+len(bl)])==tuple(bl):
                    out.append((name,k)); k=0; i+=len(bl); break
            else: return None
        return out,k
    def to_blocks(s, cells):
        bl=[(len(a),len(z)) for a,z in re.findall(r'(1+)(0+)',cells)]
        if ''.join(bw(x) for x in bl)!=cells: return None
        out=[]
        for x in bl:
            if x==s.runblock:
                if out and out[-1][0]=='R': out[-1]=('R',out[-1][1]+1)
                else: out.append(('R',1))
            else: out.append(x)
        return out
    def parse_cells(s, cells):
        """cells: string starting with 'B' or 'L'; returns (ctx, digits, last, end) or None"""
        ctx=cells[0]=='L'; c=cells[1:]
        if not ctx: c=c.lstrip('0')
        for en,ec in s.ends.items():
            if c.endswith(ec):
                body=c[:len(c)-len(ec)]
                if body and body[-1]=='1': continue
                b=s.to_blocks(body+'1')  # sentinel trick not needed if body ends in 0
                b=s.to_blocks(body) if body else []
                if b is None: continue
                p=s.parse_blocks(b)
                if p is None: continue
                return ctx,p[0],p[1],en
        return None
    def canon_digits(s, digits):
        b=[]
        for sh,k in digits:
            if k: b.append(('R',k))
            b+=list(s.shapes[sh])
        b2=[]
        for x in b:
            if x==s.runblock: x=('R',1)
            if x[0]=='R' and b2 and b2[-1][0]=='R': b2[-1]=('R',b2[-1][1]+x[1])
            else: b2.append(x)
        p=s.parse_blocks(b2)
        assert p is not None and p[1]==0, (digits,p)
        return p[0]
    # ---- symbolic window
    def conc(s, toks, env):
        out=[]
        for t in toks:
            if isinstance(t,int): out.append(str(t))
            elif isinstance(t,Rep): out.append(''.join(map(str,t.word))*t.n.subs(env))
            elif isinstance(t,Blank): out.append('B')
            elif isinstance(t,Ctx): out.append('L')
        return ''.join(out)
    def interpret(s, c, vs):
        env={v:7 for v in vs}
        p0=s.parse_cells(s.conc(c.left,env))
        if p0 is None: return None
        ctx,d0,l0,end=p0
        coef={}
        for v in vs:
            e2=dict(env); e2[v]=8
            p1=s.parse_cells(s.conc(c.left,e2))
            if p1 is None or p1[0]!=ctx or [x[0] for x in p1[1]]!=[x[0] for x in d0] or p1[3]!=end: return None
            coef[v]=([a[1]-b[1] for a,b in zip(p1[1],d0)], p1[2]-l0)
        def lin(idx):
            val=(d0[idx][1] if idx is not None else l0)
            terms={v:(coef[v][0][idx] if idx is not None else coef[v][1]) for v in vs}
            const=val-sum(7*a for a in terms.values())
            return (const,{v:a for v,a in terms.items() if a})
        return ctx,[(d0[i][0],lin(i)) for i in range(len(d0))],lin(None),end,c.steps
    def absrun(s, k, v, par_ok=True):
        if k<=s.big+1: return (k,None),None
        base=s.big+(k%2) if s.pairs else s.big
        return (base,v),(v,(k-base)//2 if s.pairs else k-base)
    def chain_len(s, digits):
        return 0
    def sweep(s, state, carry=('S3',)):
        ctx0,digits,last,end=state
        n=len(digits)
        j=0
        while j<n and digits[n-1-j][0] in carry: j+=1
        w=min(n,j+1)
        while True:
            vis=digits[n-w:]; usepre=(w==n)
            env={}; rd=[]
            for i,(sh,k) in enumerate(vis):
                (b,v),e=s.absrun(k,'v%d'%i); rd.append((sh,b,v))
                if e: env[e[0]]=e[1]
            (lb,lv),e=s.absrun(last,'z')
            if e: env[e[0]]=e[1]
            key=(usepre, tuple((sh,b if v is None else ('big',b)) for sh,b,v in rd), (lb if lv is None else ('big',lb)), end)
            if key in s.memo: res=s.memo[key]; s.stats['hit']+=1
            else:
                s.stats['sym']+=1
                c=s.build(not usepre, rd, (lb,lv), end)
                try:
                    c=symtm.run(s.m,c,s.sample,max_moves=50000,rotate=True)
                    vs=[v for _,_,v in rd if v]+([lv] if lv else [])
                    it=s.interpret(c,vs)
                    res=('ok',it) if it else ('unparsed',c)
                except symtm.TouchContext: res=('touch',)
                except symtm.Halted as e: res=('halt',str(e))
                except symtm.NeedSplit as e: res=('split',str(e))
                except RuntimeError as e: res=('limit',str(e))
                s.memo[key]=res
            if res[0] in ('touch','unparsed') and w<n: w+=1; continue
            if res[0]!='ok': return res+(key,)
            nctx,ndigs,nlast,nend,steps=res[1]
            ev=lambda l: l[0]+sum(a*env[v] for v,a in l[1].items())
            newd=s.canon_digits(digits[:n-w]+[(sh,ev(l)) for sh,l in ndigs])
            st=steps.k+sum(a*env.get(v,0) for v,a in steps.c.items())
            return ('ok',(ctx0 and nctx, newd, ev(nlast), nend), st)
def tok_tape(line):
    t=line.split('|')[1].split(); s='B'
    for tok in t:
        mm=re.match(r'^(.*?)x(\d+)$',tok); rep=1
        if mm: tok,rep=mm.group(1),int(mm.group(2))
        if tok.startswith('_'): s+='0'*int(tok[1:]); continue
        if '/' in tok:
            a,b=tok.split('/'); s+=('1'*int(a)+('0'*int(b) if b!='E' else ''))*rep
        else: s+=('1'*int(tok)+'0')*rep
    return s


# ---------------------------------------------------------------- driver
def direct_samples(spec, max_steps):
    """Direct simulation from blank tape: yields (step, left cells string 'B...') at each sample point (head on the
    rightmost visited cell, in state Q, reading the sample symbol)."""
    from bbtools.machine import Run
    r = Run(spec.m)
    while r.steps < max_steps:
        t = r.tape
        if r.state == spec.Q and r.head == t.hi and t.get(r.head) == spec.hs and r.steps > 0:
            yield r.steps, 'B' + ''.join(map(str, t.word(t.lo, r.head - 1)))
        if not r.step():
            raise RuntimeError(f"halted at step {r.steps}")


def check(spec, carry, max_steps):
    """Compare the abstract sweeps with the direct run at every sample point up to max_steps."""
    st, T, n, bad = None, None, 0, 0
    for step, cells in direct_samples(spec, max_steps):
        a = spec.parse_cells(cells)
        if a is None:
            st = None
            continue
        a = (a[0], list(a[1]), a[2], a[3])
        if st is not None:
            n += 1
            if st != a or T != step:
                bad += 1
                print("MISMATCH at step", step, show(st), "expected", show(a))
        r = spec.sweep(a, carry=carry)
        st, T = (r[1], step + r[2]) if r[0] == "ok" else (None, None)
    print(f"{n} sweeps compared with the direct run up to step {max_steps}: {bad} mismatches; "
          f"{len(spec.memo)} window rules derived")


def show(st):
    return " ".join(f"[{k}]{s}" for s, k in st[1]) + f" [{st[2]}] {st[3]}"


def far(spec, carry, start_steps, sweeps, every):
    """Start from the last sample before start_steps (direct run), then apply `sweeps` abstract sweeps; print the
    configuration whenever the number of digits changes or the first digit changes, and every `every` sweeps."""
    last = None
    for step, cells in direct_samples(spec, start_steps):
        last = (step, cells)
    a = spec.parse_cells(last[1])
    st, T = (a[0], list(a[1]), a[2], a[3]), last[0]
    print("start", T, show(st))
    for i in range(sweeps):
        r = spec.sweep(st, carry=carry)
        if r[0] != "ok":
            print("STOP", i, T, r[0], show(st))
            return
        old, st, T = st, r[1], T + r[2]
        if len(st[1]) != len(old[1]) or st[1][:1] != old[1][:1] or (every and i % every == 0):
            print(i, T, show(st)[:400])
    print("end", sweeps, T, show(st)[:400], f"({len(spec.memo)} window rules)")


def main(spec, carry):
    if sys.argv[1] == "check":
        check(spec, carry, int(float(sys.argv[2])))
    else:
        far(spec, carry, int(float(sys.argv[2])), int(float(sys.argv[3])), int(float(sys.argv[4])) if len(sys.argv) > 4 else 0)

M1 = "1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA"
SPEC = Spec(M1, (2, 1), {'S': [(1, 1)], 'W0': [(4, 1)], 'W1': [(2, 2)], 'W2': [(2, 2), (2, 1), (4, 1)],
                         'W3': [(2, 2), (2, 2)], 'T': [(3, 1)], 'U': [(2, 3)]}, None, 'A', 1, pairs=True,
            ends={'E': '101', 'E3': '11101'})
if __name__ == "__main__":
    main(SPEC, ('W3',))
