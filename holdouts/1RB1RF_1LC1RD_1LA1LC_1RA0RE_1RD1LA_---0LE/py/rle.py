"""RLE tape simulator with run crossing. Stacks L, R of [sym,count]; nearest the head last; head reads top of R."""
import sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine
def push(st, sym, c):
    if c<=0: return
    if st and st[-1][0]==sym: st[-1][1]+=c
    else: st.append([sym,c])
def pop1(st):
    if not st: return 0
    st[-1][1]-=1; v=st[-1][0]
    if st[-1][1]==0: st.pop()
    return v
class R:
    def __init__(s, mach):
        s.m = Machine.parse(mach) if isinstance(mach,str) else mach
        s.L=[]; s.R=[]; s.q=0; s.steps=0; s.halted=False; s.pos=0; s.lo=0; s.hi=0
    def read(s): return s.R[-1][0] if s.R else 0
    def step(s):
        x=s.read(); t=s.m.table[s.q][x]
        if t is None: s.halted=True; s.steps+=1; return False
        w,d,q2=t
        if q2==s.q:
            if d==1:
                if s.R:
                    n=s.R.pop()[1]
                else: n=1
                push(s.L,w,n); s.steps+=n; s.pos+=n
            else:
                pop1(s.R); n=1
                if s.L and s.L[-1][0]==x: n+=s.L.pop()[1]
                push(s.R,w,n); push(s.R,pop1(s.L),1); s.steps+=n; s.pos-=n
        else:
            pop1(s.R)
            if d==1: push(s.L,w,1); s.pos+=1
            else: push(s.R,w,1); push(s.R,pop1(s.L),1); s.pos-=1
            s.q=q2; s.steps+=1
        if s.pos<s.lo: s.lo=s.pos
        if s.pos>s.hi: s.hi=s.pos
        return True
    def __str__(s):
        a=' '.join(f"{x}^{c}" if c>1 else str(x) for x,c in s.L)
        b=' '.join(f"{x}^{c}" if c>1 else str(x) for x,c in reversed(s.R))
        return f"{a} {'ABCDEF'[s.q]}> {b}"
if __name__=='__main__':
    # self-test vs Machine Run
    from bbtools.machine import Run
    for M in sys.argv[1:]:
        r=R(M); ref=Run(Machine.parse(M))
        for i in range(20000):
            r.step()
            while ref.steps<r.steps: ref.step()
            assert ref.steps==r.steps and ref.state==r.q and ref.head==r.pos, (i,)
            if i%997==0:
                cells=[]
                for x,c in r.L: cells+= [x]*c
                h=len(cells)
                for x,c in reversed(r.R): cells+=[x]*c
                lo=r.pos-h
                ref_cells=[ref.tape.get(p) for p in range(lo, lo+len(cells))]
                assert cells==ref_cells,(i,)
                assert all(ref.tape.get(p)==0 for p in range(ref.tape.lo-1,lo))
                assert all(ref.tape.get(p)==0 for p in range(lo+len(cells),ref.tape.hi+2))
        print('ok',M,r.steps)
