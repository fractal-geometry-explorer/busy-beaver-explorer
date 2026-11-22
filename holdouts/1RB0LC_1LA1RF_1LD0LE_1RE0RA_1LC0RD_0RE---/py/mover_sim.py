"""Exact event-driven simulator of 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- built on the mover lemmas.

usage:  python3 py/mover_sim.py check N        run N bounces from step 273,791 and compare the tape with a direct
                                               simulation (c/dump.c) at the step reached
        python3 py/mover_sim.py run MAXSTEPS   run to MAXSTEPS and print every drain end (list of blocks)

Tape at a right-end turn (head in E on the blank):   Y | movers(gs) | Z  E> 0^inf
  Y : stack (top = nearest the movers) of canonical items: int g = g pairs read outward as (1,0) (= (01)^g left to
      right), '0'/'1' single cells, ('M', Movers) a block of movers at rest that the head does not cross (expanded
      lazily, one mover at a time, when the head reaches it), 'B' blank at the bottom.
  gs: the movers the head crosses on every bounce (Movers.lean `movers gs`), rightmost first, as runs.
  Z : stack of canonical items between the movers and the right end ('X' at the bottom).
Moves:
  jump   k bounces of Q's walk at once (Walk.walk without movers, Movers.bounce0m/1m with movers);
  macro  head in E on a 0 just right of the movers: Movers.left_all, then the run on Y cell by cell until the head
         steps right onto the movers in D or F, then Movers.right_gen (bounce_gen);
  cells  everything else, one machine step at a time, runs of pairs crossed by Rules.lean's crossing rules.
"""
T={}
MACH="1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---"
for s_,part in enumerate(MACH.split('_')):
    for r in range(2):
        q=part[3*r:3*r+3]
        T[(s_,r)]=None if q[2]=='-' else (int(q[0]),1 if q[1]=='R' else -1,ord(q[2])-65)
A_,B_,C_,D_,E_,F_=range(6)
class Halt(Exception): pass
class Boundary(Exception): pass
class MacroPoint(Exception): pass

class Movers:
    def __init__(self): self.r=[]; self.G=0; self.m=0
    def __bool__(self): return self.m>0
    def first(self): return self.r[0][0]
    def add_first(self,k):
        g,c=self.r[0]
        if c==1: self.r[0][0]=g+k
        else: self.r[0][1]=c-1; self.r.insert(0,[g+k,1])
        self.G+=k
    def pop_first(self):
        g,c=self.r[0]
        if c==1: self.r.pop(0)
        else: self.r[0][1]=c-1
        self.G-=g; self.m-=1; return g
    def append(self,g):
        if self.r and self.r[-1][0]==g: self.r[-1][1]+=1
        else: self.r.append([g,1])
        self.G+=g; self.m+=1
    def gaps(self):
        for g,c in self.r:
            for _ in range(c): yield g

def push(st,c):
    t=st[-1]
    if c==0:
        if t=='B': return
        st.append('0'); return
    if t=='0':
        st.pop(); t=st[-1]
        if isinstance(t,int): st[-1]=t+1
        else: st.append(1)
        return
    st.append('1')
def push_gap(st,g):
    if g<=0: return
    t=st[-1]
    if isinstance(t,int): st[-1]=t+g
    else: st.append(g)
def push_mover(st,g):
    for x in (0,0,1,1,0): push(st,x)
    push_gap(st,g)
def pop(st):
    while True:
        t=st[-1]
        if t=='B': return 0
        if t=='X': raise Boundary()
        if t=='0' or t=='1': st.pop(); return int(t)
        if isinstance(t,int):
            if t>1: st[-1]=t-1
            else: st.pop()
            st.append('0'); return 1
        # ('M', movers): expand the rightmost mover
        mv=t[1]
        if not mv: st.pop(); continue
        g=mv.pop_first(); push_mover(st,g)

def run_local(L,R,s,maxmoves,stop_rightend=False,macro=False,pending=False):
    """machine run on (L, s, R), head reads top of R.  Returns (steps, state) when the head steps right onto 'X'
    (top of R), or with stop_rightend when back at the right end in E.  With macro: raises MacroPoint (steps, s)
    when the head is in E on a 0 with L empty ('X')."""
    steps=0; moves=0
    if pending:
        x=pop(L); push(R,x)
    while True:
        if stop_rightend and moves>0 and s==E_ and len(R)==1 and R[0]=='B': return steps,s
        if moves>maxmoves: raise RuntimeError('too long')
        moves+=1
        if R[-1]=='X': return steps,s
        if s==E_ and isinstance(R[-1],int):
            g=R.pop(); push_gap(L,g); steps+=2*g; continue
        if macro and L[-1]=='X' and s==E_ and (R[-1]=='0' or R[-1]=='B'):
            raise MacroPoint(steps)
        c=pop(R)
        tr=T[(s,c)]
        if tr is None: raise Halt((steps,list(L[-12:]),list(R[-12:])))
        w,d,ns=tr; steps+=1; s=ns
        if d>0:
            push(L,w)
        else:
            push(R,w)
            if s==C_ and isinstance(L[-1],int):
                g=L.pop(); push_gap(R,g); steps+=2*g
            if L[-1]=='X': raise Boundary(steps,s)
            x=pop(L); push(R,x)

def absorb(Y,gs):
    while len(Y)>=6 and isinstance(Y[-1],int) and Y[-1]>=(1 if gs else 2) and Y[-2]=='0' and Y[-3]=='1' and Y[-4]==1 and Y[-5]=='0':
        g=Y[-1]; del Y[-5:]; gs.append(g)

def jumpcost(k,A,G,m,q,mov):
    da=3 if mov else 2
    tot=k*(4*G+20*m+4*A-3)+4*da*k*(k-1)//2-(4*k*(k-1)//2 if mov else 0)
    n0=(k+1)//2 if q==0 else k//2
    return tot+13*n0+9*(k-n0)

def walk_form(S):
    return len(S)>=4 and isinstance(S[-1],int) and S[-2] in ('0','1') and isinstance(S[-3],int)
def do_jump(S,k,mov):
    A=S[-1]; q=int(S[-2]); C=S[-3]
    S[-1]=A+(3 if mov else 2)*k; S[-2]=str(q^(k&1))
    if C==k:
        del S[-3]
        if S[-2]=='1' and S[-3]=='0':
            a=S.pop(); S.pop(); S.pop(); push_gap(S,1); push_gap(S,a)
    else: S[-3]=C-k

class Sim:
    def __init__(self,cells,steps):
        self.Y=['B']
        for c in cells: push(self.Y,c)
        self.gs=Movers(); self.Z=['X']; self.steps=steps; self.stats={}
        self.events=[]
    def st(self,k,n=1): self.stats[k]=self.stats.get(k,0)+n
    def merge_Z(self):
        # Z (and nothing between) onto Y, when there are no movers
        items=self.Z[1:]
        for it in items:
            if isinstance(it,int): push_gap(self.Y,it)
            else: push(self.Y,int(it))
        self.Z=['X']
    def macro(self):
        """head in E on a 0 just right of the movers (consumed): left_all, Y-local run, right_gen.  Returns the
        state the head is in when it comes out on the right of the movers (D), with the trailing 0 not yet placed."""
        gs=self.gs; G=gs.G; m=gs.m
        R=['X','0']
        st,s=run_local(self.Y,R,E_,10**8)
        if s not in (D_,F_): raise RuntimeError('exit state %d'%s)
        for c in ((1,0,1) if s==D_ else (0,0,1)): push(self.Y,c)
        self.steps+=(2*G+15*m)+st+(2*G+5*m)
        self.st('macro' if s==D_ else 'macroF')
    def bounce(self,maxmoves=10**8):
        if getattr(self,'swapped',False):
            # Z became the whole tape (no movers left): make it Y again
            self.Y[:]=self.Z[:]; self.Z[:]=['X']; self.swapped=False
        Y,gs,Z=self.Y,self.gs,self.Z
        if len(Z)==1:
            absorb(Y,gs)
            if gs and gs.first()<2:
                g=gs.pop_first(); push_mover(Z,g)
                if not gs: self.merge_Z()
                return self.bounce(maxmoves)
            if walk_form(Y):
                mov=bool(gs); C=Y[-3]
                k=C if not mov else min(C,gs.first()-1)
                if k>=1:
                    self.steps+=jumpcost(k,Y[-1],gs.G,gs.m,int(Y[-2]),mov)
                    do_jump(Y,k,mov)
                    if mov: gs.add_first(-k)
                    self.st('jump'); self.st('jb',k); return k
            if gs:
                self.macro(); self.steps+=1; gs.add_first(-1); return 1
            R=['B']
            st,s=run_local(Y,R,E_,maxmoves,stop_rightend=True)
            self.steps+=st; self.st('plain'); return 1
        # Z nonempty (and gs nonempty)
        if walk_form(Z) and isinstance(Z[-3],int):
            C=Z[-3]; k=C
            self.steps+=jumpcost(k,Z[-1],0,0,int(Z[-2]),False); do_jump(Z,k,False); self.st('zjump'); self.st('jb',k)
            self.after_z(birth=True); return k
        R=['B']; touched=False; s0=E_; pend=False
        while True:
            try:
                st,s=run_local(Z,R,s0,maxmoves,stop_rightend=True,macro=True,pending=pend)
                self.steps+=st; break
            except MacroPoint as e:
                self.steps+=e.args[0]; touched=True
                if gs.first()<2:
                    self.unfold_into_Z(); s0=E_; pend=False
                    continue
                pop(R)   # the 0 read by E becomes part of the swept movers
                self.macro()
                gs.add_first(-2); push(Z,0); s0=D_; pend=False
                self.st('zmacro')
            except Boundary as e:
                st,s=e.args; self.steps+=st; touched=True
                self.unfold_into_Z(); s0=s; pend=True; self.st('zunfold')
        self.st('zcells')
        self.after_z(birth=not touched)
        return 1
    def unfold_into_Z(self):
        """move the rightmost mover from gs to the bottom of Z (as cells)"""
        gs,Z=self.gs,self.Z
        if not gs: raise RuntimeError('no movers left to unfold')
        g=gs.pop_first()
        Zc=['X']; push_mover(Zc,g)
        for it in Z[1:]:
            if isinstance(it,int): push_gap(Zc,it)
            else: push(Zc,int(it))
        Z[:]=Zc
        if not gs:
            # no movers left: Z joins Y
            self.merge_Z_live()
    def merge_Z_live(self):
        # Z's items move onto Y; Z stays as the same list object but now only 'X'... the running local sim uses Z as
        # its left stack, so we move Y's content under Z instead: Z := Y + Z items, Y := ['B'] (Y keeps nothing)
        Y,Z=self.Y,self.Z
        items=Z[1:]
        Z[:]=Y[:]
        for it in items:
            if isinstance(it,int): push_gap(Z,it)
            else: push(Z,int(it))
        Y[:]=['B']; self.swapped=True
    def after_z(self,birth):
        Y,gs,Z=self.Y,self.gs,self.Z
        if getattr(self,'swapped',False):
            self.Y[:]=self.Z[:]; self.Z[:]=['X']; self.swapped=False; return
        if len(Z)>1 and isinstance(Z[1],int) and gs:
            gs.add_first(Z[1]); del Z[1]
        if birth and walk_form(Z):
            # the head no longer crosses the movers: they are static now
            Y.append(('M',self.gs)); self.gs=Movers(); self.merge_Z(); self.st('birth')

def to_cells(sim):
    out=[]
    def items(st, stop):
        for t in reversed(st):
            if t==stop: break
            yield t
    def emit(t):
        if isinstance(t,int): out.extend([1,0]*t)
        elif isinstance(t,tuple):
            for g in t[1].gaps():
                out.extend([1,0]*g); out.extend([0,1,1,0,0])
        else: out.append(int(t))
    for t in items(sim.Z,'X'): emit(t)
    for g in sim.gs.gaps(): out.extend([1,0]*g); out.extend([0,1,1,0,0])
    for t in items(sim.Y,'B'): emit(t)
    out.reverse(); return out


# ---------------------------------------------------------------- command line
def rle(xs):
    out = []; i = 0
    while i < len(xs):
        best = None
        for L in (1, 2, 3):
            g = xs[i:i + L]; r = 1
            while xs[i + r * L:i + (r + 1) * L] == g: r += 1
            if r >= 2 and (best is None or r * L > best[0] * len(best[1])): best = (r, g)
        if best:
            out.append(('(%s)^%d' if len(best[1]) > 1 else '%s^%d') % (' '.join(map(str, best[1])), best[0]))
            i += best[0] * len(best[1])
        else:
            out.append(str(xs[i])); i += 1
    return ' '.join(out)

def dump(k):
    import os, subprocess
    here = os.path.dirname(os.path.abspath(__file__))
    exe = os.path.join(here, '../c/dump')
    if not os.path.exists(exe):
        subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(here, '../c/dump.c')], check=True)
    out = subprocess.run([exe, MACH, str(k)], capture_output=True, text=True).stdout.split()
    return out[0], out[1], int(out[2]), int(out[4]), [int(c) for c in out[5]]

def start():
    k, st, hp, hi, cells = dump(273791)      # a right-end turn of the rebuild after the drain end at 272,814
    assert st == 'E' and hp == hi
    return Sim(cells[:-1], int(k))

def strip(x):
    i = 0
    while i < len(x) and x[i] == 0: i += 1
    return x[i:]

if __name__ == '__main__':
    import sys, time
    mode = sys.argv[1]
    S = start(); t0 = time.time()
    if mode == 'check':
        nb = int(sys.argv[2]); n = 0
        while n < nb: n += S.bounce()
        k, st, hp, hi, cells = dump(S.steps)
        same = strip(to_cells(S)) == strip(cells[:-1]) and st == 'E' and hp == hi
        print('step', S.steps, 'bounces', n, S.stats)
        print('tape equal to direct simulation' if same else 'TAPE DIFFERS', '(%d cells)' % len(strip(cells[:-1])))
    else:
        stop = float(sys.argv[2])
        try:
            while S.steps < stop:
                if len(S.Z) == 1 and len(S.Y) <= 12 and S.gs and S.gs.first() < 2:
                    blocks = [g + 2 for g in S.gs.gaps()][::-1]
                    i = 0
                    while i < len(blocks) and blocks[i] == 3: i += 1
                    print('drain end at step', S.steps, '| reservoir', i, '| list', rle(blocks[i:-1]), '1',
                          '| %.0fs' % (time.time() - t0), flush=True)
                S.bounce()
            print('no halt to step', S.steps, S.stats)
        except Halt as e:
            print('HALT near step', S.steps, e.args)
