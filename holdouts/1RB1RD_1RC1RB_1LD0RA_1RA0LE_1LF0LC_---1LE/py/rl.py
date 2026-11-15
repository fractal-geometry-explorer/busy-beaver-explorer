"""rl.py: an exact run-length simulator with big counts (Python ints).

The tape is two stacks (left of the head, and from the head rightwards); an item is a bit (0/1) or a run [word, count]
with word a tuple of cells in tape order.  A run is crossed at once when the head, entering one copy of its word from
the near side, leaves it on the far side in the same state (the copy is rewritten uniformly).  Bits left behind are
folded into runs of the words in `words` (and their rotations).  Exactness does not depend on the folding.
"""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
from bbtools.machine import Machine, STATES

class Halt(Exception): pass

class RL:
    def __init__(self, machine, words=('011','100'), state=0):
        self.m = Machine.parse(machine) if isinstance(machine,str) else machine
        self.tab = self.m.table
        ws=set()
        for w in words:
            for r in range(len(w)): ws.add(tuple(int(x) for x in w[r:]+w[:r]))
        self.words=ws; self.wl=len(next(iter(ws)))
        assert all(len(w)==self.wl for w in ws)
        self.L=[]; self.R=[]   # stacks; top (end of list) nearest the head; R top is the cell under the head
        self.state=state; self.steps=0
        self.cache={}
    # ---- shift rule for a word
    def _cross(self, st, w, d):
        key=(st,w,d); r=self.cache.get(key)
        if r is None:
            c=list(w); n=0; i=0 if d==1 else len(c)-1; s=st; r=False
            while 0<=i<len(c) and n<1000:
                t=self.tab[s][c[i]]
                if t is None: break
                c[i],mv,s=t; i+=mv; n+=1
            else:
                if n<1000 and s==st and ((d==1 and i>=len(c)) or (d==-1 and i<0)): r=(tuple(c),n)
            self.cache[key]=r
        return r
    def _push(self, stk, item, left):
        """push a bit or run onto a stack and fold. `left`: stk is the left stack (tape order = list order);
        for the right stack the list order is reversed tape order."""
        if isinstance(item,list):
            if stk and isinstance(stk[-1],list) and stk[-1][0]==item[0]: stk[-1][1]+=item[1]
            else: stk.append(item)
            return
        stk.append(item)
        wl=self.wl
        # top wl bits form a word equal to the run beneath?
        if len(stk)>wl and isinstance(stk[-wl-1],list):
            ok=True
            for q in range(1,wl+1):
                if isinstance(stk[-q],list): ok=False;break
            if ok:
                w=tuple(stk[-wl:]) if left else tuple(stk[-1:-wl-1:-1])
                if stk[-wl-1][0]==w:
                    del stk[-wl:]; stk[-1][1]+=1; return
        if len(stk)>=2*wl:
            for q in range(1,2*wl+1):
                if isinstance(stk[-q],list): return
            if left: w=tuple(stk[-wl:]); w2=tuple(stk[-2*wl:-wl])
            else: w=tuple(stk[-1:-wl-1:-1]); w2=tuple(stk[-wl-1:-2*wl-1:-1])
            if w==w2 and w in self.words:
                del stk[-2*wl:]
                if stk and isinstance(stk[-1],list) and stk[-1][0]==w: stk[-1][1]+=2
                else: stk.append([w,2])
    def step(self):
        """one macro step: a single transition, or a run crossed"""
        st=self.state
        if self.R and isinstance(self.R[-1],list):
            run=self.R[-1]; r=self._cross(st,run[0],1)
            if r:
                self.R.pop(); self.steps+=r[1]*run[1]; self._push(self.L,[r[0],run[1]],True); return
            if run[1]>=2 and len(run[0])==self.wl:
                r=self._cross(st,run[0]+run[0],1)
                if r:
                    h=run[1]//2; self.steps+=r[1]*h
                    if run[1]&1: run[1]=1
                    else: self.R.pop()
                    a,b=r[0][:self.wl],r[0][self.wl:]
                    if a==b: self._push(self.L,[a,2*h],True)
                    else: self._push(self.L,[r[0],h],True)
                    return
            # peel one copy
            w=run[0]; run[1]-=1
            if run[1]==0: self.R.pop()
            for b in reversed(w): self.R.append(b)
        y=self.R.pop() if self.R else 0
        t=self.tab[st][y]
        if t is None:
            self.R.append(y); self.steps+=1; raise Halt()
        wr,mv,ns=t; self.state=ns; self.steps+=1
        if mv==1:
            self._push(self.L,wr,True)
        else:
            self._push(self.R,wr,False)
            # move left: bring the cell left of the head to the top of R; if L top is a run, try crossing leftwards
            while True:
                if not self.L: self.R.append(0); return
                top=self.L[-1]
                if isinstance(top,list):
                    r=self._cross(self.state,top[0],-1)
                    if r:
                        self.L.pop(); self.steps+=r[1]*top[1]; self._push(self.R,[r[0],top[1]],False); continue
                    if top[1]>=2 and len(top[0])==self.wl:
                        r=self._cross(self.state,top[0]+top[0],-1)
                        if r:
                            h=top[1]//2; self.steps+=r[1]*h
                            if top[1]&1: top[1]=1
                            else: self.L.pop()
                            a,b=r[0][:self.wl],r[0][self.wl:]
                            if a==b: self._push(self.R,[a,2*h],False)
                            else: self._push(self.R,[r[0],h],False)
                            continue
                    w=top[0]; top[1]-=1
                    if top[1]==0: self.L.pop()
                    self.L.extend(w)
                self.R.append(self.L.pop()); return
    def at_right_end(self):
        return not self.R
    def segs(self):
        """left stack as list of str / (word-str,count), left to right, leading zeros stripped"""
        out=[]; cur=[]
        for it in self.L:
            if isinstance(it,list):
                if cur: out.append(''.join(map(str,cur))); cur=[]
                out.append((''.join(map(str,it[0])),it[1]))
            else: cur.append(it)
        if cur: out.append(''.join(map(str,cur)))
        return out
    def show(self):
        s=[]
        for it in self.segs():
            s.append(it if isinstance(it,str) else '(%s)^%d'%it)
        r=[]
        for it in reversed(self.R):
            r.append(str(it) if not isinstance(it,list) else '(%s)^%d'%(''.join(map(str,it[0])),it[1]))
        return ' '.join(s)+' %s> '%STATES[self.state]+' '.join(r)
    def next_visit(self, state=0):
        while True:
            self.step()
            if self.state==state and not self.R: return

if __name__=='__main__':
    M=sys.argv[1]; n=int(sys.argv[2])
    r=RL(M)
    for i in range(n):
        r.next_visit(); print(i+1,r.steps,r.show())
