"""Concrete simulation on run-length tapes with shift rules (symtm) and machine-specific jump rules.
A side is a list of segments: ('R', bit, n) a run of n>=1 equal cells, ('A', first, n) n alternating cells.
Canonical: runs of length>=2 are R, maximal stretches of single cells are A (n>=2), or R with n=1 alone."""
import sys
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools.symtm import Config, Rep, Blank, Lin, try_cross, try_rotate, step, Halted
from bbtools.machine import Machine, STATES

def seg_cells_runs(segs):
    """-> list of (bit, len) runs; A segments expanded lazily as ('A',f,n) kept"""
    out = []
    for s in segs:
        out.append(s)
    return out

def canon_side(segs):
    # first expand to a list of (bit,len) where A becomes marker entries
    runs = []  # elements: [bit, len] or ['A', f, n]
    def push_run(b, n):
        if n <= 0: return
        if runs and runs[-1][0] == b and len(runs[-1]) == 2:
            runs[-1][1] += n
        elif runs and runs[-1][0] == 'A' and runs[-1][1] ^ ((runs[-1][2] - 1) & 1) == b:
            # A ends with bit b: last cell merges into this run
            a = runs[-1]
            a[2] -= 1
            if a[2] == 0: runs.pop()
            push_run(b, n + 1)
        else:
            runs.append([b, n])
    def push_alt(f, n):
        if n <= 0: return
        if n == 1: push_run(f, 1); return
        # if previous run is same bit f: the first cell merges
        if runs and len(runs[-1]) == 2 and runs[-1][0] == f:
            runs[-1][1] += 1; f ^= 1; n -= 1
            if n == 1: push_run(f, 1); return
            if n == 0: return
        if runs and runs[-1][0] == 'A':
            a = runs[-1]; last = a[1] ^ ((a[2] - 1) & 1)
            if last != f:
                a[2] += n; return
        runs.append(['A', f, n])
    for s in segs:
        if s[0] == 'R': push_run(s[1], s[2])
        else: push_alt(s[1], s[2])
    # now convert runs of length 1 sequences into A
    out = []
    for r in runs:
        if len(r) == 2:
            b, n = r
            if n == 1:
                if out and out[-1][0] == 'A' and (out[-1][1] ^ ((out[-1][2] - 1) & 1)) != b:
                    out[-1] = ('A', out[-1][1], out[-1][2] + 1)
                elif out and out[-1][0] == 'R' and out[-1][2] == 1 and out[-1][1] != b:
                    out[-1] = ('A', out[-1][1], 2)
                else:
                    out.append(('R', b, 1))
            else:
                # a run of >=2: if previous A ends with b, steal (already handled in push); 
                out.append(('R', b, n))
        else:
            _, f, n = r
            if out and out[-1][0] == 'A' and (out[-1][1] ^ ((out[-1][2] - 1) & 1)) != f:
                out[-1] = ('A', out[-1][1], out[-1][2] + n)
            elif out and out[-1][0] == 'R' and out[-1][2] == 1 and out[-1][1] != f:
                out[-1] = ('A', out[-1][1], n + 1)
            else:
                out.append(('A', f, n))
    return out

def tokens_to_segs(toks):
    segs = []
    for t in toks:
        if isinstance(t, int): segs.append(('R', t, 1))
        elif isinstance(t, Rep):
            n = t.n.k if hasattr(t.n, 'k') else t.n
            n = t.n.c if False else n
            w = t.word
            if len(set(w)) == 1: segs.append(('R', w[0], len(w) * n))
            elif len(w) == 2: segs.append(('A', w[0], 2 * n))
            elif len(w) % 2 == 0 and all(w[i] != w[i+1] for i in range(len(w)-1)): segs.append(('A', w[0], len(w) * n))
            elif all(w[i] == w[0] for i in range(len(w))): segs.append(('R', w[0], len(w) * n))
            else:
                if n > 64: raise ValueError(f'cannot expand {t}')
                for _ in range(n):
                    for b in w: segs.append(('R', b, 1))
        else: raise ValueError(t)
    return segs

def lin_val(x):
    assert not x.vars(), x
    return x.k

SMALL = 3
def segs_to_tokens(segs, side):
    out = []
    for s in segs:
        if s[0] == 'R':
            if s[2] >= SMALL: out.append(Rep((s[1],), Lin(s[2])))
            else: out.extend([s[1]] * s[2])
        else:
            f, n = s[1], s[2]
            if n >= 2 * SMALL:
                if side == 'L':
                    # keep the cells next to the head literal: rep first, odd cell at the end
                    out.append(Rep((f, 1 - f), Lin(n // 2)))
                    if n % 2: out.append(f)
                else:
                    if n % 2: out.append(f); f ^= 1; n -= 1
                    out.append(Rep((f, 1 - f), Lin(n // 2)))
            else:
                for i in range(n): out.append(f ^ (i & 1))
    return out

class Sim:
    def __init__(self, machine, jumps=()):
        self.m = Machine.parse(machine)
        self.cfg = Config([Blank()], 0, [Blank()])
        self.steps = 0
        self.jumps = jumps
        self.halted = None
    def left_segs(self):
        c = self.cfg
        assert isinstance(c.left[0], Blank)
        return canon_side(tokens_to_segs(c.left[1:]))
    def right_segs(self):
        c = self.cfg
        assert isinstance(c.right[-1], Blank)
        return canon_side(tokens_to_segs(c.right[:-1]))
    def set(self, lsegs, state, rsegs, add_steps=0):
        # strip zeros next to blank
        while lsegs and lsegs[0][0] == 'R' and lsegs[0][1] == 0: lsegs = lsegs[1:]
        while rsegs and rsegs[-1][0] == 'R' and rsegs[-1][1] == 0: rsegs = rsegs[:-1]
        self.cfg = Config([Blank()] + segs_to_tokens(lsegs, 'L'), state, segs_to_tokens(rsegs, 'R') + [Blank()])
        self.steps += add_steps
    def normalize(self):
        self.set(self.left_segs(), self.cfg.state, self.right_segs())
    def move(self):
        for j in self.jumps:
            r = j(self)
            if r: return 'jump'
        c = self.cfg
        c.steps = Lin(0)
        x = try_cross(self.m, c)
        if x is None:
            c2 = c.copy(); rot = try_rotate(c2)
            if rot is not None:
                x = try_cross(self.m, c2)
                if x is not None:
                    self.cfg = c = c2
        if x is None:
            x = self.try_rechunk(c)
            if x is not None:
                c = self.cfg
        if x is None:
            try:
                step(self.m, c)
            except Halted as e:
                self.halted = str(e); self.steps += 1; return 'halt'
        self.steps += lin_val(c.steps)
        self.normalize()
        return 'cross' if x else 'step'
    def try_rechunk(self, c):
        """the repeat next to the head re-cut into copies of a multiple of its word, then a shift rule"""
        for side in ('r', 'l'):
            seq = c.right if side == 'r' else c.left
            if not seq: continue
            t = seq[0] if side == 'r' else seq[-1]
            if not isinstance(t, Rep): continue
            n = lin_val(t.n)
            for mult in (2, 3, 4, 6):
                if n < 2 * mult or len(t.word) * mult > 8: continue
                q, rem = divmod(n, mult)
                big = Rep(t.word * mult, Lin(q))
                lit = list(t.word) * rem
                c2 = c.copy()
                if side == 'r':
                    c2.right = [big] + lit + c2.right[1:]
                else:
                    c2.left = c2.left[:-1] + lit + [big]
                x = try_cross(self.m, c2)
                if x is not None:
                    self.cfg = c2
                    return x
        return None

    def __str__(self):
        def fs(segs):
            return ' '.join((f"{s[1]}^{s[2]}" if s[2] > 1 else f"{s[1]}") if s[0]=='R' else (f"({s[1]}{1-s[1]})^{s[2]//2}" + (f" {s[1]}" if s[2]%2 else '')) for s in segs)
        return fs(self.left_segs()) + f" {STATES[self.cfg.state]}> " + fs(self.right_segs())
