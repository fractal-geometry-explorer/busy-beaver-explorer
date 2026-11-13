"""Exact accelerated simulation for a machine whose tape is mostly repeats of one word w (e.g. `10`, `1`, `111010`).

Each side of the head is a list of cells and repeats (w w)^n; the run between two visits of a wall (the head in a
given state at the left or right end of the tape, on blank) is done by `bbtools.symtm.run`, which crosses a repeat
at once when one copy is a shift rule.  At every visit the tape is re-normalised (maximal runs of w become repeats).
Exact: `bscheck.py` compares every visit with the plain C simulator (`tools/c/tmrun.c`).

usage: python3 blocksim.py MACHINE WORD STATE L|R VISITS     the tape at each wall visit, w-runs as (w)^n
"""
import os, sys, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import Config, run, Rep, Lin, Blank, Halted, step as symstep, try_cross
from bbtools.machine import Machine, STATES

class Norm:
    def __init__(self, w, minrep=3):
        self.w = w            # string word, e.g. '10'
        self.minrep = minrep
        self.rx = re.compile('(?:%s){%d,}' % (w, minrep))
    def flatten(self, seq):
        """seq of symtm tokens (no Blank/Ctx) -> list of str and int (int n = w^n)"""
        out = []
        for t in seq:
            if isinstance(t, int): out.append(str(t))
            elif isinstance(t, Rep):
                n = t.n.k; assert t.n.is_const()
                ws = ''.join(map(str, t.word))
                if ws == self.w * (len(ws)//len(self.w)) and len(ws) % len(self.w) == 0:
                    out.append(n * (len(ws)//len(self.w)))
                else:
                    out.append(ws * n)
            else: raise ValueError(t)
        return out
    def merge(self, items):
        # join strings, extract runs, merge ints, absorb literal copies of w next to ints
        res = []
        for it in items:
            if res and isinstance(it, str) and isinstance(res[-1], str): res[-1] += it
            elif res and isinstance(it, int) and isinstance(res[-1], int): res[-1] += it
            else: res.append(it)
        out = []
        for it in res:
            if isinstance(it, str):
                pos = 0
                for m in self.rx.finditer(it):
                    if m.start() > pos: out.append(it[pos:m.start()])
                    out.append((m.end()-m.start())//len(self.w)); pos = m.end()
                if pos < len(it): out.append(it[pos:])
            else: out.append(it)
        # absorb: str ending with w before int; str starting with w after int
        changed = True
        while changed:
            changed = False
            for i in range(len(out)):
                if isinstance(out[i], int):
                    if i > 0 and isinstance(out[i-1], str) and out[i-1].endswith(self.w):
                        out[i-1] = out[i-1][:-len(self.w)]; out[i] += 1; changed = True
                    if i+1 < len(out) and isinstance(out[i+1], str) and out[i+1].startswith(self.w):
                        out[i+1] = out[i+1][len(self.w):]; out[i] += 1; changed = True
            out2 = []
            for it in out:
                if it == '' : changed = True; continue
                if out2 and isinstance(it, int) and isinstance(out2[-1], int): out2[-1] += it; changed=True
                elif out2 and isinstance(it, str) and isinstance(out2[-1], str): out2[-1] += it; changed=True
                else: out2.append(it)
            out = out2
        return out
    def tokens(self, items):
        toks = []
        w = tuple(map(int, self.w))
        for it in items:
            if isinstance(it, str): toks.extend(int(ch) for ch in it)
            else:
                # use doubled word for crossing (period-2 shift rules), remainder literal
                toks.append(Rep(w + w, Lin(it // 2)))
                if it % 2: toks.extend(w)
        return toks
    def norm_side(self, seq, left):
        assert isinstance(seq[0 if left else -1], Blank)
        body = seq[1:] if left else seq[:-1]
        items = self.merge(self.flatten(body))
        # strip zeros next to blank
        if items and isinstance(items[0 if left else -1], str):
            s = items[0 if left else -1]
            s = s.lstrip('0') if left else s.rstrip('0')
            if left: items[0] = s
            else: items[-1] = s
            items = [x for x in items if x != '']
        toks = self.tokens(items)
        return [Blank()] + toks if left else toks + [Blank()]
    def items_str(self, cfg):
        L = self.merge(self.flatten(cfg.left[1:])); R = self.merge(self.flatten(cfg.right[:-1]))
        f = lambda it: (' '.join(it) if isinstance(it, str) else '(%s)^%d' % (self.w, it))
        return ' '.join(map(f, L)) + ' %s> ' % STATES[cfg.state] + ' '.join(map(f, R))

def visit_stop(state, side='R'):
    def stop(c):
        if c.state != state: return False
        if side == 'R':
            return len(c.right) == 1 and isinstance(c.right[0], Blank)
        return len(c.left) == 1 and isinstance(c.left[0], Blank)
    return stop

class BlockSim:
    def __init__(self, M, w, state='A', side='R'):
        self.m = Machine.parse(M); self.norm = Norm(w)
        self.cfg = Config([Blank()], 0, [Blank()], 0)
        self.stop = visit_stop(STATES.index(state), side)
        self.steps = 0
    def next_visit(self, max_moves=10**7):
        c = self.cfg
        c.steps = Lin(0)
        # take at least one move
        first = True
        def stop(cc):
            nonlocal first
            if first: first = False; return False
            return self.stop(cc)
        run(self.m, c, stop, max_moves=max_moves, rotate=True)
        self.steps += c.steps.k
        c.left = self.norm.norm_side(c.left, True); c.right = self.norm.norm_side(c.right, False)
        return c

if __name__ == '__main__':
    M, w, st, side, n = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
    b = BlockSim(M, w, st, side)
    for i in range(n):
        try: b.next_visit()
        except Halted as e:
            print('HALT', e, b.steps); break
        print(b.steps, b.norm.items_str(b.cfg))
