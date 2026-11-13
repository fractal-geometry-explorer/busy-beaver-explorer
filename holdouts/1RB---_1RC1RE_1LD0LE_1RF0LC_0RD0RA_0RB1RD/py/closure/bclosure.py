"""Two-sided closed set: a window around the head, the tape beyond it abstracted on each side.

Machine, event state, node pattern and thresholds from the environment as for pclosure.py; BBDEPTH = chunks kept on
each side.  Seen from the head outwards a side of the tape is  lit0 chunk_1 chunk_2 ...,  a chunk being a big repeat
`(w)^n` (count free, >= BIG) and the literal cells after it.  A class is
    (ctxL, chunksL, lit0L, state, hl, lit0R, chunksR, ctxR)
with at most DEPTH chunks on each side; ctx is '$' (blank beyond) or a chunk c, meaning: beyond comes whatever may
follow c according to the successor relation P of that side (a chunk of P[side, c], or the blank tape if '$' is in
it).  hl: the head stands on the first cell of the left side instead of the first cell of the right side.
A class is run symbolically with a wall cell where a side is open, until the head reaches a wall (the class is then
continued for every successor), a node (a left-end event matching BBNODE) or a halt.  Reached tapes are cut back to
DEPTH chunks; what is cut off goes into P.  Closed: every piece of every class ends in a class of the set, no halt.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..',
                                '1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD', 'py', 'closure'))
import pclosure  # noqa: E402
from pclosure import (BIG, ENV, MAX_MOVES, NODE, Driver, Lin, NeedCmp, NeedSplitVar, Undecided, accel, canon, splits,
                      subst)  # noqa: E402
from paccel import Sim, WallHit  # noqa: E402

for _i in range(6, 40):
    ENV[_i] = 1000000007 + 2 * 3 * 5 * 7 * 11 * 13 * _i + 30 * _i * _i
DEPTH = int(os.environ.get('BBDEPTH', '2'))
LOW = int(os.environ.get('BBLOW', str(BIG)))   # class threshold: a repeat of >= LOW words is free (BIG: the engine's)
pclosure.BIG = LOW
MAXPIECES = int(os.environ.get('BBPIECES', '3000'))


def parse_side(text):
    """(lit0, chunks, walled) of the canonical text of one side."""
    parts = text.split()
    walled = bool(parts) and parts[-1][-1] in '23'
    if walled:
        parts[-1] = parts[-1][:-1]
        if not parts[-1]:
            parts.pop()
    lit0 = ''
    out = []
    for p in parts:
        if p.startswith('('):
            out.append(p)
        elif out:
            out[-1] = out[-1] + ' ' + p
        else:
            lit0 = p
    return lit0, tuple(out), walled


def side_tokens(lit0, chunks, wall, counts):
    out = [int(c) for c in lit0]
    for ch in chunks:
        p = ch.split()
        out.append([tuple(int(c) for c in p[0][1:p[0].index(')')]), next(counts)])
        if len(p) > 1:
            out.extend(int(c) for c in p[1])
    if wall:
        out.append(wall)
    return out


def build(key, counts):
    ctxL, chL, litL, q, hl, litR, chR, ctxR = key
    it = iter(counts)
    s = Sim()
    s.st = q
    Lo = side_tokens(litL, chL, 3 if ctxL != '$' else 0, it)
    Ro = side_tokens(litR, chR, 2 if ctxR != '$' else 0, it)
    s.L = [t if isinstance(t, int) else [tuple(reversed(t[0])), t[1]] for t in reversed(Lo)]
    s.R = list(reversed(Ro))
    s.steps = Lin(0)
    if hl:
        s.R.append(s.popL())
    s.recompress()
    return s


def sides(s):
    Lo = [t if isinstance(t, int) else [tuple(reversed(t[0])), t[1]] for t in reversed(s.L)]
    Ro = list(reversed(s.R))
    return canon(Lo)[0], canon(Ro)[0]


def nvars(key):
    return len(key[1]) + len(key[6])


def show(key):
    ctxL, chL, litL, q, hl, litR, chR, ctxR = key
    return '[%s] %s %s <%s%s> %s %s [%s]' % (ctxL, ' '.join(reversed(chL)), litL, 'ABCDEF'[q], '<' if hl else '',
                                              litR, ' '.join(chR), ctxR)


class B:
    def __init__(self, log=print):
        self.log = log
        self.rules = {}
        self.P = {}              # (side, chunk) -> set of successors
        self.inh = {}
        self.dep = {}            # (side, chunk) -> classes that listed P[side, chunk]
        self.memo = {}           # class -> set of results
        self.classes = {}
        self.todo = []
        self.halts = []
        self.undec = []
        self.nrun = 0

    def add(self, c, e):
        work = [(c, e)]
        while work:
            c, e = work.pop()
            S = self.P.setdefault(c, set())
            if e in S:
                continue
            S.add(e)
            for k in self.dep.get(c, ()):
                if k not in self.todo:
                    self.todo.append(k)
            for a in self.inh.get(c, ()):
                work.append((a, e))

    def inherit(self, a, b):
        if a == b:
            return
        I = self.inh.setdefault(b, set())
        if a in I:
            return
        I.add(a)
        for e in list(self.P.get(b, ())):
            self.add(a, e)

    def cut(self, side, ch, ctx):
        if len(ch) <= DEPTH:
            return ch, ctx
        for i in range(DEPTH - 1, len(ch) - 1):
            self.add((side, ch[i]), ch[i + 1])
        if ctx == '$':
            self.add((side, ch[-1]), '$')
        else:
            self.inherit((side, ch[-1]), (side, ctx))
        return ch[:DEPTH], ch[DEPTH - 1]

    def push(self, ctxL, chL, litL, q, hl, litR, chR, ctxR):
        chL, ctxL = self.cut('L', chL, ctxL)
        chR, ctxR = self.cut('R', chR, ctxR)
        key = (ctxL, chL, litL, q, hl, litR, chR, ctxR)
        if key not in self.classes and key not in self.todo:
            self.todo.append(key)

    def absorb(self, res, cur):
        kind, q, Lt, Rt = res
        ctxL, ctxR = cur[0], cur[7]
        litL, chL, _ = parse_side(Lt)
        litR, chR, _ = parse_side(Rt)
        if kind == 'node':
            self.push(ctxL, chL, litL, q, False, litR, chR, ctxR)
            return
        side = kind
        ctx = ctxL if side == 'L' else ctxR
        self.dep.setdefault((side, ctx), set()).add(cur)
        for e in list(self.P.get((side, ctx), ())):
            add, c2 = ((), '$') if e == '$' else ((e,), e)
            if side == 'L':
                self.push(c2, chL + add, litL, q, True, litR, chR, ctxR)
            else:
                self.push(ctxL, chL, litL, q, False, litR, chR + add, c2)

    def run_leaf(self, key, counts):
        s = build(key, [Lin(c.k, c.c) if isinstance(c, Lin) else c for c in counts])
        d = Driver(s, True)
        d.rules = self.rules
        d.env = ENV
        out = []

        def on_event(d, toks):
            Lt, Rt = sides(d.s)
            if NODE.match(Rt):
                out.append(('node', d.s.st, Lt, Rt))
                return True
            return False

        self.nrun += 1
        try:
            d.run(None, on_event, max_moves=MAX_MOVES)
        except WallHit:
            s = d.s
            w = s.R.pop()
            s.recompress()
            if w == 3:
                assert not s.L
                return ('L', s.st, '', sides(s)[1])
            assert not s.R
            return ('R', s.st, sides(s)[0], '')
        if d.s.halt:
            return ('halt',)
        if not out:
            return ('undecided', 'no node or wall within %d moves' % d.moves)
        return out[0]

    def results(self, key):
        if key in self.memo:
            return self.memo[key]
        res = set()
        t0 = time.time()
        stack = [[Lin(LOW, {i: 1}) for i in range(nvars(key))]]
        n = 0
        while stack:
            counts = stack.pop()
            n += 1
            if n > MAXPIECES:
                res.add(('undecided', 'too many pieces'))
                break
            try:
                r = self.run_leaf(key, counts)
            except (NeedSplitVar, NeedCmp) as e:
                for sub in splits(e):
                    stack.append([subst(c, sub) for c in counts])
                continue
            except Undecided as e:
                r = ('undecided', str(e)[:80])
            if r[0] == 'halt':
                r = ('halt', ' '.join(repr(c) for c in counts))
            res.add(r)
        if time.time() - t0 > 10:
            self.log('slow (%.0f s, %d pieces): %s' % (time.time() - t0, n, show(key)))
        self.memo[key] = res
        return res

    def bfs(self, budget=None, out=None):
        self.todo.append(('$', (), '', 0, False, '', (), '$'))
        t0 = time.time()
        n = 0
        while self.todo:
            if budget and time.time() - t0 > budget:
                self.log('stopped: %d classes left' % len(self.todo))
                break
            key = self.todo.pop(0)
            new = key not in self.classes
            self.classes[key] = 1
            for r in self.results(key):
                if r[0] == 'halt':
                    if new:
                        self.halts.append((key, r[1]))
                        self.log('HALT: %s with counts %s' % (show(key), r[1]))
                elif r[0] == 'undecided':
                    if new:
                        self.undec.append((key, r[1]))
                        self.log('undecided: %s: %s' % (show(key), r[1]))
                else:
                    self.absorb(r, key)
            n += 1
            if n % 50 == 0 or not self.todo:
                self.log('%5d classes, queue %4d, visits %5d, runs %6d, chunks %4d, edges %5d, halts %d, undecided %d, '
                         '%4.0f s | %s' % (len(self.classes), len(self.todo), n, self.nrun, len(self.P),
                                           sum(map(len, self.P.values())), len(self.halts), len(self.undec),
                                           time.time() - t0, show(key)))
        if out:
            json.dump(dict(machine=accel.MACHINE, mirror=accel.MIRROR, big=BIG, low=LOW, depth=DEPTH, node=NODE.pattern,
                           classes=[[list(k), sorted(map(list, v))] for k, v in self.memo.items()],
                           P=[[k[0], k[1], sorted(v)] for k, v in self.P.items()],
                           inherit=[[k[0], k[1], sorted(map(list, v))] for k, v in self.inh.items()],
                           halts=[[list(a), b] for a, b in self.halts],
                           undecided=[[list(a), b] for a, b in self.undec], todo=len(self.todo)), open(out, 'w'))
        return not self.todo and not self.halts and not self.undec


if __name__ == '__main__':
    b = B(log=lambda s: print(s, flush=True))
    ok = b.bfs(budget=float(sys.argv[2]) if len(sys.argv) > 2 else None, out=sys.argv[1])
    print('classes %d, chunks %d, runs %d, halting pieces %d, undecided %d' % (
        len(b.classes), len(b.P), b.nrun, len(b.halts), len(b.undec)))
    print('CLOSED, no halting piece' if ok else 'NOT CLOSED')
