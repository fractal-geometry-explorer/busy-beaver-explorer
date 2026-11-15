"""qsim: exact accelerated simulator for 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC--- (block queue).
Level 1: rope machine with macro rules for (01)^n, b=00110 and (b (01)^n)^q.
Level 2/3: linear extrapolation of cycles of samples (head at the right end in state B), post-validated.
"""
import sys
M = "1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---"
def parse(m):
    T = []
    for g in m.split('_'):
        row = []
        for r in range(2):
            t = g[3 * r:3 * r + 3]
            row.append(None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65))
        T.append(row)
    return T
A, B, C, D, E, F = range(6)
W01 = ('w', '01'); W10 = ('w', '10')
class Halt(Exception):
    pass
class Sim:
    TH = 8      # counts >= TH are "large" in signatures
    TQ = 4
    PMAX = 60
    def __init__(self, m=M, accel=True):
        self.T = parse(m)
        self.L = []; self.R = []; self.s = A; self.steps = 0
        self.accel = accel
        self.hist = []          # samples: (sigid, counts, steps)
        self.sigids = {}
        self.njump = 0; self.nsample = 0; self.nraw = 0
        self.pending = None
        self.halted = False
        self.log = None
        self.nojump_until = -1
    # ---------------- stacks
    def push_L(self, x):
        L = self.L
        if x == 1:
            if L and L[-1] == 0:
                L.pop(); self.push_L(('w', '01', 1))
            else:
                L.append(1)
        elif x == 0:
            if not L:
                return
            if len(L) >= 3 and L[-1] == 1 and L[-2] == ('w', '01', 1) and L[-3] == 0:
                del L[-3:]; L.append(('b',))
            else:
                L.append(0)
        elif x[0] == 'w':
            if x[1] == '01':
                if L and type(L[-1]) is tuple and L[-1][0] == 'w' and L[-1][1] == '01':
                    L[-1] = ('w', '01', L[-1][2] + x[2])
                else:
                    L.append(x)
            else:  # '10'
                if L and L[-1] == 0:
                    L.pop(); self.push_L(('w', '01', x[2])); L.append(0)
                elif not L:
                    L.append(1)
                    if x[2] > 1: L.append(('w', '01', x[2] - 1))
                    L.append(0)
                elif type(L[-1]) is tuple and L[-1][0] == 'w' and L[-1][1] == '10':
                    L[-1] = ('w', '10', L[-1][2] + x[2])
                else:
                    L.append(x)
        else:
            L.append(x)
    def push_R(self, x):
        R = self.R
        if x == 1:
            if R and R[-1] == 0:
                R.pop(); self.push_R(('w', '10', 1))
            else:
                R.append(1)
        elif x == 0:
            if R:
                R.append(0)
        elif x[0] == 'w':
            if x[1] == '10':
                if R and type(R[-1]) is tuple and R[-1][0] == 'w' and R[-1][1] == '10':
                    R[-1] = ('w', '10', R[-1][2] + x[2])
                else:
                    R.append(x)
            else:  # (01)^n placed left of R's top
                if R and R[-1] == 0:
                    R.pop(); self.push_R(('w', '10', x[2])); R.append(0)
                elif not R:
                    # (01)^n then blank = 0 (10)^(n-1) 1
                    R.append(1)
                    if x[2] > 1: R.append(('w', '10', x[2] - 1))
                    R.append(0)
                elif type(R[-1]) is tuple and R[-1][0] == 'w' and R[-1][1] == '01':
                    R[-1] = ('w', '01', R[-1][2] + x[2])
                else:
                    R.append(x)
        else:
            R.append(x)
    def pop_L(self):
        L = self.L
        while True:
            if not L:
                return 0
            x = L.pop()
            if type(x) is int:
                return x
            if x[0] == 'w':
                if x[2] > 1: L.append(('w', x[1], x[2] - 1))
                L.append(int(x[1][0]))
                return int(x[1][1])
            if x[0] == 'b':
                L.append(0); L.append(('w', '01', 1)); L.append(1)
                return 0
            if x[0] == 'S':
                if x[2] > 1: L.append(('S', x[1], x[2] - 1))
                L.append(('b',))
                if x[1] > 0: L.append(('w', '01', x[1]))
                continue
            raise ValueError(x)
    def pop_R(self):
        R = self.R
        while True:
            if not R:
                return 0
            x = R.pop()
            if type(x) is int:
                return x
            if x[0] == 'w':
                if x[2] > 1: R.append(('w', x[1], x[2] - 1))
                R.append(int(x[1][1]))
                return int(x[1][0])
            if x[0] == 'U':
                if x[2] > 1: R.append(('U', x[1], x[2] - 1))
                if x[1] > 0: R.append(('w', '10', x[1]))
                return 1
            raise ValueError(x)
    # ---------------- one (macro) step
    def step(self):
        R = self.R; L = self.L; s = self.s
        if s == C and R:
            top = R[-1]
            if type(top) is tuple:
                if top[0] == 'w' and top[1] == '10':
                    R.pop(); self.push_L(('w', '01', top[2])); self.steps += 2 * top[2]; return
                if top[0] == 'U' and top[1] >= 2:
                    R.pop(); n = top[1] - 2; q = top[2]
                    if L and type(L[-1]) is tuple and L[-1][0] == 'S' and L[-1][1] == n:
                        L[-1] = ('S', n, L[-1][2] + q)
                    else:
                        L.append(('S', n, q))
                    self.steps += q * (5 + 2 * n); return
            elif top == 1 and len(R) >= 2 and type(R[-2]) is tuple and R[-2][0] == 'w' and R[-2][1] == '10' and R[-2][2] >= 2:
                R.pop(); k = R.pop()[2]
                L.append(('b',))
                if k > 2: R.append(('w', '10', k - 2))
                self.steps += 5; return
        x = self.pop_R()
        t = self.T[s][x]
        if t is None:
            self.push_R(x) if (x or R) else None
            self.halted = True
            raise Halt()
        w, d, s2 = t
        self.steps += 1
        self.s = s2
        if d == 1:
            self.push_L(w)
        else:
            self.push_R(w)
            if s2 == D:
                while L:
                    top = L[-1]
                    if type(top) is not tuple: break
                    if top[0] == 'w':
                        if top[1] != '01': break
                        L.pop(); self.push_R(('w', '10', top[2])); self.steps += 2 * top[2]
                    elif R and type(R[-1]) is tuple and R[-1][0] == 'w' and R[-1][1] == '10':
                        k = R[-1][2]
                        if top[0] == 'b':
                            L.pop(); R.pop()
                            if k > 1: R.append(('w', '10', k - 1))
                            R.append(1); R.append(('w', '10', 3)); self.steps += 21
                        elif top[0] == 'S':
                            n, q = top[1], top[2]
                            L.pop(); R.pop()
                            if n + k - 1 > 0: R.append(('w', '10', n + k - 1))
                            R.append(1)
                            if q > 1: R.append(('U', n + 2, q - 1))
                            R.append(('w', '10', 3)); self.steps += q * (2 * n + 21)
                        else: break
                    else: break
            y = self.pop_L()
            self.push_R(y)
    def at_end(self):
        if self.s != B: return False
        R = self.R
        if not R: return True
        if len(R) <= 2 and all(x == 0 for x in R):
            del R[:]; return True
        return False
    # ---------------- resting tape
    def canon(self):
        L = self.L; out = []
        i = 0; n = len(L)
        while i < n:
            x = L[i]
            if x == ('b',):
                if i + 1 < n and type(L[i + 1]) is tuple and L[i + 1][0] == 'w' and L[i + 1][1] == '01':
                    y = ('S', L[i + 1][2], 1); i += 2
                else:
                    y = ('S', 0, 1); i += 1
            else:
                y = x; i += 1
            if type(y) is tuple and y[0] == 'S' and out and type(out[-1]) is tuple and out[-1][0] == 'S' and out[-1][1] == y[1]:
                out[-1] = ('S', y[1], out[-1][2] + y[2])
            else:
                out.append(y)
        self.L = out
    def cells(self, maxlen=10**7):
        out = []
        for x in self.L:
            if type(x) is int: out.append(str(x))
            elif x[0] == 'w': out.append(x[1] * x[2])
            elif x[0] == 'b': out.append('00110')
            elif x[0] == 'S': out.append(('00110' + '01' * x[1]) * x[2])
        return ''.join(out)
    def show(self):
        out = []
        for x in self.L:
            if type(x) is int: out.append(str(x))
            elif x[0] == 'w': out.append(('a' if x[1] == '01' else 'A') + ('^%d' % x[2] if x[2] > 1 else ''))
            elif x[0] == 'b': out.append('b')
            elif x[0] == 'S':
                inner = 'b' + (' a^%d' % x[1] if x[1] > 1 else (' a' if x[1] == 1 else ''))
                out.append('(%s)^%d' % (inner, x[2]) if x[2] > 1 else inner)
        return ' '.join(out)
    def sig_counts(self):
        TH = self.TH; TQ = self.TQ
        sig = []; cnt = []
        for x in self.L:
            if type(x) is int: sig.append(x)
            elif x[0] == 'w':
                n = x[2]
                if n < TH: sig.append((x[1], n))
                else: sig.append((x[1], 'N', n & 1)); cnt.append(n)
            elif x[0] == 'S':
                n, q = x[1], x[2]
                sn = n if n < TH else ('N', n & 1)
                sq = q if q < TQ else 'Q'
                sig.append(('S', sn, sq))
                if n >= TH: cnt.append(n)
                if q >= TQ: cnt.append(q)
            else: sig.append(x)
        return tuple(sig), cnt
    def set_counts(self, cnt):
        TH = self.TH; TQ = self.TQ
        it = iter(cnt); L = self.L
        for i, x in enumerate(L):
            if type(x) is int: continue
            if x[0] == 'w':
                if x[2] >= TH: L[i] = ('w', x[1], next(it))
            elif x[0] == 'S':
                n, q = x[1], x[2]
                if n >= TH: n = next(it)
                if q >= TQ: q = next(it)
                L[i] = ('S', n, q)
    # ---------------- run to the next sample (head at the right end, state B)
    def trip(self):
        while True:
            self.step()
            if self.at_end():
                break
        self.nraw += 1
        self.canon()
    def sample(self):
        sig, cnt = self.sig_counts()
        sid = self.sigids.setdefault(sig, len(self.sigids))
        self.hist.append((sid, cnt, self.steps))
        self.nsample += 1
    def try_jump(self):
        h = self.hist; t = len(h) - 1
        if self.pending is not None: return False
        if self.nsample <= self.nojump_until: return False
        sid = h[t][0]
        for p in range(1, min(self.PMAX, t // 3) + 1):
            if h[t - p][0] != sid or h[t - 2 * p][0] != sid or h[t - 3 * p][0] != sid: continue
            ok = True
            for i in range(1, p):
                a = h[t - i][0]
                if h[t - i - p][0] != a or h[t - i - 2 * p][0] != a: ok = False; break
            if not ok: continue
            c0, c1, c2, c3 = h[t][1], h[t - p][1], h[t - 2 * p][1], h[t - 3 * p][1]
            d = [x - y for x, y in zip(c0, c1)]
            if d != [x - y for x, y in zip(c1, c2)] or d != [x - y for x, y in zip(c2, c3)]: continue
            # the intermediate samples must move by the same deltas too
            for i in range(1, p):
                di = [x - y for x, y in zip(h[t - i][1], h[t - i - p][1])]
                if di != [x - y for x, y in zip(h[t - i - p][1], h[t - i - 2 * p][1])]: ok = False; break
            if not ok: continue
            s0, s1, s2, s3 = h[t][2], h[t - p][2], h[t - 2 * p][2], h[t - 3 * p][2]
            D1 = s0 - s1; D2 = (s0 - s1) - (s1 - s2)
            if D2 != (s1 - s2) - (s2 - s3): continue
            if not any(d): continue
            J = None
            for c, dd in zip(c0, d):
                if dd < 0:
                    j = (c - self.TH - 2 * (-dd) - 2) // (-dd)
                    J = j if J is None else min(J, j)
            if J is None:
                continue   # nothing decreases: unbounded growth pattern, do not extrapolate
            J -= 1
            if J < 2: continue
            self.do_jump(p, J, d, D1, D2)
            return True
        return False
    def do_jump(self, p, J, d, D1, D2):
        h = self.hist; t = len(h) - 1
        snap = (list(self.L), self.steps, list(h), self.nsample, self.njump)
        c0 = h[t][1]
        self.set_counts([c + J * dd for c, dd in zip(c0, d)])
        self.steps += J * D1 + (J * (J + 1) // 2) * D2
        self.njump += 1
        cyc = [h[t - p + i][0] for i in range(1, p + 1)]   # sigs of the next p samples expected
        self.pending = {'snap': snap, 'p': p, 'J': J, 'd': d, 'cyc': cyc, 'i': 0, 'D1': D1 + J * D2, 'D2': D2,
                        'start': None}
        self.hist = []
        self.sample()
        self.pending['start'] = self.hist[-1]
        if self.log: self.log('jump p=%d J=%d steps=%d' % (p, J, self.steps))
    def check_pending(self):
        pd = self.pending
        if pd is None: return
        i = pd['i']; sid = self.hist[-1][0]
        if sid != pd['cyc'][i]:
            return self.rollback()
        pd['i'] += 1
        if pd['i'] == pd['p']:
            st = pd['start']; cur = self.hist[-1]
            if [x - y for x, y in zip(cur[1], st[1])] != pd['d'] or cur[2] - st[2] != pd['D1'] + pd['D2']:
                return self.rollback()
            self.pending = None
    def rollback(self):
        pd = self.pending
        self.L, self.steps, self.hist, self.nsample, self.njump = pd['snap']
        self.L = list(self.L); self.hist = list(self.hist)
        self.R = []; self.s = B
        self.pending = None
        J = pd['J'] // 2
        if self.log: self.log('rollback, J -> %d' % J)
        if J >= 2:
            self.do_jump(pd['p'], J, pd['d'], pd['D1'] - pd['J'] * pd['D2'], pd['D2'])
        else:
            self.nojump_until = self.nsample + 3 * pd['p'] + 2
    def run(self, max_steps=None, max_samples=None):
        """run until the step count reaches max_steps (stops at the first sample at or beyond it)"""
        n = 0
        while True:
            self.trip()
            self.sample()
            self.check_pending()
            if self.accel:
                self.try_jump()
            n += 1
            if max_steps is not None and self.steps >= max_steps: return
            if max_samples is not None and n >= max_samples: return
def start():
    s = Sim()
    return s
if __name__ == "__main__":
    import time
    N = int(float(sys.argv[1]))
    s = Sim(accel=(len(sys.argv) < 3 or sys.argv[2] != 'raw'))
    t0 = time.time()
    try:
        s.run(max_steps=N)
    except Halt:
        print('HALT at step', s.steps + 1)
    print('steps', s.steps, 'samples', s.nsample, 'raw trips', s.nraw, 'jumps', s.njump, 'sec %.1f' % (time.time() - t0))
    print(s.show()[-600:])
