"""Small simulator for exploring MACHINE from synthetic configurations.

Configurations are written like '(101)^5 10 A> 0': cells, (w)^n repeats, the head as 'S>' before the cell it reads.
"""
import re, sys

MACHINE = '1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA'


def parse_machine(m):
    t = []
    for g in m.split('_'):
        row = []
        for i in (0, 3):
            s = g[i:i + 3]
            row.append(None if s[2] == '-' else (int(s[0]), 1 if s[1] == 'R' else -1, ord(s[2]) - 65))
        t.append(row)
    return t


def expand(s):
    out = ''
    for p in s.split():
        if '^' in p:
            w, e = p.split('^')
            out += w.strip('()') * int(e)
        else:
            out += p
    return out


def compress(s, minrep=2):
    """Run-length code a cell string with words of length 1..3 (greedy)."""
    out, i = [], 0
    while i < len(s):
        best = None
        for L in (1, 2, 3):
            w = s[i:i + L]
            if len(w) < L: break
            k = 1
            while s[i + k * L:i + (k + 1) * L] == w: k += 1
            if k >= minrep and k * L > L + 1 and (best is None or k * L > best[1] * len(best[0])): best = (w, k)
        if best:
            w, k = best
            out.append(('(%s)^%d' % (w, k)) if len(w) > 1 else '%s^%d' % (w, k)); i += k * len(w)
        else:
            out.append(s[i]); i += 1
    return ' '.join(out)


class Sim:
    def __init__(self, cfg, machine=MACHINE):
        self.T = parse_machine(machine)
        l, st, r = re.match(r'(.*?)\s*([A-F])>\s*(.*)', cfg).groups()
        L, R = expand(l), expand(r) or '0'
        pad = 4 * (len(L) + len(R)) + 1000
        self.tape = bytearray(pad) + bytearray(int(c) for c in L + R) + bytearray(pad)
        self.h = pad + len(L); self.st = ord(st) - 65; self.lo = pad; self.hi = pad + len(L) + len(R) - 1
        self.steps = 0; self.halted = False

    def run(self, stop, maxsteps):
        T, k = self.T, 0
        while k < maxsteps:
            if self.h <= 0 or self.h >= len(self.tape) - 1:
                n = len(self.tape); self.tape = bytearray(n) + self.tape + bytearray(n)
                self.h += n; self.lo += n; self.hi += n
            tr = T[self.st][self.tape[self.h]]
            if tr is None: self.halted = True; break
            w, d, s = tr; self.tape[self.h] = w; self.h += d; self.st = s; k += 1
            self.lo = min(self.lo, self.h); self.hi = max(self.hi, self.h)
            if stop(self): break
        self.steps += k

    def show(self):
        s = ''.join(map(str, self.tape[self.lo:self.hi + 1])); p = self.h - self.lo
        a = len(s[:p]) - len(s[:p].lstrip('0')); b = s[p + 1:].rstrip('0')
        return (compress(s[a:p]) + ' ' + 'ABCDEF'[self.st] + '> ' + compress(s[p] + b)).strip()


def next_event(cfg, state, side, accept=lambda sim: True, cap=10**7):
    """Run from cfg (one step at least) to the next time the head is in `state` at end `side` ('L'/'R') on a 0
    and accept(sim) holds; returns (shown tape or 'HALT' or '?', steps)."""
    S = ord(state) - 65
    sim = Sim(cfg)
    def stop(m):
        return m.st == S and m.tape[m.h] == 0 and (m.h == m.hi if side == 'R' else m.h == m.lo) and accept(m)
    sim.run(stop, cap)
    if sim.halted: return 'HALT', sim.steps
    if sim.steps >= cap: return '?', sim.steps
    return sim.show(), sim.steps
