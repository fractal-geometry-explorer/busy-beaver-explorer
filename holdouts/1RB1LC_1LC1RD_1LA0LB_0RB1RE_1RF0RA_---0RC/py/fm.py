"""Frame matcher for py/framemap.py and py/pieces.py (see there)."""

import re, itertools, sys
class FM:
    def __init__(s, M, frames, turns=False):
        s.turns = turns; s.T = {}
        for i, g in enumerate(M.split('_')):
            for b in (0, 1):
                w = g[3*b:3*b+3]; s.T[(i, b)] = None if w[0] == '-' else (int(w[0]), 1 if w[1] == 'R' else -1, ord(w[2]) - 65)
        s.frames = {}
        for name, tmpl in frames.items():
            toks = tmpl.split(); rx = '^0*'; vs = []
            for t in toks:
                if '^' in t:
                    u, v = t.split('^'); rx += '((?:%s)*)' % u; vs.append((v, len(u)))
                elif t in 'ABCDEF': rx += t
                else: rx += t
            rx += '0*$'
            s.frames[name] = (toks, re.compile(rx), vs)
    def build(s, name, P):
        toks = s.frames[name][0]; cells = []; head = None; st = None
        for t in toks:
            if '^' in t:
                u, v = t.split('^'); cells += [int(c) for c in u * P[v]]
            elif t in 'ABCDEF': head = len(cells); st = ord(t) - 65
            else: cells += [int(c) for c in t]
        pad = 3; tape = dict((i + pad, c) for i, c in enumerate(cells))
        return tape, head + pad, st
    def match(s, tape, p, st):
        ks = [k for k, v in tape.items() if v]
        lo = min(ks + [p]); hi = max(ks + [p])
        out = ''.join(str(tape.get(i, 0)) for i in range(lo, p)) + "ABCDEF"[st] + ''.join(str(tape.get(i, 0)) for i in range(p, hi + 1))
        for name, (toks, rx, vs) in s.frames.items():
            m = rx.match(out)
            if m: return name, {v: len(g) // ul for (v, ul), g in zip(vs, m.groups())}
        return None
    def nxt(s, name, P, maxn=10**6):
        tape, p, st = s.build(name, P)
        for n in range(1, maxn):
            t = s.T[(st, tape.get(p, 0))]
            if t is None: return ('HALT', n)
            tape[p] = t[0]; p += t[1]; st = t[2]
            turn = True
            if s.turns:
                t2 = s.T[(st, tape.get(p, 0))]
                turn = not (t2 is not None and t2[1] == t[1])
                if s.turns is True and not turn: continue
            r = s.match(tape, p, st)
            if r and isinstance(s.turns, (set, frozenset, list, tuple)) and r[0] in s.turns and not turn: r = None
            if r: return r + (n,)
        return None
