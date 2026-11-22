"""Summaries of the run of 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC at fixed step counts, and its phase table.

usage:  gcc -O2 -o snap c/snap.c && mkdir snaps && ./snap 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC 5e11 1e9 snaps
        python3 py/phases.py snaps/*.txt > evidence/phases-5e11.txt      (about 2 h for the simulation)

Each line: step, leftmost/rightmost visited cell, head and state, then the tape from left to right as its big blocks
(a word repeated, at least 600 cells; greedy compression with periods up to 36) and ~n for n cells of anything else.
Then the phase table: S = left end fixed between two summaries, G = left end moving.  Observation only.
"""
import re, sys, os


def comp(s, maxp=36, minrep=3):
    out = []; i = 0; lit = ''
    while i < len(s):
        best = None
        for p in range(1, maxp + 1):
            w = s[i:i + p]
            if len(w) < p: break
            k = 1
            while s[i + k * p:i + (k + 1) * p] == w: k += 1
            if k >= minrep and (best is None or k * p > best[0] * best[1] + p): best = (k, p)
        if best:
            if lit: out.append(lit); lit = ''
            k, p = best; out.append(f"({s[i:i + p]})^{k}"); i += k * p
        else:
            lit += s[i]; i += 1
    if lit: out.append(lit)
    return out


def summary(path, big=600):
    f = open(path); L, pos, st = f.readline().split(); t = f.readline().strip(); L = int(L)
    out = []; junk = 0
    for tk in comp(t):
        if tk.startswith('('):
            w, k = tk[1:].split(')^'); n = len(w) * int(k)
            if n >= big:
                if junk: out.append(f"~{junk}")
                junk = 0; out.append(tk); continue
            junk += n
        else:
            junk += len(tk)
    if junk: out.append(f"~{junk}")
    return f"L={L} R={L + len(t) - 1} head={pos}{st} :: " + " ".join(out)


FIVE = r"\((11100|11001|10011|00111|01110|01011|10110|01101|11010|10101)\)\^"


def table(lines):
    rows = []
    for line in lines:
        m = re.match(r"(\d+) L=(-?\d+) R=(-?\d+) head=\S+ :: (.*)", line)
        if not m: continue
        toks = m[4].split()
        soup = max([int(t[1:]) for t in toks if t.startswith('~')] + [0])
        a = int(toks[0].split('^')[1]) if toks[0].startswith('(100)^') else 0
        five = sum(int(t.split('^')[1]) for t in toks if re.match(FIVE, t))
        rows.append((int(m[1]), int(m[2]), int(m[3]), a, five, soup))
    out = []; cur = None
    for prev, r in zip(rows, rows[1:]):
        kind = 'S' if r[1] == prev[1] else 'G'
        if cur is None or cur[0] != kind:
            if cur: out.append(cur)
            cur = [kind, prev, r]
        else:
            cur[2] = r
    if cur: out.append(cur)
    res = ["phase from..to (steps): left end; (100)^a; period-5 blocks K (words); largest irregular stretch (cells); right end"]
    for k, s, e in out:
        res.append(f"{k} {s[0]:.3g}..{e[0]:.3g}: L {s[1]}->{e[1]}; a {s[3]}->{e[3]}; K {s[4]}->{e[4]}; irregular {s[5]}->{e[5]}; R {s[2]}->{e[2]}")
    return res


if __name__ == '__main__':
    lines = [os.path.basename(p)[:-4].lstrip('0') + ' ' + summary(p) for p in sorted(sys.argv[1:])]
    print("\n".join(lines)); print(); print("\n".join(table(lines)))
