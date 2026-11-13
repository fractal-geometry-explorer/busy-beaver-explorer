"""The half-phase map of 1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA on (w, k), and its orbit from blank tape.

A half-phase end is `0^inf w (10)^k F> 0^inf` (or `w (01)^k A>`), w a short word.  The next one is
`w' (10)^k'` with k' = (3k + c)/2, where (w', c) depends only on w and the parity of k.  Each table entry is read
off c/halfphase.c (direct simulation) for 12 values of k between 60 and 140 of that parity and must agree for all
of them.  The orbit from blank tape (exact for the first 21 half-phases by direct simulation) is then run with the
table; halting entries are the pairs (w, parity) whose half-phase halts (B reads 1).

usage: python3 wordmap.py orbit N        N half-phases of the orbit, the word states it visits
       python3 wordmap.py check K        the orbit by direct simulation while k < K, against the table
       python3 wordmap.py markov L       the word states reachable from (w='', 10) under any parities (|w| <= L), and
                                         the chance of a halt when the parities are fair coins
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join("/tmp", "halfphase_" + str(os.getuid()))
SRC = os.path.join(HERE, "..", "c", "halfphase.c")
if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(SRC):
    subprocess.run(["gcc", "-O2", "-o", BIN, SRC], check=True)

TAB = {}


def run(cases):
    inp = "".join(f"{w + u * k} {q}\n" for w, u, q, k in cases)
    out = subprocess.run([BIN], input=inp, capture_output=True, text=True).stdout.strip().split("\n")
    res = []
    for line in out:
        f = line.split()
        if f[0] in ("HALT", "LONG"):
            res.append((f[0],))
        else:
            res.append((int(f[0]), ord(f[1]) - 65, f[2][2:], f[3][2:], int(f[4][2:])))
    return res


def entry(w, u, q, par):
    key = (w, u, q, par)
    if key not in TAB:
        ks = [k for k in range(60, 140) if k % 2 == par][:12]
        vals = set()
        for k, r in zip(ks, run([(w, u, q, k) for k in ks])):
            vals.add(r if len(r) == 1 else (r[1], r[2], r[3], 2 * r[4] - 3 * k))
        TAB[key] = vals.pop() if len(vals) == 1 else ("IRREG", sorted(map(str, vals)))
    return TAB[key]


def start():
    w, u, q, k = "", "10", 5, 4
    seq = []
    while k < 60:
        r = run([(w, u, q, k)])[0]
        q, w, u, k = r[1], r[2], r[3], r[4]
        seq.append((w, u, q, k))
    return seq


def orbit(n, keep=True):
    # keep=False: do not store the orbit (needed for long runs: k grows by 0.585 bits per half-phase)
    import collections
    seq = start()
    count = len(seq)
    w, u, q, k = seq[-1]
    visits, near = collections.Counter(), 0
    for _ in range(n):
        e = entry(w, u, q, k & 1)
        visits[(w, u, "AF"[q == 5])] += 1
        if entry(w, u, q, 1 - (k & 1))[0] == "HALT":
            near += 1
        if e[0] in ("HALT", "LONG", "IRREG"):
            print("stops:", w, u, q, k % 2, e)
            break
        q, w, u, c = e
        k = (3 * k + c) >> 1
        count += 1
        if keep or len(seq) < 60:
            seq.append((w, u, q, k))
    for s in seq[:30]:
        print(f"w={s[0]!r:12} ({s[1]})^{s[3]}")
    print(f"... {count} half-phases, no halt; k has {k.bit_length()} bits (about {int(k.bit_length() * 0.30103)} digits)")
    print(f"word states visited: {len(visits)}; times the other parity would have halted: {near}")
    print("most visited:", ", ".join(f"{w!r}:{c}" for (w, u, s), c in visits.most_common(10)))
    return seq


def check(K):
    seq = orbit(200)
    w, u, q, k = "", "10", 5, 4
    i = bad = 0
    while k < K:
        r = run([(w, u, q, k)])[0]
        q, w, u, k = r[1], r[2], r[3], r[4]
        bad += (w, u, q, k) != seq[i]
        i += 1
    print(f"direct simulation: {i} half-phases (k up to {k}) against the table orbit, {bad} mismatches")


def markov(L):
    import numpy as np
    s0 = ("", "10", 5)
    G, todo, seen = {}, [s0], {s0}
    while todo:
        s = todo.pop()
        succ = []
        for par in (0, 1):
            e = entry(*s, par)
            if e[0] == "HALT":
                succ.append("HALT")
                continue
            n = (e[1], e[2], e[0])
            if e[0] in ("LONG", "IRREG") or len(n[0]) > L:
                succ.append("UNK")
                continue
            succ.append(n)
            if n not in seen:
                seen.add(n)
                todo.append(n)
        G[s] = succ
    S = list(G)
    idx = {s: i for i, s in enumerate(S)}
    n = len(S) + 2
    H, U = n - 2, n - 1
    P = np.zeros((n, n))
    for s, ab in G.items():
        for t in ab:
            P[idx[s], H if t == "HALT" else U if t == "UNK" else idx[t]] += 0.5
    P[H, H] = P[U, U] = 1
    halting = [(s[0], par) for s, ab in G.items() for par, t in enumerate(ab) if t == "HALT"]
    print(f"{len(S)} word states reachable with |w| <= {L}; halting entries: {halting}")
    x = np.zeros(n)
    x[idx[s0]] = 1
    Mx = P.copy()
    for e in range(48):
        y = x @ Mx
        if e % 4 == 0 or y[H] > 0.3:
            print(f"P(halt within 2^{e} half-phases) = {y[H]:.3e}   (leaves the states: {y[U]:.1e})")
        if y[H] > 0.999:
            break
        Mx = Mx @ Mx


if __name__ == "__main__":
    cmd, arg = sys.argv[1], int(sys.argv[2])
    {"orbit": orbit, "long": lambda n: orbit(n, keep=False), "check": check, "markov": markov}[cmd](arg)
