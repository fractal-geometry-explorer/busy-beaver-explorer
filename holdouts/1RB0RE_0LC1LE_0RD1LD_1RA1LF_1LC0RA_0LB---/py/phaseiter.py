"""Exact phase-by-phase run of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- from blank tape, with exact integers.

usage: python3 phaseiter.py [PHASES] [--log FILE] [--check N]

A phase starts at PS(D, Z) = `0^inf D 0^Z 1 0 0 E> 0^inf` (README.md).  Its first 41 steps (`start`) and the
sweeps (`sweeps`) are Lean theorems for any tape left of the zeros: with Z = 4j + 8 + r, 0 <= r < 4, they lead to

    0^inf D 0^(4+r) 1 0 0 0 (100)^(2j+1) 0 A> 0^inf

in 41 + sum_{i<j} (18(2i+1) + 64) steps.  From there this program runs the machine on the run-length coded tape
with the shift rules of tools/py/bbtools/symtm.py (a repeat (w)^k is crossed in one move when one copy takes the
head across it in the same state; the counts are plain integers here, so every move is an exact run of the
machine) until the next phase start: the head in state E on blank tape just right of `1 0 0`, with a run of zeros
longer than the word on its left.  No extrapolation: each phase is the machine itself, accelerated.  A halt would
be reported with its phase and word.

Output: every phase whose word D has a new *shape* (the word with its long repeat counts replaced by letters), and a
summary.  `--check N` first compares the first N phases with py/phases.py's list of phase starts from the plain
machine, and with the plain machine (c/nextps.c) on the phases whose Z is small.
"""
import argparse
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402
from bbtools import symtm  # noqa: E402
from bbtools.symtm import Rep, Blank, Config, Lin  # noqa: E402

M = "1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---"
MACH = Machine.parse(M)
E = 4


def cnt(t):
    return t.n.k


def cells(tokens):
    """Total cell count of a token list (ints and constant Reps)."""
    return sum(1 if isinstance(t, int) else len(t.word) * cnt(t) for t in tokens)


def compress(tokens, minrep=4):
    """Normal form of a word given as cells and constant repeats: literal stretches are re-bracketed into repeats
    of words of length 1..3 when at least `minrep` copies are in a row, adjacent repeats of one word merge, and a
    repeat absorbs literal copies of its word on either side.  The cells are unchanged."""
    # flatten to blocks (word, count); literals are (cell,), 1
    blocks = []
    for t in tokens:
        if isinstance(t, int):
            blocks.append(((t,), 1))
        elif cnt(t) > 0:
            blocks.append((t.word, cnt(t)))
    # literal runs into a cell string, re-split periodically
    out = []
    lit = []

    def flush():
        i = 0
        s = lit
        while i < len(s):
            best = None
            for p in (1, 2, 3):
                if i + p * minrep > len(s):
                    continue
                k = 1
                while i + (k + 1) * p <= len(s) and s[i + k * p:i + (k + 1) * p] == s[i:i + p]:
                    k += 1
                if k >= minrep and (best is None or k * p > best[0] * best[1]):
                    best = (k, p)
            if best:
                k, p = best
                out.append((tuple(s[i:i + p]), k))
                i += k * p
            else:
                out.append(((s[i],), 1))
                i += 1
        lit.clear()

    for w, k in blocks:
        if len(w) * k <= 12 and k < minrep:
            lit.extend(list(w) * k)
        else:
            flush()
            out.append((w, k))
    flush()
    # merge: same word adjacent; literal copies around a repeat
    changed = True
    while changed:
        changed = False
        res = []
        for w, k in out:
            if res and res[-1][0] == w and (k > 1 or res[-1][1] > 1):
                res[-1] = (w, res[-1][1] + k)
                changed = True
                continue
            res.append((w, k))
        out = res
        # literal cells before a repeat that spell its word (rotated) are absorbed: x (y x)^k -> (x y)^k x
        for i in range(1, len(out)):
            w, k = out[i]
            if k > 1 and len(w) > 1:
                L = len(w)
                if i >= L and all(out[i - L + q][1] == 1 and len(out[i - L + q][0]) == 1 for q in range(L)):
                    pre = tuple(out[i - L + q][0][0] for q in range(L))
                    if pre == w:
                        out[i - L:i + 1] = [(w, k + 1)]
                        changed = True
                        break
            if k > 1 and len(w) == 1 and out[i - 1] == (w, 1):
                out[i - 1:i + 1] = [(w, k + 1)]
                changed = True
                break
    toks = []
    for w, k in out:
        if k == 1 or len(w) * k <= 3:
            toks.extend(list(w) * k)
        else:
            toks.append(Rep(w, Lin(k)))
    return toks


def gaps(tokens):
    """The word as its gaps: the numbers of zeros between consecutive 1s, after the first 1, run-length coded as a
    list [(pattern, count)] (a pattern is a tuple of gaps repeated count times).  Trailing zeros are dropped."""
    out = []          # list of [pattern, count]
    cur = None        # zeros since the last 1 (None before the first 1)

    def emit(pat, k=1):
        if out and out[-1][0] == pat:
            out[-1][1] += k
        else:
            out.append([pat, k])

    for t in tokens:
        if isinstance(t, int):
            w, k = (t,), 1
        else:
            w, k = t.word, cnt(t)
        if 1 not in w:
            if cur is not None:
                cur += len(w) * k
            continue
        ones = [i for i, x in enumerate(w) if x == 1]
        pre, post = ones[0], len(w) - 1 - ones[-1]
        inner = tuple(ones[q + 1] - ones[q] - 1 for q in range(len(ones) - 1))
        # first copy
        if cur is not None:
            emit((cur + pre,))
        for g in inner:
            emit((g,))
        if k > 1:
            per = (post + pre,) + inner
            if len(set(per)) == 1:
                emit((per[0],), len(per) * (k - 1))
            else:
                emit(per, k - 1)
        cur = post
    return [(p, k) for p, k in out]


def gap_text(g, big=None):
    parts = []
    for p, k in g:
        ps = ",".join(("*" if big and x >= big else str(x)) for x in p)
        if len(p) > 1:
            ps = f"[{ps}]"
        if k == 1:
            parts.append(ps)
        else:
            ks = "*" if big and k >= 4 else (str(k) if len(str(k)) < 12 else f"[{len(str(k))} digits]")
            parts.append(f"{ps}^{ks}")
    return " ".join(parts)


def shape(tokens, big=8):
    """The gaps of the word with every gap >= big and every count >= 4 written `*`: the word's structure."""
    return gap_text(gaps(tokens), big)


def show(tokens):
    parts = []
    for t in tokens:
        if isinstance(t, int):
            parts.append(str(t))
        else:
            w = "".join(map(str, t.word))
            k = cnt(t)
            parts.append(f"({w})^{k}" if len(str(k)) < 12 else f"({w})^[{len(str(k))} digits]")
    return " ".join(parts)


def is_ps(c):
    return c.state == E and c.right == [Blank()] and c.left[-3:] == [1, 0, 0]


def sweep_steps(j):
    # sum_{i<j} 18(2i+1) + 64 = 18 j^2 + 64 j
    return 18 * j * j + 64 * j


class Halt(Exception):
    pass


def phase(D, Z, max_moves=10 ** 7):
    """One exact phase from PS(D, Z) (D a token list, Z >= 8).  Returns (D', Z', steps)."""
    r = Z % 4
    j = (Z - 8 - r) // 4
    n = 2 * j + 1
    left = [Blank()] + list(D) + [0] * (4 + r) + [1, 0, 0, 0, Rep((1, 0, 0), Lin(n)), 0]
    c = Config(left, 0, [Blank()])
    steps = 41 + sweep_steps(j)
    while True:
        try:
            c = symtm.run(MACH, c, is_ps, max_moves=max_moves, rotate=True)
        except symtm.Halted as e:
            raise Halt(f"halt ({e}) during the end of the phase, after {steps + c.steps.k} steps of it")
        # the zeros left of `1 0 0`
        body = c.left[1:-3]
        z = 0
        i = len(body)
        while i > 0:
            t = body[i - 1]
            if t == 0:
                z += 1
            elif isinstance(t, Rep) and set(t.word) == {0}:
                z += len(t.word) * cnt(t)
            else:
                break
            i -= 1
        d = body[:i]
        while d and (d[0] == 0 or (isinstance(d[0], Rep) and set(d[0].word) == {0})):
            d = d[1:]                   # blank cells the head visited left of the word
        if z > cells(d) + 8:
            return compress(d), z, steps + c.steps.k
        # not a phase start yet: take one machine step and go on
        symtm.step(MACH, c)


def blank_first():
    """The first phase start from blank tape (step 457; Lean: blank_start): D(2, 0), Z = 15."""
    return compress([0, 1, 0, 0, 1, 0, 1][1:]), 15, 457


def plain_check(nph):
    """Compare with the plain machine: phases.py's list of phase starts and c/nextps.c."""
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, here)
    import phases
    phases.build()
    D, Z, _ = blank_first()
    for i, (_, d, z) in enumerate(phases.BLANK):
        assert flat(D) == d and Z == z, (i, flat(D), d, Z, z)
        D, Z, _ = phase(D, Z)
    print(f"agrees with the plain machine's phase starts from blank tape ({len(phases.BLANK)} phases, step 8.7e7)")
    D, Z, _ = blank_first()
    k = 0
    for i in range(nph):
        D2, Z2, _ = phase(D, Z)
        if Z < 3000:
            out = phases.nextps(flat(D), Z)
            assert out[:2] == (flat(D2), Z2), (i, out, flat(D2), Z2)
            k += 1
        D, Z = D2, Z2
    print(f"{k} phases with Z < 3000 agree with c/nextps.c")


def flat(D):
    return "0" + "".join("".join(map(str, t.word)) * cnt(t) if isinstance(t, Rep) else str(t) for t in D)


def cross_check(nph, every=1):
    """At every `every`-th phase up to nph, run the engine and the plain machine (c/nextps.c) from the same word
    D with a small Z of the same residue mod 8 (just long enough for a phase), and compare the next phase start."""
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, here)
    import phases
    phases.build()
    D, Z, _ = blank_first()
    k = 0
    t0 = time.time()
    for i in range(1, nph + 1):
        if i % every == 0:
            zs = 2 * cells(D) + 40
            zs += (Z - zs) % 8
            D2, Z2, _ = phase(D, zs)
            out = phases.nextps(flat(D), zs)
            assert out[:2] == (flat(D2), Z2), (i, out[:2], flat(D2), Z2)
            k += 1
        D, Z, _ = phase(D, Z)
    print(f"cross-check: at {k} phases up to {nph}, the engine and the plain machine agree on the next phase start "
          f"from the phase's word with a small Z of the same residue mod 8 ({time.time() - t0:.0f} s)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("phases", type=int, nargs="?", default=2000)
    ap.add_argument("--log", default=None)
    ap.add_argument("--check", type=int, default=0)
    ap.add_argument("--events", default=None, help="write every phase where the word's shape changes to this file")
    ap.add_argument("--every", type=int, default=0, help="print a progress line every N phases")
    ap.add_argument("--xcheck", type=int, nargs=2, default=None, metavar=("PHASES", "EVERY"),
                    help="cross-check the engine against the plain machine on the words of the first PHASES phases")
    a = ap.parse_args()
    sys.set_int_max_str_digits(0)
    if a.check:
        plain_check(a.check)
    if a.xcheck:
        cross_check(*a.xcheck)
    D, Z, steps = blank_first()
    seen = {}
    log = open(a.log, "w") if a.log else None
    ev = open(a.events, "w") if a.events else None
    prev = None
    t0 = time.time()
    res = [0] * 8
    for i in range(1, a.phases + 1):
        s = shape(D)
        if s not in seen:
            seen[s] = i
            line = f"phase {i}: Z mod 8 = {Z % 8}, Z has {len(str(Z))} digits, gaps {gap_text(gaps(D))}"
            print(line, flush=True)
        if ev and s != prev:
            ev.write(f"{i} {Z % 64} {len(str(Z))} {gap_text(gaps(D))}\n")
        prev = s
        if log:
            log.write(f"{i} {Z % 64} {len(str(Z))} {gap_text(gaps(D))}\n")
        res[Z % 8] += 1
        try:
            D, Z, st = phase(D, Z)
        except Halt as e:
            print(f"HALT in phase {i}: {e}; D = {show(D)}, Z mod 64 = {Z % 64}")
            return
        steps += st
        if a.every and i % a.every == 0:
            print(f"  .. phase {i}, Z has {len(str(Z))} digits, steps ~10^{len(str(steps)) - 1}, word {len(D)} tokens "
                  f"/ {cells(D)} cells, {time.time() - t0:.0f} s", flush=True)
    print(f"no halt in {a.phases} phases; Z has {len(str(Z))} digits; {len(str(steps))}-digit step count "
          f"(about 10^{len(str(steps)) - 1}); {len(seen)} word shapes; phases by Z mod 8: {res}; "
          f"{time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
