"""Lean theorems for single rounds of a run, for every tape further left.  Shared by the G12 machines of this
worker (their gen scripts import this file).

`rounds(machine, state, k0, k1, steps)`: run from blank tape and stop at the moments the head is in `state` on a 0
right of every visited cell (the sample points).  For the sample points with index k0 .. k1-1 and the next one,
the cells the round between them never visits on the left become a context `L`; the rest is written exactly (runs
of length >= 4 as repeats) and `bbtools.symtm.prove` writes the theorem that the start reaches the end in the
counted number of steps, for every L.  Returns a list of (lean_text, start_string, end_string, steps).
"""
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove  # noqa: E402

from fcfg import table  # noqa: E402


def samples(text, state, max_steps, count):
    t = table(text)
    tape, h, s, n, hi = {}, 0, 0, 0, 0
    out = []
    lo_since = 0
    while n < max_steps and len(out) < count:
        x = tape.get(h, 0)
        tr = t[(s, x)]
        if tr is None:
            break
        w, d, s = tr
        tape[h] = w
        h += 1 if d == "R" else -1
        n += 1
        lo_since = min(lo_since, h)
        hi = max(hi, h)
        if s == state and h == hi and tape.get(h, 0) == 0 and tape.get(h - 1, 0) == 1:
            out.append((n, dict(tape), h, lo_since))
            lo_since = h
    return out


def word(cells):
    parts, i = [], 0
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == cells[i]:
            j += 1
        k = j - i
        parts.append(f"{cells[i]}^{k}" if k >= 4 else " ".join(str(cells[i]) for _ in range(k)))
        i = j
    return " ".join(parts)


def rounds(text, state, k0, k1, max_steps=10**8, name="round", max_moves=100000):
    sm = samples(text, state, max_steps, k1 + 1)
    res = []
    for k in range(k0, k1):
        (n0, t0, h0, _), (n1, t1, h1, lo) = sm[k], sm[k + 1]
        a = lo - 1                      # cells a .. stay explicit; left of a is the context L
        st = word([t0.get(i, 0) for i in range(a, h0)])
        en = word([t1.get(i, 0) for i in range(a, h1)])
        S = "ABCDEF"[state]
        start, end = f"L {st} {S}> 0^inf", f"L {en} {S}> 0^inf"
        lean, _ = prove(text, f"{name}_{n0}", start, end, nsteps=n1 - n0, count_first=True, max_seg=40, max_moves=max_moves,
                        doc=f"The round of the run from step {n0:,} to step {n1:,}, for every tape further left.")
        res.append((lean, start, end, n1 - n0))
    return res
