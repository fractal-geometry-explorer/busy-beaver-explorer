"""The base-5 odometer of the machines 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA{0RF,1RF}_{F}---, checked against the run.

usage: python3 holdouts/MACHINE/py/odometer.py [STEPS]       (default 1.5e9 steps; compiles ../c/odo.c with gcc)

c/odo.c samples the run each time the head arrives at the left end of the tape in state D with `1000` there, and
prints the tape as runs of b = 1000 and the stretches between them.  Here each stretch is split into gadgets
g0 = 1001, g1 = 1001100, g2 = 100110, g3 = 10011, g4 = 10010, s = 0 (anything else is printed as ?bits), and every
sample is compared with the regular odometer round applied to the one before:

  the left block k gains one b, then the first gadget advances:
    g0 -> g1: the block after it loses one b       g1 -> g2, g2 -> g3: nothing
    g4 -> g0: the block before it gains one b, the block after loses one
    s  -> g0: the block before it loses one b
    g3 -> g4: carry, the next gadget advances (by the same rules)
  a carry into the last gadget (the right end of the tape) is a reset: see the README.

The script prints the counts of regular and other rounds and the other rounds themselves.
"""
import functools
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.basename(os.path.dirname(HERE))
G = {"g0": "1001", "g1": "1001100", "g2": "100110", "g3": "10011", "g4": "10010", "s": "0"}


@functools.lru_cache(None)
def split(s):
    if s == "":
        return ()
    for n in ("g1", "g2", "g3", "g4", "g0", "s"):
        if s.startswith(G[n]):
            r = split(s[len(G[n]):])
            if r is not None:
                return (n,) + r
    return None


def parse(fields):
    out = []
    for i, f in enumerate(fields):
        if i % 2 == 0:
            out.append(int(f))
        else:
            sp = split(f)
            if sp is None:
                out.append("?" + f)
            else:
                for j, g in enumerate(sp):
                    if j:
                        out.append(0)
                    out.append(g)
    return out


def regular(t):
    L = list(t)
    L[0] += 1
    i = 1
    while True:
        if i >= len(L) - 1 or not isinstance(L[i], str) or L[i].startswith("?"):
            return None
        g = L[i]
        if g == "g0":
            if L[i + 1] < 1:
                return None
            L[i], L[i + 1] = "g1", L[i + 1] - 1
        elif g in ("g1", "g2"):
            L[i] = {"g1": "g2", "g2": "g3"}[g]
        elif g == "g3":
            L[i] = "g4"
            i += 2
            continue
        elif g == "g4":
            if L[i + 1] < 1:
                return None
            L[i], L[i - 1], L[i + 1] = "g0", L[i - 1] + 1, L[i + 1] - 1
        elif g == "s":
            if L[i - 1] < 1:
                return None
            L[i], L[i - 1] = "g0", L[i - 1] - 1
        return L


def show(t):
    return " ".join(str(x) for x in t)


def main():
    steps = sys.argv[1] if len(sys.argv) > 1 else "1500000000"
    exe = os.path.join(tempfile.mkdtemp(), "odo")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "odo.c")], check=True)
    p = subprocess.Popen([exe, M, steps, "0"], stdout=subprocess.PIPE, text=True)
    prev = None
    good = other = 0
    for line in p.stdout:
        if "|" not in line:
            continue
        a, b = line.split("|")
        st, t = int(a.split()[0]), parse(b.split())
        t = t[:-1] if t and t[-1] == 0 else t
        if prev is not None:
            if regular(prev[1]) == t:
                good += 1
            else:
                other += 1
                print(f"step {prev[0]:>13,}: {show(prev[1])[:150]}")
                print(f"  ->  {st:>11,}: {show(t)[:150]}")
        prev = (st, t)
    print(f"{good} regular odometer rounds, {other} other rounds (resets and exhausted blocks)")


if __name__ == "__main__":
    main()
