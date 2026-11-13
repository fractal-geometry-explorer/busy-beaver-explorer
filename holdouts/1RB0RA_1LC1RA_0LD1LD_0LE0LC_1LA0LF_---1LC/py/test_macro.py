"""Tests of c/macro.c (the run-length simulator with phase jumps) against the plain simulator.
python3 holdouts/<M>/py/test_macro.py

1. the whole tape after N steps, with and without jumps, equals the plain simulator's, for several N;
2. the main phase starts (step, y, cells, ones, fingerprint of the tape) of the first 3.3 million steps equal the
   plain simulator's;
3. with and without jumps the main phase starts agree up to 10^15 steps.
"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.machine import Machine
M = "1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC"
MP = 2 ** 61 - 1


def plain(nmax, stops):
    """tapes (as 'left STATE right' strings without outer zeros) at the steps in `stops`, and the main phase starts"""
    m = Machine.parse(M)
    tape, pos, st = {}, 0, 0
    out, mains, lasty = {}, [], None
    lo = hi = 0
    for n in range(nmax + 1):
        if n in stops:
            cells = [k for k, v in tape.items() if v]
            a, b = min(cells + [pos]), max(cells + [pos])
            out[n] = ("".join(str(tape.get(i, 0)) for i in range(a, pos)).lstrip("0"), "ABCDEF"[st],
                      "".join(str(tape.get(i, 0)) for i in range(pos, b + 1)).rstrip("0"))
        if st == 0 and pos < lo and tape.get(pos + 1) == 1 and not tape.get(pos + 2) and not tape.get(pos + 3) \
                and not tape.get(pos + 4):
            y, q = 0, pos + 5
            while tape.get(q) == 1 and not tape.get(q + 1):
                y, q = y + 1, q + 2
            if y >= 2 and y != lasty:
                lasty = y
                ones = [i - pos - 1 for i in range(pos + 1, hi + 1) if tape.get(i)]
                mains.append((n, y, max(ones) + 1, len(ones), sum(ones) % MP, sum(i * i for i in ones) % MP))
        w, d, ns = m.table[st][tape.get(pos, 0)]
        tape[pos] = w
        lo, hi = min(lo, pos), max(hi, pos)
        pos += d
        st = ns
    return out, mains


def macro(exe, *args):
    return subprocess.run([exe, *args], capture_output=True, text=True, check=True).stdout.splitlines()


def main():
    exe = os.path.join(tempfile.mkdtemp(), "macro")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "../c/macro.c")], check=True)
    # 1. whole tapes
    runs = []
    for n in (0, 1, 7, 100, 173, 500, 3000, 5000, 50000, 400000):
        for mode in ([], ["nojump"]):
            lines = macro(exe, f"={n}", "bits", *mode)
            got = int(lines[-2].split()[3])
            runs.append((got, lines[-1]))
    tapes, mains = plain(max(3300000, max(g for g, _ in runs)), {g for g, _ in runs})
    for got, line in runs:
        if " <" in line:                      # the head faces left: it is on the last cell of the left part
            l, _, r = line.partition(" <")
            st, r, l = r[0], r[2:], l.strip()
            l, r = l[:-1], (l[-1:] or "0") + r
        else:
            l, _, r = line.partition("> ")
            st, l = l[-1], l[:-2]
        l, r = l.strip().lstrip("0"), r.strip().rstrip("0")
        pl, ps, pr = tapes[got]
        assert (l, st, r) == (pl, ps, pr), (got, l[-30:], st, r[:30], pl[-30:], ps, pr[:30])
    print(f"tapes equal at {len(runs)} stops (up to step {max(g for g, _ in runs)})")
    # 2. main phase starts against the plain simulator
    ms = []
    for line in macro(exe, "=3300000"):
        if line.startswith("main phase"):
            p = line.split()
            ms.append((int(p[3]), int(p[5]), int(p[7]), int(p[9]), int(p[11]), int(p[12])))
    ms = [x for x in ms if x[0] <= 3300000]
    assert ms == mains and len(ms) == 6, (ms, mains)
    print(f"{len(ms)} main phase starts equal to the plain simulator's (y = {[x[1] for x in ms]})")
    # 3. jumps against no jumps
    a = [l.split(" runs ")[0] for l in macro(exe, "15") if l.startswith("main")]
    b = [l.split(" runs ")[0] for l in macro(exe, "15", "nojump") if l.startswith("main")]
    assert a == b and len(a) == 14, (len(a), len(b))
    print(f"{len(a)} main phase starts up to 10^15 steps: the same with and without jumps")
    print("OK")


if __name__ == "__main__":
    main()
