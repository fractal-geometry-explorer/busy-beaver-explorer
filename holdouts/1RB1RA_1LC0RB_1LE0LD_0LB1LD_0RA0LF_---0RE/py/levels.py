"""The run from blank tape as a sequence of levels, with the engine of py/closure.py on numbers.

Prints each level start (sample number is not tracked; b, type index in order of appearance, block counts), using
the verified cycles of closure.py for jumps.  With arguments `TYPE b m1 m2 [c]` it instead runs single levels of a
counter type from made-up counts: b fixed, m = m1..m2, to see whether any halts and where each goes.

usage (from the repo root):
  python3 holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/py/levels.py SECONDS
  python3 holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/py/levels.py 6 B M1 M2
  python3 holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/py/levels.py 7 B M1 M2 C
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import closure as C  # noqa: E402
from closure import Blank, Config, Lin, Rep, compress, norm, run, key_counts, build, run_level, show, Fail, Need, Modulus  # noqa: E402

T6 = "0^inf B> 0 (11110)^{b} 1 (111100)^{m} 1 1 1 0^inf"       # = (01111)^b (011110)^m 0111
T7 = "0^inf B> 0 (11110)^{b} 0 1 1 1 1 1 0 0 0 1 1 (100)^{c} 1 1 0 1 1 1 1 0 0 (110011)^{m} 1 1 0 1 1 1 0^inf"


def one(toks):
    k, c, _ = run_level(compress(norm(toks)), [], [])
    return k, c


def main():
    types = []
    if len(sys.argv) > 2:
        t, b, m1, m2 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        c = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        for m in range(m1, m2 + 1):
            s = (T6 if t == 6 else T7).format(b=b, m=m, c=c)
            try:
                k, cs = one(Config.parse(s).right)
                print(f"m={m}: -> " + " ".join(map(str, compress(norm(build(k, cs))))), flush=True)
            except (Fail, Need, Modulus) as e:
                print(f"m={m}: {type(e).__name__} {str(e)[:100]}", flush=True)
        return
    seconds = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    t0 = time.time()
    c = run(C.MACH, Config([Blank()], 0, [Blank()]), C.is_sample, rotate=True, max_moves=200000)
    toks = compress(norm(c.right))
    while not C.is_level_start(toks):
        toks = C.visit(toks)
    n = 0
    while time.time() - t0 < seconds:
        toks = compress(norm(toks))
        print(f"level {n} ({time.time() - t0:.0f} s): " + " ".join(map(str, toks)), flush=True)
        k, cs = one(toks)
        toks = build(k, cs)
        n += 1


if __name__ == "__main__":
    main()
