"""Checks c/passorbit.c against the closed form of py/passmap.py.

usage:
  python3 py/passorbit.py check N [FILE]   recompute the first N passes from [2, 2] with `passmap` and compare every
                                           checkpoint (list and hash) in FILE, the output of `passorbit orbit`
                                           (default: run c/passorbit.c for N passes)
  python3 py/passorbit.py comps S0 S1 P    the same counts as `passorbit comps S0 S1 P`, from `passmap` (slow)
  python3 py/passorbit.py after S          every list of S ones or fewer, S = 0 mod 4, whose closed-form orbit meets a
                                           stop block of 1 within 200 passes: from there, run the machine itself
                                           (`run_pass`) for up to 200 passes and count how many halt
"""
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import passmap  # noqa: E402

MASK = (1 << 64) - 1
FNV0 = 14695981039346656037
FNVP = 1099511628211
END = MASK


def fnv(h, y):
    """The hash of passorbit.c: FNV-1a a 64-bit word at a time, over the blocks and then 2^64 - 1."""
    for v in list(y) + [END]:
        h = ((h ^ v) * FNVP) & MASK
    return h


def build():
    out = os.path.join(tempfile.mkdtemp(), "passorbit")
    subprocess.run(["gcc", "-O2", "-o", out, os.path.join(ROOT, "c", "passorbit.c")], check=True)
    return out


CP = re.compile(r"^checkpoint (\d+) (\[[^\]]*\]) hash ([0-9a-f]{16})$")


def checkpoints(text):
    return {int(m.group(1)): (eval(m.group(2)), int(m.group(3), 16))
            for m in map(CP.match, text.splitlines()) if m}


def python_checkpoints(n, at):
    """{passes: (list, hash)} at each count in `at`, from passmap."""
    want, h, y = {}, FNV0, list(passmap.FIRST)
    for i in range(n):
        h = fnv(h, y)
        if i + 1 in at:
            want[i + 1] = (list(y), h)
        y = passmap.passmap(y)
        assert isinstance(y, list), (i, y)
    return want


def check(n, text=None):
    if text is None:
        text = subprocess.run([build(), "orbit", str(n)], capture_output=True, text=True, check=True).stdout
    got = {k: v for k, v in checkpoints(text).items() if k <= n}
    want = python_checkpoints(n, set(got))
    assert got and got == want, (got, want)
    return sorted(got)


def comps(s0, s1, p):
    """Counts by event and sum mod 4, as `passorbit comps` prints them (`sum` lines)."""
    from itertools import combinations
    cnt = {}
    for s in range(s0, s1 + 1):
        for k in range(1, s + 1):
            for cuts in combinations(range(1, s), k - 1):
                c = (0,) + cuts + (s,)
                y = [c[i + 1] - c[i] for i in range(k)]
                ev = "no_event"
                for _ in range(p):
                    z = passmap.passmap(y)
                    if z is None:
                        ev = "stop_block_1"
                        break
                    if z == passmap.HALT:
                        ev = "halt"
                        break
                    y = z
                key = f"{ev}_sum_mod4_{s % 4}"
                cnt[key] = cnt.get(key, 0) + 1
    return cnt


def after(smax, p=200):
    """{outcome: count} for the lists of `after` (outcome: halt, no_halt, unclean or steps)."""
    from itertools import combinations
    res = {}
    for s in range(4, smax + 1, 4):
        for k in range(1, s + 1):
            for cuts in combinations(range(1, s), k - 1):
                c = (0,) + cuts + (s,)
                y = [c[i + 1] - c[i] for i in range(k)]
                for _ in range(p):
                    z = passmap.passmap(y)
                    if not isinstance(z, list):
                        break
                    y = z
                if z is not None:
                    continue
                out = "no_halt"
                for _ in range(p):
                    r = passmap.run_pass(y, 10 ** 7)
                    if r is None:
                        out = "steps"
                        break
                    y, _, clean = r
                    if y == passmap.HALT:
                        out = "halt"
                        break
                    if not clean:
                        out = "unclean"
                        break
                res[out] = res.get(out, 0) + 1
    return res


def main(argv):
    if len(argv) >= 2 and argv[0] == "check":
        text = open(argv[2]).read() if len(argv) > 2 else None
        print("checkpoints agree:", check(int(argv[1]), text))
    elif len(argv) == 4 and argv[0] == "comps":
        for k, v in sorted(comps(*map(int, argv[1:])).items()):
            print("sum", k, v)
    elif len(argv) == 2 and argv[0] == "after":
        print(after(int(argv[1])))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
