"""The sample map of 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD, checked against the machine, and iterated.

Sample: the head in state C at the right end of the visited tape.  From step 216 on, every sample is (except one
in each R step, where the tape is a solid block 1^k)
    K(x, m, s) = 1^4 0 (10)^x 1^m  with the head on the cell s right of the block of m ones (blank beyond).
The map from one sample to the next:
    m even, x >= 1 :  (x-1, m+4, 1-s)                       B
    m even, x = 0  :  ((m+6)/2, 1 if s = 0 else 3, 0)       R
    m odd,  x = 0  :  the machine halts (A reads a 1)        H
    m odd,  x = (m+3)/2, s = 0 :  (2x+3, 1, 0)               A'
    m odd,  otherwise 1 <= x < (m+5)/2 :  (2x+1, m-2x+4, 1-s)  A
    m odd,  x >= (m+5)/2     :  (x-(m+5)/2, 2m+7-s, s)      C

usage (from the repository root):
    python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/samplemap.py check STEPS
        run tools/c/tmrun (compiled into /tmp) and check the map on every pair of consecutive samples
    python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/samplemap.py orbit ROUNDS
        iterate the map from the sample at step 216, a whole B phase at once, for ROUNDS R steps
"""
import os, re, subprocess, sys, tempfile, collections

M = "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD"
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")


def step(x, m, s):
    if m % 2 == 0:
        return ((x - 1, m + 4, 1 - s), "B") if x >= 1 else (((m + 6) // 2, 1 if s == 0 else 3, 0), "R")
    if x == 0:
        return None, "H"
    h = (m + 5) // 2
    if x >= h:
        return (x - h, 2 * m + 7 - s, s), "C"
    if x == h - 1 and s == 0:
        return (2 * x + 3, 1, 0), "A'"
    return (2 * x + 1, m - 2 * x + 4, 1 - s), "A"


def samples(steps):
    exe = os.path.join(tempfile.gettempdir(), "bbx_tmrun")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(ROOT, "tools", "c", "tmrun.c")], check=True)
    p = subprocess.Popen([exe, M, str(steps), "at", "C", "R", str(10 ** 12)], stdout=subprocess.PIPE, text=True)
    rx = re.compile(r"(\d+) 1\^4 0 ((?:1 0 )*)(?:1\^(\d+)|(1)) C>([01])$")
    for line in p.stdout:
        line = line.strip()
        if line.startswith(("running", "halted")):
            print(line); continue
        # compress (1 0)^x: tmrun prints "1 0 1 0 ..." runs as single cells, so count them
        mm = rx.match(line)
        if not mm:
            yield int(line.split()[0]), None, bool(re.fullmatch(r"\d+ 1\^\d+ C>[01]", line)); continue
        x = mm.group(2).count("1 0 ")
        m = int(mm.group(3)) if mm.group(3) else 1
        yield int(mm.group(1)), (x, m, int(mm.group(5))), False


def check(steps):
    cnt, prev = collections.Counter(), None
    for k, c, solid in samples(steps):
        if c is None:
            # inside an R step the head passes the right end once more, over a solid tape 1^k
            cnt["samples of another shape (inside R: solid tape)" if solid else "samples of another shape"] += 1
            if not solid:
                prev = None
            continue
        if prev is not None:
            nxt, rule = step(*prev[1])
            if nxt == c:
                cnt["rule " + rule] += 1
            else:
                cnt["mismatches"] += 1
                if cnt["mismatches"] <= 5:
                    print("mismatch at step", k, prev[1], "->", c, "map:", nxt)
        prev = (k, c)
    for key in sorted(cnt):
        print(f"{key}: {cnt[key]}")
    print("last sample:", prev)


def orbit(rounds, x=7, m=1, s=0):
    """Iterate from K(7, 1, 0) (the sample at step 216); a B phase is applied at once."""
    cnt = collections.Counter()
    r = 0
    while r < rounds:
        if m % 2 == 0 and x >= 1:
            m += 4 * x; s ^= x & 1; cnt["B"] += x; x = 0; continue
        nxt, rule = step(x, m, s)
        cnt[rule] += 1
        if rule == "H":
            print("halts in round", r); break
        if rule == "R":
            r += 1
        x, m, s = nxt
    print(f"after {r} R steps: rules {dict(cnt)}; x has {x.bit_length()} bits, m = {m}, s = {s}")


TABLE = {}
for i, part in enumerate(M.split("_")):
    for y in (0, 1):
        t = part[3 * y:3 * y + 3]
        TABLE[(i, y)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)


def next_sample(x, m, s, limit=10 ** 6):
    """Run the machine from K(x, m, s) to the next sample of the same form (skipping solid tapes)."""
    tape = [1, 1, 1, 1, 0] + [1, 0] * x + [1] * m + [s]
    tape = dict(enumerate(tape))
    head, st, hi, lo = len(tape) - 1, 2, len(tape) - 1, 0
    for _ in range(limit):
        tr = TABLE[(st, tape.get(head, 0))]
        if tr is None:
            return "H"
        tape[head], head, st = tr[0], head + tr[1], tr[2]
        hi, lo = max(hi, head), min(lo, head)
        if st == 2 and head == hi:
            cells = [tape.get(i, 0) for i in range(lo, hi)]
            while cells and cells[0] == 0:
                cells.pop(0)
            if all(cells):
                continue
            if cells[:5] != [1, 1, 1, 1, 0]:
                return ("other", cells)
            rest, xx = cells[5:], 0
            while rest[:2] == [1, 0]:
                rest, xx = rest[2:], xx + 1
            if not all(rest):
                return ("other", cells)
            return (xx, len(rest), tape.get(head, 0))
    return "limit"


def small():
    bad = n = 0
    cases = [(x, m) for x in range(25) for m in range(1, 30)] + [(x, m) for x in range(25, 45) for m in range(1, 70, 2)]
    cases += [(x, m) for x in range(45) for m in range(31, 70, 2) if x < 25]
    for x, m in cases:
        for s in (0, 1):
            got = next_sample(x, m, s)
            want, rule = step(x, m, s)
            n += 1
            if (want if rule != "H" else "H") != got:
                bad += 1
                print("differs:", (x, m, s), "machine", got, "map", want, rule)
    print(f"{n} small samples, {bad} differ from the map")


if __name__ == "__main__":
    {"check": lambda: check(int(sys.argv[2])), "orbit": lambda: orbit(int(sys.argv[2])), "small": small}[sys.argv[1]]()
