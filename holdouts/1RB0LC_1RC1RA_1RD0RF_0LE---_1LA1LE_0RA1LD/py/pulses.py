"""The pulse rules of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD, tested on random tapes (observation, not proof).

The tape at the head's visit to the left end at step 182,483 is  C>0 (011)^4 001101 (10)^11 (11010)^9 ...
Everything after 001101 up to the first run of three or more 1s is a list of "words" 10 and 110 (runs of one or two 1s,
each followed by a single 0). Such words are transparent: one round trip of the head (two returns to the left end)
leaves them as they are. The first place where the tape is not made of words is the first *defect*: a run 1^k with
k >= 3, or a run of two or more 0s. One round trip acts on the first defect only (a "pulse").

usage: python3 pulses.py SPEC [TRIPS] [SEEDS]
  SPEC builds the tape after that left part: wN = N random words, kK = 1^K then 0, zJ = J zeros in a row in place of
  the single 0 that ends the previous word. A blank tape follows. For each seed the tape is printed as its defects,
  "[n]k" = n words then the defect k (1^k if k > 0, 0^-k if k < 0), after each round trip.
examples:
  python3 pulses.py 'w15 k9 w8 k7 w5' 1 20     # 1^9 -> 1^6       (20 of 20 seeds)
  python3 pulses.py 'w15 k4 w8 k7 w5' 1 20     # 1^4, 1^5 dissolve into words
  python3 pulses.py 'w15 k3 w8 k7 w5' 1 20     # 1^3 -> 00
  python3 pulses.py 'w15 z3 w8 k7 w5' 1 20     # an inner 000: the machine halts
  python3 pulses.py 'w15 z2 w8 k7 w5' 4 3      # 00: a local zigzag; the result depends on the words, not only their numbers
"""
import random
import re
import sys

M = "1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"
T = {}
for i, s in enumerate(M.split("_")):
    for b in (0, 1):
        x = s[3 * b:3 * b + 3]
        T[(i, b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)


def left_part():
    tape = bytearray(1 << 16)
    p = lo = hi = 1 << 15
    st = 0
    for _ in range(182483):
        w, d, st = T[(st, tape[p])]
        tape[p] = w
        p += d
        lo, hi = min(lo, p), max(hi, p)
    assert st == 2 and p == lo
    s = "".join(str(c) for c in tape[lo:hi + 1])
    return s[:s.index("11010" * 9) + 45]


def round_trip(s):
    """Run from C on the first cell of s until the second return to the left end; None if it halts."""
    tape = {i: int(c) for i, c in enumerate(s)}
    p, st, lo, hi, v = 0, 2, 0, len(s) - 1, 0
    while True:
        tr = T[(st, tape.get(p, 0))]
        if tr is None:
            return None
        w, d, st = tr
        tape[p] = w
        p += d
        lo, hi = min(lo, p), max(hi, p)
        if st == 2 and p == lo:
            v += 1
            if v == 2:
                return "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1))


def defects(x):
    m = re.match(r"0(011)*001101", x)
    if m is None:
        return "(left part not of the form 0 (011)^a 001101)"
    toks = re.findall(r"1+|0+", x[m.end():])
    out, w = [], 0
    for j, tk in enumerate(toks):
        if tk[0] == "1":
            if len(tk) >= 3:
                out.append("[%d]%d" % (w, len(tk)))
                w = 0
            else:
                w += 1
        elif len(tk) >= 2 and j < len(toks) - 1:
            out.append("[%d]-%d" % (w, len(tk)))
            w = 0
    out.append("[%d]end" % w)
    return " ".join(out)


def build(pre, spec, seed):
    random.seed(seed)
    x = ""
    for tk in spec.split():
        n = int(tk[1:])
        if tk[0] == "w":
            x += "".join(random.choice(["10", "110"]) for _ in range(n))
        elif tk[0] == "k":
            x += "1" * n + "0"
        elif tk[0] == "z":
            x += "0" * (n - 1)
    return pre + x + "000"


def main(argv):
    spec = argv[0]
    trips = int(argv[1]) if len(argv) > 1 else 1
    seeds = int(argv[2]) if len(argv) > 2 else 1
    pre = left_part()
    for sd in range(seeds):
        cur = build(pre, spec, sd)
        print("seed", sd, "start", defects(cur))
        for r in range(trips):
            cur = round_trip(cur)
            if cur is None:
                print("   HALT")
                break
            print("  ", r + 1, defects(cur))


if __name__ == "__main__":
    main(sys.argv[1:])
