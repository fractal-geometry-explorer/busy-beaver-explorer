"""Run 1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE from random tapes of the shape the run has: blocks a^x (a = 10, x
uniform in [LO, HI]) split by single 0s, a 0 at the left end and 0 1 at the right end, the head in state A at the
left end; count how many halt within STEPS steps.  Shows that whether the machine halts depends on the block
lengths: with blocks of length 1 and 2 a few per cent halt within 10^5 steps, with all blocks >= 3 none did.

usage: python3 random_tapes.py SEED LO HI MAXBLOCKS TRIALS STEPS
  e.g. python3 random_tapes.py 2 1 2 8 1000 100000   (29 of 1000 halt)
       python3 random_tapes.py 1 3 12 8 1000 100000  (none halt)
"""
import random
import sys

M = "1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE"


def parse(s):
    T = {}
    for i, g in enumerate(s.split("_")):
        for r in range(2):
            t = g[3 * r:3 * r + 3]
            if t[2] != "-":
                T[(i, r)] = (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def run(T, cells, steps):
    tape, h, q = dict(enumerate(cells)), 0, 0
    for k in range(steps):
        r = tape.get(h, 0)
        if (q, r) not in T:
            return k + 1
        w, d, q = T[(q, r)]
        tape[h] = w
        h += d
    return None


def main(argv):
    seed, lo, hi, nbmax, trials, steps = map(int, argv)
    random.seed(seed)
    T = parse(M)
    halts = 0
    for _ in range(trials):
        nb = random.randint(1, nbmax)
        s = "0" + "".join("10" * random.randint(lo, hi) + ("0" if i < nb - 1 else "01") for i in range(nb))
        if run(T, [int(c) for c in s], steps) is not None:
            halts += 1
    print(f"{halts} of {trials} random tapes halt within {steps} steps")


if __name__ == "__main__":
    main(sys.argv[1:])
