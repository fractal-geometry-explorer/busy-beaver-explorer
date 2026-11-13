"""The hole map of 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC.

Sample: the head in D on the leftmost visited cell, reading a 1. The visited tape is then N cells of 1 with one 0
(the hole) at position p (0-based from the left). From one sample to the next:

    p even:            N' = N + p/2 + 2,   p' = N' - 2
    p odd, p >= 5:     N' = N + 1,         p' = (p-3)/2
    p = 3:             N odd: N' = N + 4, p' = N' - 3;   N even: N' = N + 3, p' = N' - 2
    p = 1:             halts

`check`   compares the map with the machine on every (N, p) with N < LIMIT (default 120), and along the run from
          blank tape for STEPS steps (default 2e7);
`run K`   iterates the map K times from the run's first sample and reports how close it came to halting.

usage: python3 holemap.py check [LIMIT] [STEPS] | run K
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine, Run, Tape  # noqa: E402

M = "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"
C = 3      # state D


def hmap(N, p):
    """The next sample (N', p'), or None for a halt."""
    if p % 2 == 0:
        N2 = N + p // 2 + 2
        return N2, N2 - 2
    if p >= 5:
        return N + 1, (p - 3) // 2
    if p == 3:
        return (N + 4, N + 1) if N % 2 else (N + 3, N + 1)
    if p == 1:
        return None
    raise ValueError((N, p))


def sample(r):
    w = r.tape.word()
    z = [i for i, c in enumerate(w) if c == 0]
    return len(w), z


def machine_next(N, p, maxs=10 ** 7):
    """Run the machine from the sample (N, p) to the next sample: (N', p'), None for a halt, '?' otherwise."""
    t = Tape()
    for i in range(N):
        t.set(i, 1)
    t.set(p, 0)
    t.lo, t.hi = 0, N - 1
    r = Run(Machine.parse(M), state=C, tape=t, head=0)
    while r.steps < maxs:
        if not r.step():
            return None
        if r.state == C and r.head == r.tape.lo and r.tape.get(r.head) == 1:
            n, z = sample(r)
            return (n, z[0]) if len(z) == 1 else "?"
    return "?"


def check(limit, steps):
    bad = 0
    for N in range(3, limit):
        for p in range(1, N - 1):
            want = hmap(N, p)
            got = machine_next(N, p)
            if got != want:
                bad += 1
                print("mismatch", N, p, want, got)
    print(f"map = machine on all samples with N < {limit}, 1 <= p <= N-2: {bad} mismatches")
    r = Run(Machine.parse(M))
    prev, n, ok = None, 0, 0
    while r.steps < steps:
        if not r.step():
            print("halted at", r.steps)
            return
        if r.state == C and r.head == r.tape.lo and r.tape.get(r.head) == 1 and r.steps > 1:
            N, z = sample(r)
            cur = (N, z[0]) if len(z) == 1 else None
            if prev is not None:
                ok += hmap(*prev) == cur
                n += 1
            prev = cur
    print(f"along the run to {steps:.0e} steps: {ok} of {n} sample transitions follow the map")


def run(k):
    N, p = 5, 2      # the run's first sample (step 11)
    closest = []
    for i in range(k):
        nxt = hmap(N, p)
        if nxt is None:
            print("halts at map step", i, "N =", N)
            return
        if p in (1, 3):
            closest.append((i, p))
        N, p = nxt
    print(f"no halt in {k} map steps; N now has {len(str(N))} digits; visits to p = 1 or 3: {closest[:20]}")


if __name__ == "__main__":
    if sys.argv[1] == "check":
        check(int(sys.argv[2]) if len(sys.argv) > 2 else 120, float(sys.argv[3]) if len(sys.argv) > 3 else 2e7)
    else:
        run(int(sys.argv[2]))
