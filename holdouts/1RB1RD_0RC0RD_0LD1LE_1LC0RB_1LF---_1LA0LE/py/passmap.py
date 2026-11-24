"""The pass map of 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE, and its checks against the exact simulator.

usage: python3 passmap.py check-blank N     compare the map with the first N right-end events from blank tape
       python3 passmap.py check-random K    compare the map, the restart and the merge rules on K random starts
       python3 passmap.py check-restarts K  compare what follows a restart with the rules (merge, halt) on K random restarts
       python3 passmap.py halts M           show that (10)^(2^m+4) 0^(2m-6) halts for m = 3..M (simulator)
(needs ../c/events.c compiled to ../c/events: gcc -O2 -o events events.c)

A right-end event is the head stepping onto a new rightmost cell in state C.  Almost always the tape is then
(10)^x 0^y (written (x, y)).  `step(x, y)` is the next event, or None when the pass ends in a restart (see README).

The pass, as the README explains it: a front sweeps right, halving each block of 10 pairs it meets (a cycle eats two
pairs and adds one pair and two 0s behind it; Lean: `front_cycles`).  The front is (a, z, b): a pairs behind it,
z zeros (z odd, -1 right after a reset) and b pairs left in the block ahead.  Where the block ends:
  b odd, at the separator 11:  reset   a += 1, the zeros become the new block b = (z + 3) / 2, z = -1, c -= 1
  b even, at the separator:    cross   a += 1, z += 4, the block ahead is the right block, b = c - 2
  b odd, at the right end:     the pass ends with (x', y') = (a + 1, z + 5)
  b even, at the right end:    reset   b = (z + 3) / 2, z = -1
The sweep back to the left end turns (x, y) into the blocks x - 5 and c = y/2 + 1 with a separator between them.
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EVENTS = os.path.join(HERE, "..", "c", "events")


def cross_point(x, y):
    """The front where it reaches the separator with an even block: (a, z, c)."""
    a, z, b, c = 2, 1, x - 5, y // 2 + 1
    while b % 2 == 1:
        a += (b - 1) // 2 + 1
        z += b - 1
        b = (z + 3) // 2
        z = -1
        c -= 1
    a += b // 2 + 1
    z += b + 4
    return a, z, c


def step(x, y):
    """The next right-end event (x', y'), or None if this pass ends in a restart (c < 0)."""
    a, z, c = cross_point(x, y)
    b = c - 2
    if b < 0:
        if b < -2:
            return None
        a, z, b = a - 1, z - 2, b + 2      # (a, z, b) and (a - 1, z - 2, b + 2) are the same front
    while b % 2 == 0:
        a += b // 2
        z += b
        b = (z + 3) // 2
        z = -1
        if b == 2:
            raise RuntimeError("front stuck at b = 2")  # never met; the machine would then run off to the right
    a += (b - 1) // 2
    z += b - 1
    return a + 1, z + 5


def restart(x, y):
    """For a pass that ends in a restart: (wall X, buffer Y0, j).  The next event is (10)^X 0^Y0 10 0000."""
    a, z, c = cross_point(x, y)
    j = -c
    assert j >= 1
    Y0 = 2 ** j * (z - 4) + 1
    X = a - ((2 ** j - 1) * (z - 4) + 2 * j + 1) // 2
    return X, Y0, j


def events(k, toks=()):
    out = subprocess.run([EVENTS, str(k)] + list(toks), capture_output=True, text=True, check=True).stdout
    res = []
    for line in out.strip().split("\n"):
        if line.startswith("HALT"):
            res.append("HALT")
            break
        res.append(line.split(":")[1].split())
    return res


def xy(tokens):
    if len(tokens) == 2 and tokens[0][0] == "a" and tokens[1][0] == "z":
        return int(tokens[0][1:]), int(tokens[1][1:])
    return None


def check_blank(n):
    evs = [xy(t) for t in events(n)]
    ok = bad = 0
    for p, q in zip(evs, evs[1:]):
        if p and q and p[0] >= 6:
            if step(*p) == q:
                ok += 1
            else:
                bad += 1
                print("MISMATCH", p, q, step(*p))
    print(f"{ok} passes agree, {bad} disagree")


def check_random(k, seed=1):
    rnd = random.Random(seed)
    ok = bad = 0
    for _ in range(k):
        x, y = rnd.randint(6, 400), 2 * rnd.randint(0, 40)
        r = step(x, y)
        ev = events(1, ["a%d" % x, "z%d" % y])[0]
        if r is not None:
            good = ev == ["a%d" % r[0], "z%d" % r[1]]
        else:
            X, Y0, j = restart(x, y)
            good = ev == ["a%d" % X, "z%d" % Y0, "a1", "z4"] if Y0 > 0 else True
        ok += good
        bad += not good
        if not good:
            print("MISMATCH", x, y, ev)
    print(f"{ok} starts agree, {bad} disagree")


def blank_events(n):
    """B[1..n]: the right-end events from blank tape after (10)^1 0^4, by the map from (21, 44) = B[14] on (valid
    up to B[975986], the first restart of the run from blank)."""
    B = [None] + [xy(t) for t in events(16)[2:16]]
    while len(B) <= n:
        B.append(step(*B[-1]))
    return B


def check_restarts(k, seed=2):
    """After (10)^X 0^Y0 10 0000 the right part runs as a copy of the run from blank while the buffer of 0s shrinks by
    3 a pass.  Y0 = 3k: after k + 1 passes the tape is (10)^(X + x) 0^y with (x, y) = B[k + 1].  Y0 = 3k + 2: halts
    on pass k + 2."""
    rnd = random.Random(seed)
    B = blank_events(200)
    ok = bad = 0
    for _ in range(k):
        X, r = rnd.randint(50, 3000), rnd.choice([0, 2])
        Y0 = 3 * rnd.randint(5, 60) + r
        n = Y0 // 3
        ev = events(n + 3, ["a%d" % X, "z%d" % Y0, "a1", "z4"])
        if r == 0:
            good = ev[n] == ["a%d" % (X + B[n + 1][0]), "z%d" % B[n + 1][1]]
        else:
            good = ev[-1] == "HALT" and len(ev) == n + 3
        ok += good
        bad += not good
        if not good:
            print("MISMATCH", X, Y0, ev[n - 1:n + 3])
    print(f"{ok} restarts agree, {bad} disagree")


def halts(mmax):
    for m in range(3, mmax + 1):
        x, y = 2 ** m + 4, 2 * m - 6
        X, Y0, j = restart(x, y)
        ev = events(10, ["a%d" % x, "z%d" % y])
        print(f"m={m}: (10)^{x} 0^{y}: restart wall {X} buffer {Y0} (mod 3 = {Y0 % 3}); simulator: {ev[-1]}")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "check-blank":
        check_blank(int(sys.argv[2]))
    elif cmd == "check-random":
        check_random(int(sys.argv[2]))
    elif cmd == "check-restarts":
        check_restarts(int(sys.argv[2]))
    elif cmd == "halts":
        halts(int(sys.argv[2]))
