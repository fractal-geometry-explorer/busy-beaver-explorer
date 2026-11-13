"""The rest map of 1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD, checked against the machine.

A rest is the head at the left end in state B reading 1 with the tape  B>1 P (1101)^A 0 (1101)^b1 0 ... 0 (1101)^bk
(single 0 separators, no marker), P = "0" (type 0) or "000" (type 000).  The list L = [b1..bk] enters only through
    g(L) = 6 + b1/2 + b2/4 + ... + bk/2^k,  i.e.  g([]) = 6,  g([b] + L) = (b + g(L) + 6)/2.
Next rest (A + g is always a multiple of 3 on the orbit from blank tape):
    type 000, A+g even:          000, (3A+g)/2
    type 000, A+g = 1 mod 4:     push A+1 onto L, 000, (A+g-5)/4
    type 000, A+g = 3 mod 4:     push A+1 onto L, 0,   (A+g+1)/4
    type 0,   A+g odd:           0,   (3A+g-3)/2
    type 0,   A+g even:          000, (3A+g-6)/2
The first rest is type 0, A = 3, L = [] (62 steps).

usage:
  python3 py/map.py iterate N          the first N rests from blank tape (prints the first 40, then a summary)
  python3 py/map.py events STEPS       compare with every rest of a direct run of STEPS steps (C, ../<M1>/c/evw.c)
  python3 py/map.py random N SEED      compare with N runs from random rests (A+g = 0 mod 3), each to the next rest
"""
import os
import random
import re
import subprocess
import sys

M = "1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD"
HERE = os.path.dirname(os.path.abspath(__file__))
SHARED_C = os.path.join(HERE, "..", "..", "1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB", "c")


def g_of(L):
    g = 6
    for b in reversed(L):
        assert (b + g) % 2 == 0
        g = (b + g + 6) // 2
    return g


def step(t, A, L):
    """(type, A, L) -> next rest."""
    g = g_of(L)
    if t == "000":
        if (A + g) % 2 == 0:
            return "000", (3 * A + g) // 2, L
        if (A + g) % 4 == 1:
            return "000", (A + g - 5) // 4, [A + 1] + L
        return "0", (A + g + 1) // 4, [A + 1] + L
    if (A + g) % 2 == 1:
        return "0", (3 * A + g - 3) // 2, L
    return "000", (3 * A + g - 6) // 2, L


def step_g(t, A, g):
    """The same on (type, A, g) only; returns (type, A, g, pushed)."""
    if t == "000":
        if (A + g) % 2 == 0:
            return "000", (3 * A + g) // 2, g, False
        g2 = (A + g + 7) // 2
        if (A + g) % 4 == 1:
            return "000", (A + g - 5) // 4, g2, True
        return "0", (A + g + 1) // 4, g2, True
    if (A + g) % 2 == 1:
        return "0", (3 * A + g - 3) // 2, g, False
    return "000", (3 * A + g - 6) // 2, g, False


def evw():
    exe = os.path.join("/tmp", "evw_" + str(os.getuid()))
    if not os.path.exists(exe):
        subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(SHARED_C, "evw.c")], check=True)
    return exe


def rests(steps, tape=None, first_only=False):
    """Rests (step, type, A, L) of a direct run (from blank tape, or from `tape` in evw's TAPE syntax)."""
    env = dict(os.environ)
    if tape:
        env["TAPE"] = tape
    p = subprocess.Popen([evw(), M, str(steps), "B", "L", "1101"], stdout=subprocess.PIPE, text=True, env=env)
    try:
        for line in p.stdout:
            f = line.split()
            if f[0] == "HALT":
                yield ("HALT", int(f[1]))
                return
            if len(f) < 4 or f[1] != "B>1" or f[2] not in ("0", "000") or int(f[0]) == 0:
                continue
            toks, nums, ok = f[3:], [], True
            for i, x in enumerate(toks):
                if i % 2 == 0:
                    m = re.fullmatch(r"1101(?:\^(\d+))?", x)
                    if not m:
                        ok = False
                        break
                    nums.append(int(m.group(1) or 1))
                elif x != "0":
                    ok = False
                    break
            if ok and len(toks) % 2 == 1:
                yield (int(f[0]), f[2], nums[0], nums[1:])
                if first_only:
                    return
    finally:
        p.kill()
        p.wait()


def cmd_iterate(n):
    t, A, g = "0", 3, 6
    pushes, small = 0, 0
    for i in range(1, n + 1):
        if i <= 40:
            print(i, t, A, g)
        t, A, g, p = step_g(t, A, g)
        pushes += p
        if i > 9 and A < 64:
            small += 1
            print("small A at rest", i + 1, t, A, g)
    print(f"rest {n + 1}: type {t}, A has {A.bit_length()} bits, g {g.bit_length()} bits; {pushes} pushes; "
          f"rests after the 10th with A < 64: {small}")


def cmd_events(steps):
    rs = list(rests(steps))
    ok = 0
    for (k, t, A, L), (k2, t2, A2, L2) in zip(rs, rs[1:]):
        pred = step(t, A, L)
        if pred != (t2, A2, L2):
            print("MISMATCH at", k, (t, A, L), "->", (t2, A2, L2), "predicted", pred)
            return 1
        ok += 1
    print(f"{len(rs)} rests up to step {rs[-1][0]}, {ok} transitions, all as predicted; last rest {rs[-1][1:]}")
    return 0


def cmd_random(n, seed):
    rnd = random.Random(seed)
    bad = 0
    for _ in range(n):
        L, g = [], 6
        for _ in range(rnd.randint(0, 4)):
            while True:
                b = rnd.randint(3, 400)
                if (b + g) % 2 == 0:
                    break
            L, g = [b] + L, (b + g + 6) // 2
        t = rnd.choice(["0", "000"])
        while True:
            A = rnd.randint(5, 600)
            if (A + g) % 3 == 0:
                break
        tape = f"B>1 {t} (1101)^{A} " + " ".join(f"0 (1101)^{b}" for b in L)
        gen = rests(5 * 10 ** 9, tape, True)
        got = next(gen, None)
        gen.close()
        got = got if got is None or got[0] == "HALT" else got[1:]
        if got != step(t, A, L):
            bad += 1
            print("MISMATCH", (t, A, L), "got", got, "predicted", step(t, A, L))
    print(f"{n} random rests, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.set_int_max_str_digits(0)
    cmd = sys.argv[1] if len(sys.argv) > 1 else "iterate"
    if cmd == "iterate":
        cmd_iterate(int(float(sys.argv[2])) if len(sys.argv) > 2 else 1000)
    elif cmd == "events":
        sys.exit(cmd_events(int(float(sys.argv[2]))))
    elif cmd == "random":
        sys.exit(cmd_random(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1))
