"""Iterate the round map of 1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA (lean/Macro.lean, `next`) from Z 1.

usage: python3 orbit.py N [--check STEPS]

Round starts: R n m = `A> 0 11 (01)^n 0 11 (01)^m`, Z k = `A> 0 11 (01)^k` (Z k is R (k-1) (-1) in the rule below):
  n even: (n, m) -> (3n/2 + 2, m + 2)        n odd: (n, m) -> ((3n+7)/2, m - 1)
and the machine halts iff the counter would go below -1 (n odd at m = -1); Lean: `halts_iff'`.
Prints n's size, the counter m and its minimum after the first rounds.  With --check, compares the first round
starts with a direct simulation of STEPS steps.
"""
import sys


def simulate(steps):
    t = {"A": ("1RB", "1RC"), "B": ("1LC", "1LE"), "C": ("1RA", "1RD"), "D": ("0RF", "0RE"), "E": ("1LA", "0LB"),
         "F": (None, "1RA")}
    tape, h, st, lo, hi, out = {}, 0, "A", 0, 0, []
    for n in range(steps):
        x = tape.get(h, 0)
        if st == "A" and x == 0 and h == lo and n:
            out.append("".join(str(tape.get(i, 0)) for i in range(lo, hi + 1)).rstrip("0"))
        tr = t[st][x]
        if tr is None:
            out.append("halt")
            break
        tape[h] = int(tr[0])
        h += 1 if tr[1] == "R" else -1
        st = tr[2]
        lo, hi = min(lo, h), max(hi, h)
    return out


def word(n, m):
    if m == -1:
        return "011" + "01" * (n + 1)
    return "011" + "01" * n + "011" + "01" * m


def main(argv):
    N = int(float(argv[0]))
    if "--check" in argv:
        steps = int(float(argv[argv.index("--check") + 1]))
        n, m, ok = 0, -1, 0
        for w in simulate(steps):
            if w != word(n, m):
                print("mismatch at round", ok, w[:80], (n, m))
                return
            ok += 1
            n, m = (3 * n // 2 + 2, m + 2) if n % 2 == 0 else ((3 * n + 7) // 2, m - 1)
        print(f"the first {ok} round starts of a {steps}-step run agree with the map")
    n, m, low = 0, -1, None
    odd = 0
    for i in range(1, N + 1):
        if n % 2 == 0:
            n, m = 3 * n // 2 + 2, m + 2
        else:
            if m == -1:
                print("HALTS at round", i)
                return
            n, m = (3 * n + 7) // 2, m - 1
            odd += 1
        if i >= 100 and (low is None or m < low[0]):
            low = (m, i)
        if i % (N // 10 or 1) == 0:
            print(f"round {i}: n has {n.bit_length()} bits, counter m = {m}, odd rounds {odd}, "
                  f"lowest m after round 100: {low[0]} (round {low[1]})", flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
