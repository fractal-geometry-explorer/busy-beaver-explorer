"""Iterate the round map of 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD (lean/Macro.lean, `next`) from P 3 0.

usage: python3 orbit.py N [--check STEPS]

A round start is P u v = `C> 0 11 0 (11)^u 0 (11)^v` or Q u v = `C> 0 11 0 11 0 (11)^u 0 (11)^v` (counts of pairs):
  P: u < v -> P(3u+2, v-u-1)     u >= v+2 -> Q(3v+3, u-v-2)
  Q: u < v -> Q(3u+3, v-u-1)     u >= v+2 -> P(3v+5, u-v-2)
  u = v or u = v+1: the machine halts (Lean: `halts_iff'`).
Prints the growth of u+v and the closest approach of u-v to {0, 1} after the first rounds, measured by
log2(|u - v - 1/2| / (u + v)) (from bit lengths, to within one).  With --check, also compares the first rounds with a direct simulation of the
machine for STEPS steps (round starts: state C on the blank left of the tape).
"""
import math
import sys


def nxt(k, u, v):
    if u == v or u == v + 1:
        return None
    if u < v:
        return (k, 3 * u + (2 if k == "P" else 3), v - u - 1)
    return ("Q" if k == "P" else "P", 3 * v + (3 if k == "P" else 5), u - v - 2)


def simulate(steps):
    """Round starts of the machine itself: (step, block lengths) each time C reads the blank left of the tape."""
    t = {"A": ("1RB", "1RC"), "B": ("1LC", "1LC"), "C": ("1RE", "0LD"), "D": ("1LB", "1RF"), "E": (None, "1RA"),
         "F": ("0RD", "1RD")}
    tape, h, st, lo, hi, out = {}, 0, "A", 0, 0, []
    for n in range(steps):
        x = tape.get(h, 0)
        if st == "C" and x == 0 and h == lo and n:
            s = "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1)).strip("0")
            out.append((n, [len(b) for b in s.split("0")]))
        tr = t[st][x]
        if tr is None:
            out.append((n + 1, "halt"))
            break
        tape[h] = int(tr[0])
        h += 1 if tr[1] == "R" else -1
        st = tr[2]
        lo, hi = min(lo, h), max(hi, h)
    return out


def main(argv):
    n = int(float(argv[0]))
    if "--check" in argv:
        steps = int(float(argv[argv.index("--check") + 1]))
        ev = [b for _, b in simulate(steps) if b != "halt" and b[0] == 2 and all(x % 2 == 0 for x in b)]
        s, ok = ("P", 3, 0), 0
        for b in ev:
            k, u, v = s
            want = [2, 2 * u, 2 * v] if k == "P" else [2, 2, 2 * u, 2 * v]
            while want and want[-1] == 0:
                want.pop()
            if b != want:
                print("mismatch", b, s)
                return
            ok += 1
            s = nxt(*s)
        print(f"the first {ok} round starts of a {steps}-step run agree with the map")
    s, best = ("P", 3, 0), None
    for i in range(1, n + 1):
        s = nxt(*s)
        if s is None:
            print("HALTS at round", i)
            return
        k, u, v = s
        if i >= 20:
            # log2(|u - v - 1/2| / (u + v)), to within one, from bit lengths
            lq = abs(2 * (u - v) - 1).bit_length() - (2 * (u + v)).bit_length()
            if best is None or lq < best[0]:
                best = (lq, i)
        if i % (n // 10 or 1) == 0:
            print(f"round {i}: u+v has {(u + v).bit_length()} bits; closest approach so far log2 = {best[0]} "
                  f"at round {best[1]}", flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
