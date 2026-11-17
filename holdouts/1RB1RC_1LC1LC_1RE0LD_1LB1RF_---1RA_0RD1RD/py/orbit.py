"""Iterate the round map of 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD (lean/Macro.lean, `next`) from P 3 0.

usage: python3 orbit.py N [--check STEPS]
       python3 orbit.py rules      the rule table with step counts (round_steps) against direct simulation

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


def round_steps(k, u, v):
    """Machine steps of the round from P u v / Q u v (u >= 3) to the next round start, or to the halt (counting the
    halting step)."""
    q = 0 if k == "P" else 1
    if u < v:
        return 12 * u * v + 24 * u + (27 if q else 11)
    if u == v:
        return 12 * u * u - 6 * u + (8 if q else 5)
    if u == v + 1:
        return 12 * u * u - 18 * u + (17 if q else 14)
    return 12 * u * v + 12 * u + 12 * v + (35 if q else 15)


TT = {(st, r): (None if t is None else (int(t[0]), 1 if t[1] == "R" else -1, t[2]))
      for st, ts in {"A": ("1RB", "1RC"), "B": ("1LC", "1LC"), "C": ("1RE", "0LD"), "D": ("1LB", "1RF"),
                     "E": (None, "1RA"), "F": ("0RD", "1RD")}.items() for r, t in enumerate(ts)}


def blocks(s):
    """The tape at a round start as block lengths."""
    k, u, v = s
    b = [2, 2 * u, 2 * v] if k == "P" else [2, 2, 2 * u, 2 * v]
    while b and b[-1] == 0:
        b.pop()
    return b


def run(tape, h, st, steps, n0=0):
    """Run from (tape, h, st), yielding (step, block lengths) at each round start and (step, 'halt') at the halt."""
    lo, hi = min(h, min(tape, default=h)), max(h, max(tape, default=h))
    for n in range(n0, steps):
        x = tape.get(h, 0)
        if st == "C" and x == 0 and h == lo and n > n0:
            s = "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1)).strip("0")
            yield n, [len(b) for b in s.split("0")]
        t = TT[(st, x)]
        if t is None:
            yield n + 1, "halt"
            return
        tape[h] = t[0]; h += t[1]; st = t[2]
        if h < lo:
            lo = h
        elif h > hi:
            hi = h


def check_rules():
    bad = n = halts = 0
    for k in "PQ":
        for u in range(3, 41):
            for v in range(0, 41):
                w = "011" + ("011" if k == "Q" else "") + "0" + "1" * (2 * u) + "0" + "1" * (2 * v)
                m, b = next(run({i: int(c) for i, c in enumerate(w)}, 0, "C", 10 ** 7))
                want = nxt(k, u, v)
                n += 1; halts += b == "halt"
                if b != ("halt" if want is None else blocks(want)) or m != round_steps(k, u, v):
                    bad += 1; print("differs at", k, u, v, b, m, want, round_steps(k, u, v))
    print(f"rules grid: {n} rounds ({halts} halting), {bad} failures")
    N = 10 ** 7
    s, acc, nr = ("P", 3, 0), 42, 0
    for m, b in run({}, 0, "A", N):
        if b != "halt" and (b[0] != 2 or any(x % 2 for x in b)):
            continue                  # C on the left end, but not a round start (the first steps)
        if nr:
            acc += round_steps(*s); s = nxt(*s)
        nr += 1
        if b != blocks(s) or m != acc:
            bad += 1; print("run differs at step", m, b, s, acc); acc = m
    print(f"rules run: {nr} round starts in the first {N:.0e} steps, the last at step {acc}, "
          f"{'all at the predicted step' if not bad else 'FAILED'}")
    return bad


def main(argv):
    if argv[0] == "rules":
        sys.exit(1 if check_rules() else 0)
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
