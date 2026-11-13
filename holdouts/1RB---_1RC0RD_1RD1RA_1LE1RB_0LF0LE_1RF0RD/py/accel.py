"""An exact accelerated run of the separator-counter machines, built on the rules proved in `lean/Count.lean`.

The run is followed from one post-event configuration P(d, bs) to the next:
* if the phase does not overflow (bs[1:] has a 0 at or above index d), `event_rule` gives the next P at once;
* otherwise the counts before the overflowing one are applied with `count` (each proved): after c counts the
  string above b1 is all ones and the counter holds 2^d + c; from that configuration the machine is simulated
  cell by cell until it is in a P configuration again (any P configuration will do: the rules apply from it).
So the only unproved part is the direct simulation, which is exact.  Step counts: each count costs a + b·t + e·r
steps (t, r the two carry lengths; the constants are the step counts of the lemmas, `COST`), summed in closed form.

usage: python3 accel.py MACHINE STATE OVERFLOWS [--quiet] [--c=PATH]
       (--c=PATH: simulate with the C program `c/transient.c`, compiled to PATH)
       (STATE = B for 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD, E for 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA)
Prints one line per overflow: index, d, M, the string (top bit first), the result, and the length of the simulated
stretch.
"""
import sys

STARTS = {"1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD": (69, 0, [0, 1]),
          "1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA": (311, 0, [1, 1, 1, 0, 0, 1, 1])}
# Steps of one count with t trailing 1-digits in the counter and r trailing ones in the string above b1, read off
# the step counts of the lemmas of lean/Count.lean: carry 3t (5t for the sibling), erase 3t+6 (3t+8), walk 8r+24.
COST = {"1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD": (30, 6, 8),
        "1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA": (32, 8, 8)}


def counts_cost(m, v0, u0, c):
    """Steps of c counts from counter value v0 and string value u0: sum of a + b·t + e·r."""
    a, b, e = COST[m]
    st = c + bin(v0).count("1") - bin(v0 + c).count("1")
    sr = c + bin(u0).count("1") - bin(u0 + c).count("1")
    return a * c + b * st + e * sr


def val(bits):
    return sum(b << i for i, b in enumerate(bits))


def tobits(v, n):
    return [(v >> i) & 1 for i in range(n)]


def transient(m, S, left, right, limit):
    """Simulate from `left S> right` (cell lists, left to right) to the next P configuration."""
    tr = [(int(t[0]), 1 if t[1] == "R" else -1, "ABCDEF".index(t[2])) if t[2] != "-" else None
          for x in m.split("_") for t in (x[:3], x[3:])]
    s = "ABCDEF".index(S)
    pad = 64
    tape = bytearray(pad) + bytearray(left) + bytearray(right) + bytearray(pad)
    p = pad + len(left)
    q = s
    hi = len(tape) - pad - 1
    while tape[hi] == 0:
        hi -= 1
    n = 0
    while n < limit:
        x = tape[p]
        t = tr[2 * q + x]
        if t is None:
            return ("HALT", n)
        if n and q == s and x == 0 and hi > p and (hi - p) % 3 == 2 and tape[hi] == 1 and not any(tape[p + 1:hi]):
            l0 = 0
            while tape[l0] == 0:
                l0 += 1
            w = tape[l0:p]
            if len(w) % 2 == 0 and w[:2] == b"\1\1" and w[-2:] == b"\0\1" and all(w[3::2]):
                bits = list(w[2:-2:2])[::-1]
                return (n, (hi - p - 2) // 3, bits)
        tape[p] = t[0]
        if t[0] and p > hi:
            hi = p
        elif not t[0] and p == hi:
            while tape[hi] == 0:
                hi -= 1
        p += t[1]
        q = t[2]
        n += 1
        if p < 2:
            tape = bytearray(1024) + tape
            p += 1024
            hi += 1024
        if p >= len(tape) - 2:
            tape += bytearray(1024)
    return ("LIMIT", n)


def transient_c(m, S, left, right, limit, exe):
    import subprocess
    inp = "".join(map(str, left)) + " " + "".join(map(str, right)) + "\n"
    out = subprocess.run([exe, m, S, str(limit)], input=inp, capture_output=True, text=True).stdout.split()
    if out[0] != "P":
        return (out[0], int(out[1]))
    return (int(out[1]), int(out[2]), [int(c) for c in out[3]][::-1] if len(out) > 3 else [])


def run(m, S, overflows, quiet=False, limit=10 ** 9, exe=None):
    T, d, bs = STARTS[m]
    k = 0
    phases = 0
    while k < overflows:
        rest = bs[1:]
        if len(rest) >= d and 0 in rest[d:]:
            T += counts_cost(m, 1 << d, val(rest), 1 << d)
            h = rest[d:]
            i = h.index(0)
            h = [0] * i + [1] + h[i + 1:]
            bs = [bs[0]] + rest[:d] + h
            d += 1
            phases += 1
            continue
        M = len(bs)
        c = (1 << (M - 1)) - 1 - val(rest)
        assert 0 <= c < (1 << d)
        T += counts_cost(m, 1 << d, val(rest), c)
        T0 = T
        left = [1, 1] + [x for b in [1] * (M - 1) + [bs[0]] for x in (b, 1)] + [0, 1]
        right = [x for b in tobits((1 << d) + c, d + 1) for x in (0, 0, b)]
        res = transient_c(m, S, left, right, limit, exe) if exe else transient(m, S, left, right, limit)
        k += 1
        if res[0] in ("HALT", "LIMIT"):
            print(f"overflow {k}: d={d} M={M} bits={''.join(map(str, bs[::-1]))}: {res}")
            return
        n, d2, bs2 = res
        T += n
        if not quiet or k % 1000 == 0:
            print(f"overflow {k} (after {phases} phases), step {T0}: d={d} M={M} c={c} bits={''.join(map(str, bs[::-1]))[:80]}"
                  f" -> step {T}: d={d2} M={len(bs2)} bits={''.join(map(str, bs2[::-1]))[:80]}  ({n} steps simulated)")
        d, bs = d2, bs2


if __name__ == "__main__":
    exe = next((a[4:] for a in sys.argv if a.startswith("--c=")), None)
    run(sys.argv[1], sys.argv[2], int(sys.argv[3]), "--quiet" in sys.argv, limit=10 ** 13 if exe else 10 ** 9, exe=exe)
