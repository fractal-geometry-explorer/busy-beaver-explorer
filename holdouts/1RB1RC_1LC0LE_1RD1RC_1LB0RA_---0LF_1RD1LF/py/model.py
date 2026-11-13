"""The digit map of lean/Wave.lean, with exact step counts, checked against a direct run.

A cycle start S0 ds is the tape  0^inf 1^dn 0 ... 1^d0 0 1^14 0 1^7 0 1^6 0 1^4 0 C> 1 0^inf  (ds = [d0, ..., dn],
nearest the head first).  `cycle` applies one cycle: the wave starts on x + 61 (x = d0) and moves left; on an odd
value a it leaves a//2 + 1 behind and adds a//2 to the next digit; on an even value it stops.  At the left end of
the tape (no next digit) a = 1 halts.  Step counts are the sums of the rules in lean/Rules.lean.

usage: python3 model.py check [STEPS]      direct simulation to STEPS (default 2*10^7), every cycle start compared
       python3 model.py run CYCLES         iterate the map, print every wave that reaches the left end
       (this copy defaults to TWIN=1, the machine of this folder; TWIN=0 for 1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF)
"""
import os, sys

TWIN = os.environ.get("TWIN", "1") == "1"
if TWIN:
    M, START, CYC, S0STATE = "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF", 6053, 5009, 0
else:
    M, START, CYC, S0STATE = "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF", 6517, 5369, 2
FIRST = [26, 13, 9, 6]


def cost_odd(j):        # W (2j+3): w2z, j zigzags, zend1
    return (2 * j * j + 13 * j + 15) if not TWIN else (2 * j * j + 11 * j + 13)


def cost_even(j, ps):   # W (2j+2): w2z, j zigzags, the end, the run back
    if not TWIN:
        return (2 * j + 5) + 2 * j * j + 9 * j + (j + 6) + sum(p + 3 for p in ps) + 42
    return (2 * j + 5) + 2 * j * j + 7 * j + (j + 5) + sum(p + 1 for p in ps) + 37


def cycle(ds):
    """(next digits or None for a halt, steps, the wave value on the leftmost digit or None)."""
    x, rs, ps = ds[0], list(ds[1:]), []
    a, steps, a0 = x + 61, CYC, None
    while True:
        left = not rs
        y = rs.pop(0) if rs else 0
        if left and a0 is None:
            a0 = a
        if left and a == 1:
            return None, steps, a0
        if a % 2:
            j = (a - 3) // 2
            steps += cost_odd(j)
            a = y + j + 1
            ps.insert(0, j + 2)
        else:
            j = (a - 2) // 2
            steps += cost_even(j, ps)
            return list(reversed(ps)) + [j + 4, y + j + 1] + rs, steps, a0


def starts(limit):
    """Direct simulation: (step, digits) at every cycle start up to `limit` steps."""
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
    from bbtools.machine import Machine
    tab = Machine.parse(M).table
    n = 1 << 16
    t = bytearray(n)
    h, st, k, hi = n // 2, 0, 0, n // 2
    out = []
    while k < limit:
        tr = tab[st][t[h]]
        if tr is None:
            break
        w, d, s = tr
        t[h] = w
        h += d
        st = s
        k += 1
        hi = max(hi, h)
        if st == S0STATE and h == hi and t[h] == 1:
            cells = bytes(t[:h]).lstrip(b"\x00")
            blocks = [len(b) for b in cells.split(b"\x00")[:-1]]
            if blocks[-4:] == [14, 7, 6, 4]:
                out.append((k, blocks[:-4][::-1]))
    return out


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "check":
        limit = int(float(sys.argv[2])) if len(sys.argv) > 2 else 2 * 10 ** 7
        ev = starts(limit)
        assert ev[0] == (START, FIRST), ev[0]
        for (k1, a), (k2, b) in zip(ev, ev[1:]):
            nxt, s, _ = cycle(a)
            assert nxt == b and k1 + s == k2, (k1, a, nxt, b, s, k2 - k1)
        print(f"{len(ev)} cycle starts up to step {limit}: the map and its step counts agree with the run")
    else:
        n = int(float(sys.argv[2]))
        ds, steps = FIRST, START
        for i in range(1, n + 1):
            ds, s, a0 = cycle(ds)
            steps += s
            if ds is None:
                print(f"halts in cycle {i}, after {steps} steps")
                return
            if a0 is not None:
                t = (a0 ^ (a0 + 1)).bit_length() - 1
                print(f"cycle {i}: step {steps:.4e}, {len(ds)} digits, wave value on the leftmost digit "
                      f"{a0} ({a0.bit_length()} bits, {t} trailing 1s)")
        print(f"{n} cycles, {steps} steps ({steps:.3e}), no halt; {len(ds)} digits, largest {max(ds)}")


if __name__ == "__main__":
    main()
