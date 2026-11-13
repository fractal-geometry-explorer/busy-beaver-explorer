"""The macro map of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD: phases of additions and overflows, on integers.

State at an event: X (the bit string as a number), M (its length), N (the right block; j = (N+2)/3).
* event: X + 2^j if that is < 2^M (then N += 3), cost 22·2^j − 11 + 8·(ones cleared by the carry) steps;
* overflow: R = X + 2^j − 2^M.  R even: X = R + 1, M += 1, N += 3.  R odd: let k be the number of trailing pairs
  of bits (from the lowest) whose low bit is 1, r = R mod 4^k: X = C(r) + (R >> 2k), M += 3k + 1, N −= 3(2k − 1).
  C(r) is given by a recursion found from runs of the machine (see `C`); the case where those odd pairs reach the top
  bit (the all-ones string among them) is reported, not modelled: it is where the machine can halt.
usage: python3 macro.py 0 checkC [K]      check the formula for C against the machine, k <= K
       python3 macro.py 0 checkO M          every overflow with at most M bits, the machine against the map
       python3 macro.py PHASES            iterate from the first event, print every overflow
       python3 macro.py PHASES check LOG  compare the overflows with a `tmrun ... at B R` log
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bitmodel import blocks, to_bits, from_bits  # noqa: E402

MACH = "1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD"


def run_overflow(r, k):
    """C(r) by running the machine on the (2k+1)-bit string r with j = M."""
    M = 2 * k + 1
    bits = [int(c) for c in format(r, f"0{M}b")]
    N = 3 * M - 2
    tr = MACH.split("_")
    cells = "0".join("1" * x for x in from_bits(bits) + [N])
    pad = 64 + 4 * M
    tape = bytearray(pad) + bytearray(1 if c == "1" else 0 for c in cells) + bytearray(64)
    p, q, n = pad + len(cells), "B", 0
    rmax = p - 1
    while True:
        x = tape[p]
        t = tr["ABCDEF".index(q)][3 * x:3 * x + 3]
        assert t[2] != "-", "halt inside an overflow"
        w = int(t[0]); tape[p] = w
        if w and p > rmax: rmax = p
        if not w and p == rmax:
            while tape[rmax] == 0: rmax -= 1
        p += 1 if t[1] == "R" else -1
        q = t[2]; n += 1
        if p >= len(tape) - 2: tape += bytearray(1024)
        assert p > 0, "ran off the left padding"
        if q == "B" and p == rmax + 1:
            lo = next(i for i in range(len(tape)) if tape[i])
            s = bytes(tape[lo:rmax + 1]).decode("latin1").replace("\x01", "1").replace("\x00", "0")
            if "00" not in s:
                L = [len(y) for y in s.split("0")]
                b = to_bits(L[:-1])
                X = int("".join(map(str, b)), 2)
                assert len(b) - M == 3 * k + 1 and (L[-1] - N) == -3 * (2 * k - 1), (r, k, b, L[-1])
                return X, n


def c_t(t):
    return 42 if t == 0 else 248 * 4 ** (t - 1) - 21


def C(r, k):
    """C(r) for the k odd pairs r (each pair 01 or 11, lowest first), by the recursion found from the runs:
    C(01) = 43, C(11) = 104; for k >= 2 with t trailing 11 pairs, C(r) = C(r >> 2) + c_t 8^(k-1) if t < k and
    C(r >> 2) + (2 c_(k-1) + 21) 8^(k-1) if t = k, where c_0 = 42 and c_t = 248·4^(t-1) − 21.  Checked against
    the machine on all patterns with k <= 6 and on random ones with k = 7, 8 (`python3 macro.py 0 checkC`)."""
    if k == 1:
        return 43 if r == 1 else 104
    t = 0
    while t < k and (r >> (2 * t)) & 3 == 3:
        t += 1
    if t < k:
        return C(r >> 2, k - 1) + c_t(t) * 8 ** (k - 1)
    return C(r >> 2, k - 1) + (2 * c_t(k - 1) + 21) * 8 ** (k - 1)


def check_C(kmax=6):
    from itertools import product
    bad = n = 0
    for k in range(1, kmax + 1):
        for hs in product([0, 1], repeat=k):
            r = sum((2 * h + 1) << (2 * i) for i, h in enumerate(hs))
            n += 1
            bad += run_overflow(r, k)[0] != C(r, k)
    print(f"C(r) against the machine: {n} patterns, {bad} differ")


def overflow(R, M, N):
    """(X, M, N) after an overflow with remainder R; None if the odd pairs reach the top bit."""
    if R % 2 == 0:
        return R + 1, M + 1, N + 3
    k, s = 0, R
    while s & 1:
        k += 1
        s >>= 2
        if 2 * k >= M:
            return None
    r = R & ((1 << 2 * k) - 1)
    X, M2, N2 = C(r, k) + (R >> 2 * k), M + 3 * k + 1, N - 3 * (2 * k - 1)
    if N2 == -2:          # the right block cannot be shorter than 1: one bit fewer
        X, M2, N2 = X >> 1, M2 - 1, 1
    elif N2 < 1:
        raise ValueError(f"overflow leaves N = {N2}: not modelled")
    return X, M2, N2


def phases(X, M, N, count):
    """Yield (events in the phase, j at the overflow, M, R, k-or-'even', new X, M, N)."""
    for _ in range(count):
        j = (N + 2) // 3
        t = 0
        while X + (1 << j) < (1 << M):
            X += 1 << j; j += 1; N += 3; t += 1
        R = X + (1 << j) - (1 << M)
        new = overflow(R, M, N)
        yield t, j, M, R, new
        if new is None:
            return
        X, M, N = new


def check_overflows(Mmax):
    """Every bit string with M <= Mmax bits and every j <= M whose addition carries out: the machine against
    `overflow` (cases where the odd pairs reach the top bit are run and reported separately)."""
    from itertools import product
    sys.path.insert(0, HERE)
    agree = differ = top = halts = 0
    for M in range(1, Mmax + 1):
        for bits in product([0, 1], repeat=M):
            X = int("".join(map(str, bits)), 2)
            for j in range(1, M + 1):
                if X + (1 << j) < (1 << M):
                    continue
                N = 3 * j - 2
                R = X + (1 << j) - (1 << M)
                got = first_event(from_bits(list(bits)), N)
                exp = overflow(R, M, N)
                if got == "HALT":
                    halts += 1
                    print(f"  halts: bits {''.join(map(str, bits))}, j={j}, R={R:b}, top case: {exp is None}")
                elif exp is None:
                    top += 1
                elif got == exp:
                    agree += 1
                else:
                    differ += 1
                    print("  differ", bits, j, got, exp)
    print(f"M <= {Mmax}: {agree} overflows agree with the map, {differ} differ, {top} top cases run (no halt), "
          f"{halts} halt")


def first_event(L, N, limit=10 ** 8):
    """(X, M, N) at the first event after `L 0 1^N B>0`, or 'HALT'."""
    tr = MACH.split("_")
    cells = "0".join("1" * x for x in L + [N])
    pad = 64 + 4 * len(cells)
    tape = bytearray(pad) + bytearray(1 if c == "1" else 0 for c in cells) + bytearray(64)
    p, q, n = pad + len(cells), "B", 0
    rmax = p - 1
    while n < limit:
        x = tape[p]
        t = tr["ABCDEF".index(q)][3 * x:3 * x + 3]
        if t[2] == "-":
            return "HALT"
        w = int(t[0]); tape[p] = w
        if w and p > rmax: rmax = p
        if not w and p == rmax:
            while tape[rmax] == 0: rmax -= 1
        p += 1 if t[1] == "R" else -1
        q = t[2]; n += 1
        if p >= len(tape) - 2: tape += bytearray(1024)
        if q == "B" and p == rmax + 1:
            lo = next(i for i in range(len(tape)) if tape[i])
            s = "".join("1" if v else "0" for v in tape[lo:rmax + 1])
            if "00" not in s:
                L2 = [len(y) for y in s.split("0")]
                b = to_bits(L2[:-1])
                if b is not None:
                    return int("".join(map(str, b)), 2), len(b), L2[-1]
    return None


if __name__ == "__main__":
    n = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == "checkC":
        check_C(int(sys.argv[3]) if len(sys.argv) > 3 else 6)
        sys.exit()
    if len(sys.argv) > 2 and sys.argv[2] == "checkO":
        check_overflows(int(sys.argv[3]))
        sys.exit()
    # the event at step 39: tape 1^2 0 1 0 1 0 1 B>0 -> blocks [2, 1, 1] and N = 1
    X, M, N = 0, 2, 1
    out = list(phases(X, M, N, n))
    if len(sys.argv) > 2 and sys.argv[2] == "check":
        rows = []
        for line in open(sys.argv[3]):
            p = line.split(None, 1)
            if len(p) == 2 and p[0].isdigit():
                b = blocks(p[1])
                if b and to_bits(b[:-1]) is not None:
                    rows.append((int(p[0]), to_bits(b[:-1]), b[-1]))
        seen = []
        for (t, b, N), (t2, b2, N2) in zip(rows, rows[1:]):
            j = (N + 2) // 3
            if int("".join(map(str, b)), 2) + (1 << j) >= (1 << len(b)):
                seen.append((t2, int("".join(map(str, b2)), 2), len(b2), N2))
        for (st, X2, M2, N2), (_, j, M, R, new) in zip(seen, out):
            print(f"step {st}: run X={X2} M={M2} N={N2}; map {new}; {'agree' if new == (X2, M2, N2) else 'DIFFER'}")
    else:
        for i, (t, j, M, R, new) in enumerate(out):
            print(i, f"events {t}, overflow at j={j}, M={M}, R odd={R % 2}, ->",
                  "HALT CASE (odd pairs reach the top)" if new is None else f"M={new[1]} N={new[2]} j0={(new[2] + 2) // 3}")
