"""The separator counter of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD (and of 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA).

At an *event* the head is at the right end of the tape on blank, in state B (E for the other machine), and the tape
is a list of blocks of 1s separated by single 0s:  `1^x1 0 1^x2 0 ... 0 1^xr 0 1^N  S>0`.  The left part
`x1 ... xr` (x1 >= 2) is read as a bit string: after the first two 1s the cells come in pairs (separator, 1), and a
separator cell that is 1 is a set bit.  The first separator is the top bit.

Model (checked here): if the bit string has M bits and j = (N+2)/3 < M, the next event is the bit string plus 2^j
(bit j counted from the right, carries going left) and N+3, as long as the addition does not carry out of the top bit.

usage:
  python3 bitmodel.py events MACHINE STATE LOG      check every event of a `tmrun MACHINE T at STATE R` log
  python3 bitmodel.py exhaust MACHINE STATE M       every M-bit string and every j <= M, by direct simulation
"""
import re
import sys


def blocks(line):
    out = []
    for tok in line.split():
        if ">" in tok:
            tok = tok.split(">")[1]
        if "^" in tok:
            c, n = tok.split("^")
            out += [c] * int(n)
        else:
            out.append(tok)
    cells = "".join(out).strip("0")
    if "00" in cells:
        return None
    return [len(x) for x in cells.split("0")]


def to_bits(L):
    if not L or L[0] < 2:
        return None
    cells = []
    for i, x in enumerate(L):
        if i:
            cells.append(0)
        cells += [1] * x
    rest = cells[2:]
    if len(rest) % 2 or any(rest[2 * i + 1] != 1 for i in range(len(rest) // 2)):
        return None
    return [rest[2 * i] for i in range(len(rest) // 2)]


def from_bits(bits):
    s = "11" + "".join(f"{b}1" for b in bits)
    return [len(x) for x in s.split("0")]


def add(bits, j):
    b = bits[:]
    i = len(b) - 1 - j
    if i < 0:
        return None
    while i >= 0 and b[i] == 1:
        b[i] = 0
        i -= 1
    if i < 0:
        return None
    b[i] = 1
    return b


def simulate(m, L, N, state, limit=10 ** 8):
    """Run from `L 0 1^N S>` (blank around) to the next event; returns (steps, blocks) or ('HALT', steps)."""
    tr = m.split("_")
    cells = "0".join("1" * x for x in L + [N])
    tape = {i: int(c) for i, c in enumerate(cells)}
    p, q, n, hi = len(cells), state, 0, len(cells)
    while n < limit:
        x = tape.get(p, 0)
        t = tr["ABCDEF".index(q)][3 * x:3 * x + 3]
        if t[2] == "-":
            return "HALT", n
        tape[p] = int(t[0])
        p += 1 if t[1] == "R" else -1
        q = t[2]
        n += 1
        if p > hi:
            hi = p
        if q == state and p == hi and all(tape.get(k, 0) == 0 for k in range(p, p + 1)):
            if max(k for k, v in tape.items() if v) < p:
                lo = min(k for k, v in tape.items() if v)
                s = "".join(str(tape.get(k, 0)) for k in range(lo, p)).strip("0")
                if "00" not in s:
                    return n, [len(y) for y in s.split("0")]
    return None, n


def events(m, state, log):
    rows = []
    for line in open(log):
        p = line.split(None, 1)
        if len(p) == 2 and p[0].isdigit():
            b = blocks(p[1])
            if b:
                rows.append((int(p[0]), b[:-1], b[-1]))
    ok = bad = 0
    for (t, L, N), (t2, L2, N2) in zip(rows, rows[1:]):
        bits, bits2 = to_bits(L), to_bits(L2)
        if bits is None or (N + 2) % 3:
            continue
        nb = add(bits, (N + 2) // 3)
        if nb is None:
            print(f"step {t2}: carry out of the top bit (N={N}): {L} -> {L2}, N {N2}")
            continue
        if nb == bits2 and N2 == N + 3:
            ok += 1
        else:
            bad += 1
            print(f"step {t2}: MISMATCH {L} N={N} -> {L2} N={N2}")
    print(f"{ok} events follow the model, {bad} do not")


def exhaust(m, state, M):
    from itertools import product
    ok = bad = 0
    for bits in product([0, 1], repeat=M):
        bits = list(bits)
        for j in range(1, M + 1):
            N = 3 * j - 2
            r, res = simulate(m, from_bits(bits), N, state)
            nb = add(bits, j)
            if r == "HALT":
                print(f"HALT: bits {''.join(map(str, bits))}, N={N} (j={j}), after {res} steps")
            elif nb is not None:
                if res[:-1] == from_bits(nb) and res[-1] == N + 3:
                    ok += 1
                else:
                    bad += 1
                    print(f"MISMATCH bits {bits} j={j}: {res}")
    print(f"M={M}: {ok} additions follow the model, {bad} do not")


if __name__ == "__main__":
    if sys.argv[1] == "events":
        events(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        exhaust(sys.argv[2], sys.argv[3], int(sys.argv[4]))
