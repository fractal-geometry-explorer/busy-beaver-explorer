"""The sample map of 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE, checked against the machine, and iterated.

K(p, q) = 0^inf A> 0 1^p 0 1^q 0^inf.  The map (every case proved in lean/Macro.lean, the reduction in lean/Reduction.lean):
    p odd >= 3:  (p, q) -> ((p - 3)/2, q + (p + 5)/2)
    p even >= 2: (p, q) -> (3p/2 + q, 1)
    p = 0:       (0, q) -> (2, q - 1)
    p = 1:       halt
usage: python3 kmap.py [ITERATIONS]
"""
import sys

sys.set_int_max_str_digits(0)
TABLE = "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"


def parse(m):
    t = []
    for g in m.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s[2] not in "ABCDEF" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


TT = parse(TABLE)


def run_K(p, q, maxsteps=10 ** 8):
    """Run the machine from K(p, q) to the next time A is at the left end on a 0: (p', q', steps) or ('HALT', steps)."""
    tape = {i: c for i, c in enumerate([0] + [1] * p + [0] + [1] * q)}
    pos, st, n, lo = 0, 0, 0, 0
    while n < maxsteps:
        tr = TT[st][tape.get(pos, 0)]
        if tr is None:
            return ("HALT", n)
        w, d, st = tr
        tape[pos] = w
        pos += d
        n += 1
        lo = min(lo, pos)
        if st == 0 and pos == lo and tape.get(pos, 0) == 0:
            hi = max(k for k, v in tape.items() if v)
            parts = "".join(str(tape.get(i, 0)) for i in range(pos + 1, hi + 1)).split("0")
            return (len(parts[0]), len(parts[1]), n) if len(parts) == 2 else ("other", parts, n)
    return ("TO", n)


def f(p, q):
    if p == 1:
        return None
    if p == 0:
        return (2, q - 1)
    if p % 2:
        return ((p - 3) // 2, q + (p + 5) // 2)
    return (3 * p // 2 + q, 1)


def check(P=40, Q=20):
    bad = 0
    for p in range(P):
        for q in range(2 if p == 0 else 1, Q):
            r = run_K(p, q)
            want = f(p, q)
            if (want is None and r[0] != "HALT") or (want is not None and r[:2] != want):
                bad += 1
    return bad


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    print("map checked against the machine for p < 40, 1 <= q < 20 (q >= 2 when p = 0): mismatches =", check())
    p, q = 0, 2
    seq = []
    for i in range(n):
        if i < 25:
            seq.append((p, q))
        r = f(p, q)
        if r is None:
            print("HALT at iteration", i)
            return
        p, q = r
    print("first samples:", " ".join(f"K({a},{b})" for a, b in seq))
    print(f"{n} iterations from K(0, 2), no halt; p has {p.bit_length()} bits, q has {q.bit_length()} bits")


if __name__ == "__main__":
    main()
