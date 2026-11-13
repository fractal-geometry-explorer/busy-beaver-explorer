"""The run of 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF as an arithmetic iteration (the definitions of lean/Phase.lean).

    P c u x  =  0^inf 1^c (01)^u 0 0 (10)^x F> 0^inf

A phase: P (c+4) u x -> P c u' x' with X = x + u + 4, u' = 2 + X % 2, x' = 3 (X // 2) - 1.
An epoch starts at P c 3 5, makes c // 4 phases and ends by `endv` (a new epoch P c' 3 5, or a halt).

usage:
  epochs.py               the epochs from blank tape, as far as they can be computed (epochs 0..3, then the size of 4)
  epochs.py check N       compare the model with an exact accelerated simulation for the first N phase/epoch states
  epochs.py ends          check the eight epoch-end cases on the simulator for x = 1000, 1001, 1002
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fastsim import Sim  # noqa: E402

M = "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"


def ph(u, x):
    X = x + u + 4
    return 2 + X % 2, 3 * (X // 2) - 1


def endv(r, u, x):
    if r == 3:
        return 2 * x + 4 + 2 * u
    if (r == 0 and u == 3) or (r == 1 and u == 2):
        return 2 * x + 5
    return None


def ends(c):
    u, x = 3, 5
    for _ in range(c // 4):
        u, x = ph(u, x)
    return endv(c % 4, u, x)


def fmt(n):
    return f"{n:,}" if n.bit_length() < 64 else f"~10^{int(n.bit_length() * 0.30103)}"


# --- the accelerated simulator: the bounce rule applied k times at once (proved in Lean as `bounce_iter`) ---

def jump(s):
    """`L (01)^2X 0 0 (10)^2Y F>` with X >= 4: k = X//2 - 1 bounces at once (`bounce`, 4y+18 steps each)."""
    c = s.cfg
    if c.state != 5 or len(c.right) != 1:
        return False
    L = s.left_segs()
    if len(L) < 3:
        return False
    a, z, b = L[-3], L[-2], L[-1]
    if not (a[0] == 'A' and a[1] == 0 and a[2] % 2 == 0 and z == ('R', 0, 2) and b[0] == 'A' and b[1] == 1
            and b[2] % 2 == 0):
        return False
    X, Y = a[2] // 2, b[2] // 2
    if X < 4 or Y < 1:
        return False
    k = X // 2 - 1
    s.set(L[:-3] + [('A', 0, 2 * (X - 2 * k)), ('R', 0, 2), ('A', 1, 2 * (Y + 3 * k))], 5, [],
          k * (4 * Y + 14) + 6 * k * (k - 1))
    return True


def jump2(s):
    """The same bounce at an epoch end, where the block of (01) is preceded by nothing and the head is in state E."""
    c = s.cfg
    if c.state != 4 or len(c.right) != 1:
        return False
    L = s.left_segs()
    if len(L) != 3:
        return False
    a, z, b = L
    if not (a[0] == 'A' and a[1] == 1 and a[2] % 2 == 1 and z == ('R', 0, 2) and b[0] == 'A' and b[1] == 1
            and b[2] % 2 == 1):
        return False
    Y, Z = (a[2] + 1) // 2, (b[2] + 1) // 2
    if Y < 4 or Z < 1:
        return False
    k = Y // 2 - 1
    s.set([('A', 1, 2 * (Y - 2 * k) - 1), ('R', 0, 2), ('A', 1, 2 * (Z + 3 * k) - 1)], 4, [],
          k * (4 * Z + 14) + 6 * k * (k - 1))
    return True


PAT = re.compile(r'^(?:1\^(\d+) |(1) )?\(01\)\^(\d+) 0\^2 \(10\)\^(\d+) F> $')


def p_state(s):
    if s.cfg.state != 5 or len(s.cfg.right) != 1:
        return None
    m = PAT.match(str(s))
    if not m:
        return None
    c = int(m[1]) if m[1] else (1 if m[2] else 0)
    return c, int(m[3]), int(m[4])


def check(n, moves=10 ** 7):
    s = Sim(M, [jump, jump2])
    seen, last, bad = [], None, 0
    for _ in range(moves):
        if s.move() == 'halt':
            print("halt at", s.steps)
            break
        p = p_state(s)
        if p is None or p[1] not in (2, 3):
            continue
        if last is not None:
            c, u, x = last
            if c >= 4:
                exp = (c - 4,) + ph(u, x)
                if exp[:2] == (1, 2) and p == (endv(1, 2, exp[2]), 3, 5):
                    exp = p  # P 1 2 x is the same tape as P 0 3 x and is not matched; its epoch end follows
                if exp != p:
                    print("MISMATCH", last, "->", p, "model", exp)
                    bad += 1
            else:
                e = endv(c, u, x)
                if (e, 3, 5) != p:
                    print("END MISMATCH", last, "->", p, "model", e)
                    bad += 1
        seen.append(p)
        last = p
        if len(seen) >= n:
            break
    print(len(seen), "P states checked, mismatches:", bad, "; epoch starts:",
          [p[0] for p in seen if p[1:] == (3, 5)], "; at step", fmt(s.steps))


def check_ends():
    for c in range(4):
        for u in (2, 3):
            out = []
            for x in (1000, 1001, 1002):
                s = Sim(M, [jump, jump2])
                s.set(([('R', 1, c)] if c else []) + [('A', 0, 2 * u), ('R', 0, 2), ('A', 1, 2 * x - 1), ('R', 0, 1)],
                      5, [])
                res = "TIMEOUT"
                for _ in range(20000):
                    if s.move() == 'halt':
                        res = "HALT"
                        break
                    p = p_state(s)
                    if p and p[1:] == (3, 5):
                        res = p[0]
                        break
                e = endv(c, u, x)
                ok = (res == "HALT" and e is None) or res == e
                out.append(f"x={x}: {res}{'' if ok else ' MISMATCH (model ' + str(e) + ')'}")
            print(f"P {c} {u} x:", ", ".join(out))


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "check":
        check(int(sys.argv[2]) if len(sys.argv) > 2 else 300)
        return
    if len(sys.argv) > 1 and sys.argv[1] == "ends":
        check_ends()
        return
    c = 3
    for k in range(4):
        print(f"epoch {k}: P {fmt(c)} 3 5   ({c // 4:,} phases, c % 4 = {c % 4})")
        if k < 3:
            c = ends(c)
    N = 459271258863231 // 4
    print(f"epoch 3 has 3 % 4 = 3, so it ends in a new epoch 4: P c4 3 5, c4 = 2 x + 4 + 2 u after {N:,} phases;")
    print(f"c4 has about {int(N * 0.17609):,} digits and c4 % 4 = 2 (x + u) % 4: epoch 4 halts at its end if x + u")
    print("is odd at the end of epoch 3, and otherwise unless its own last phase leaves u = 3 (heuristic chance 3/4).")


if __name__ == "__main__":
    main()
