"""The phase map `phi` of lean/Map.lean in Python, checked against the machine.

usage: python3 phimap.py [PHASES]        (default 30000)

`phi(M, T)` is a copy of the Lean definition (T a list of blocks, `None` where Lean's map is not covered).
1. on every tail of up to 4 blocks of 0..7 ones and each M in 30..32, compares `phi` with `nextps` of phases.py
   (the plain machine) wherever `phi` is defined, and lists the uncovered cases that halt;
2. iterates `phi` from PS(9, []) for PHASES phases and checks that it never leaves the covered tails (the condition
   of `not_halts_of_covered`), and that it agrees with `phase` of phases.py on every phase; the same from the first
   phase starts of the three holdouts with the same table (lean/Twins.lean): PS(11, [6]), PS(15, []), PS(5, []).
"""
import itertools
import sys

from phases import M as M0, nextps, phase


def lead1(T):
    j = 0
    while j < len(T) and T[j] == 1:
        j += 1
    return j, list(T[j:])


def end2(k, T):
    j, r = lead1(T)
    if r in ([], [0]):
        return (2 * k + 3, [6]) if j == 0 and k >= 2 else ((2 * k + 3, [2 * j + 6]) if j > 0 else None)
    if r[0] == 0:
        return (2 * k + 3, [2 * j + 6 + r[1]] + r[2:])
    if r == [2]:
        return (2 * k + 1, [4, 1, 1, 1]) if j == 0 and k >= 1 else ((2 * k + 3, [2 * j + 2, 6]) if j > 0 else None)
    if r[0] >= 3:
        return (2 * k + 7, [1] * (j + 2) + [r[0] - 3] + r[1:])
    return None


def dend(k, m, T):
    T = list(T)
    while m == 1 and T:
        u = T.pop(0)
        k, m = k + 1 + 4 * (u // 3), u % 3
    if m == 0:
        return (2 * k + 7, []) if not T else (2 * k + 7 + T[0], T[1:])
    if m == 1:
        return (2 * k + 9, [])
    return end2(k, T)


def phi(M, T):
    if M < 5:
        return None
    return dend(5 + 4 * ((M - 5) // 3), (M - 5) % 3, T)


def norm(M, T):
    """Move leading ones of the tail into M and drop trailing empty blocks: the tape is the same."""
    T = list(T)
    while T and T[-1] == 0:
        T.pop()
    return M, tuple(T)


def main():
    sys.set_int_max_str_digits(0)
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
    checked, unc, unc_halt = 0, 0, 0
    for L in range(5):
        for T in itertools.product(range(8), repeat=L):
            if T and T[-1] == 0:
                continue
            for M in (30, 31, 32):
                r = phi(M, T)
                x = nextps(M, T)
                if r is None:
                    unc += 1
                    unc_halt += x[0] == "halt"
                    continue
                assert x[0] != "halt" and norm(*r) == norm(*x[:2]), (M, T, r, x)
                checked += 1
    print(f"phi agrees with the machine on {checked} (M, tail) pairs; {unc} uncovered, {unc_halt} of them halt")
    # this machine from blank tape, and the same table from blank tape in states F, C, B (lean/Twins.lean)
    for name, M, T in ((M0, 9, ()), ("1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA", 11, (6,)),
                       ("1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---", 15, ()),
                       ("1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---", 5, ())):
        start = (M, T)
        for i in range(n):
            r = phi(M, T)
            if r is None:
                print(f"{name}: phase {i}: tail {T} with M = {M % 3} mod 3 is not covered")
                break
            assert norm(*r) == phase(M, T), (i, M % 3, T)
            M, T = norm(*r)
        else:
            print(f"{name}: {n} phases from PS{start}: every tail covered, phi = phase throughout; M has "
                  f"{len(str(M))} digits")


if __name__ == "__main__":
    main()
