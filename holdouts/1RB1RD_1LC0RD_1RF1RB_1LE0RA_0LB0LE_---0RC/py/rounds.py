"""Rounds of 1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC, by direct simulation (c/evc.c), and the one-block rule.

usage: python3 rounds.py check N      compare the one-block rule with simulation for every n < N
       python3 rounds.py orbit K      the first K round starts from blank tape (simulated; slow beyond 12)

A round start is `B> 0 0 1^a 0 1^b ...` with the head at the left end (blocks a, b, ...).  The rule found for one
block n (computed, see README): write n = 6^j * m + (6^j - 1)/5 with m not = 1 mod 6 (j = number of trailing base-6
digits 1), then
  m = 0:              halt          (n = 0, 1, 7, 43, 259, ...: base-6 repunits)
  m even, m > 0:      n + 3m/2 + 1 + j
  m = 3 mod 6:        n + 3 + j
  m = 6q + 5:         two blocks (n - q + 1 + j, q + 1)
For j = 0 and even n this is n -> 5n/2 + 1, proved in Lean (`even_round`).
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC"


def evc():
    exe = os.path.join("/tmp", "evc_135376")
    if not os.path.exists(exe):
        subprocess.check_call(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "evc.c")])
    return subprocess.Popen([exe, M, "B", "100000000000"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)


def nxt(p, blocks):
    p.stdin.write(" ".join(map(str, blocks)) + "\n")
    p.stdin.flush()
    w = p.stdout.readline().split()
    if w[0] != "ev":
        return w[0], 0
    return tuple(int(x) for x in w[3:]), int(w[1])


def rule(n):
    j, m = 0, n
    while m % 6 == 1:
        m //= 6
        j += 1
    if m == 0:
        return "halt"
    if m % 2 == 0:
        return (n + 3 * m // 2 + 1 + j,)
    if m % 6 == 3:
        return (n + 3 + j,)
    q = (m - 5) // 6
    return (n - q + 1 + j, q + 1)


def main(argv):
    p = evc()
    if argv[0] == "check":
        bad = 0
        for n in range(int(argv[1])):
            got = nxt(p, [n] if n else [])[0] if n else "halt"
            if got != rule(n):
                print("mismatch", n, got, rule(n))
                bad += 1
        print(f"one-block rule checked for n < {argv[1]}: {bad} mismatches")
    else:
        s, t = (2,), 9
        for i in range(int(argv[1])):
            s, dt = nxt(p, list(s))
            t += dt
            print(i + 1, t, s, flush=True)
            if not isinstance(s, tuple):
                break


if __name__ == "__main__":
    main(sys.argv[1:])
