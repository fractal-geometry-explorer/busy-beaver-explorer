"""The S-map of 1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---: from an S-state `B>0 0 0 1^X 0 T` (T a short tail of
blocks of ones) to the next one, by direct simulation (c/sstate.c, compiled on the fly).

usage: python3 smap.py orbit [N]          the S-states from blank tape (the first is (41, (3,)) at step 855)
       python3 smap.py table [TAILS]      X' = (3X + c)/2 and the new tail, for X mod 6 and the tails met first

An S-state is the last time the head is at the left end in state B, on the tape `0 0 0 1^X 0 T` with X >= 10 and at
most 10 blocks in T, before a conversion sweep (a visit that reads a 1).  X' depends on X mod 6 and on the tail; the table prints c = 2X' - 3X.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---"
BIN = os.path.join("/tmp", "sstate_22465")


def build():
    if not os.path.exists(BIN):
        subprocess.check_call(["gcc", "-O2", "-o", BIN, os.path.join(HERE, "..", "c", "sstate.c")])


def tape(X, T):
    return "B>000" + "1" * X + "0" + "0".join("1" * t for t in T) + ("0" if T else "")


def next_s(X, T, maxsteps=10 ** 11):
    """(X', T', steps) of the next S-state, or ('HALT', steps)."""
    build()
    p = subprocess.Popen([BIN, M, str(maxsteps), tape(X, T), "100000000"], stdout=subprocess.PIPE, text=True)
    prev, first = None, True
    for line in p.stdout:
        f = line.split()
        if f[0] == "HALT":
            p.kill()
            return ("HALT", int(f[1]))
        if f[0] == "END":
            return ("END",)
        v0 = int(f[1])
        if v0 == 1 and prev is not None and not first:
            p.kill()
            r = list(map(int, prev[3:]))
            assert r[0] == 3, prev
            return (r[1], tuple(r[3::2]), int(prev[0]))
        if v0 == 1 and first:
            first = False
        prev = f if int(f[2]) <= 24 and int(f[1]) == 0 and int(f[3]) == 3 and int(f[4]) >= 10 else None
    return ("?",)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "orbit":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 14
        X, T, total = 41, (3,), 855
        print(f"step {total}: X = {X}, tail {T}")
        for _ in range(n):
            r = next_s(X, T)
            if len(r) != 3:
                print(r)
                return
            X, T, s = r
            total += s
            print(f"step {total}: X = {X}, tail {T}")
    else:
        tails = [(), (3,), (3, 3), (6,), (3, 6), (6, 3), (9,), (5, 3), (5, 2, 3), (3, 5, 2, 3)]
        for T in tails:
            row = []
            for r in range(6):
                X = 1200 + r
                res = next_s(X, T, 10 ** 10)
                row.append(f"{r}: c={2 * res[0] - 3 * X} {res[1]}" if len(res) == 3 else f"{r}: {res}")
            print(T, " | ".join(row))


if __name__ == "__main__":
    main()
