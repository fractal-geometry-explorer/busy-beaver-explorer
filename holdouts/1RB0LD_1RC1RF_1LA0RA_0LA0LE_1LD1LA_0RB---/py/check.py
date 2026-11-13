"""Compare the macro machine of 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB--- with a direct run.
usage: python3 check.py STEPS.  At each predicted wall time t (from the macro orbit with its step counts) the direct
run must be in state A at the left end of the visited tape, with the tape A>0 0 10 0^z (10)^y 0 1 and blank
beyond; and no other configuration of the run may be a wall (A at a fresh left end reading 0 0 1 0)."""
import sys
M = "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---"
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7

def walls(limit):
    z, y, t = 0, 0, 7
    while t <= limit:
        yield t, z, y
        k, r = divmod(z, 3)
        if r and y == 0:
            return
        t += 4 * k * k + 7 * k + [8 * k + 8 * y + 37, 16 * k + 16 * (y - 1) + 110, 16 * k + 28][r]
        z, y = [(4 * k + 1, y + 4), (4 * k + 5, y + 6), (4 * k + 8, y - 1)][r]

T = {}
for i, g in enumerate(M.split("_")):
    for r in (0, 1):
        w = g[3 * r:3 * r + 3]
        T[(i, r)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, ord(w[2]) - 65)
size = 1 << 22
tape = bytearray(size); p = size // 2; s = 0; lo = hi = p
W = list(walls(N)); wi = 0; ok = 0
for n in range(N + 1):
    if wi < len(W) and W[wi][0] == n:
        _, z, y = W[wi]
        want = "00" + "10" + "0" * z + "10" * y + "01"
        got = "".join("01"[b] for b in tape[p:max(hi, p + len(want) - 1) + 1])
        assert s == 0 and p == lo and got == want and not any(tape[lo:p]), (n, z, y)
        ok += 1; wi += 1
    elif s == 0 and p == lo and tape[p] == 0 and tape[p + 1:p + 4] == b"\x00\x01\x00" and n > 0:
        raise SystemExit(f"unexpected wall at step {n}")
    if n == N:
        break
    t = T[(s, tape[p])]
    if t is None:
        raise SystemExit(f"halt at {n}")
    tape[p] = t[0]; p += t[1]; s = t[2]; lo = min(lo, p); hi = max(hi, p)
print(f"{N} steps: {ok} walls, all at the predicted times with the predicted tapes")
