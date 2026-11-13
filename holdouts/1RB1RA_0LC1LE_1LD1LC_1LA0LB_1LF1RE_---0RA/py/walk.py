"""The Antihydra walk of `lean/Macro.lean`: (p, a) -> (p + 2, 3k + 4) for a = 2k + 1, (p - 1, 3k + 2) for a = 2k,
halting when a is even and p = 0.  The machine halts iff the walk does (`halts_iff`, Lean kernel).

    python3 py/walk.py orbit 30          # the first points of the orbit, with the machine step at which each is reached
    python3 py/walk.py run 1000000       # iterate, report the smallest p seen (after the start) and the final p
    python3 py/walk.py check 200000000   # compare the first points with a direct simulation of the machine
"""
import sys


def nxt(p, a):
    if a % 2 == 1:
        return p + 2, 3 * (a // 2) + 4
    if p == 0:
        return None
    return p - 1, 3 * (a // 2) + 2


def steps_of(p, a):
    """Machine steps from Q p a 2 to the next Q (sum of the Lean rules' step counts)."""
    if a % 2 == 1:
        k = a // 2 - 1          # a = 2(k+1) + 1: k + 1 sweeps, then odd_end with c = 3k + 3
        s = sum(2 * (1 + 3 * j) + 13 for j in range(k + 1))
        c = 3 * k + 3
        return s + (2 * c + 26 if p == 0 else (c + 2 * (p - 1) + 15) + (c + 13))
    k = a // 2 - 1              # a = 2k + 2: k sweeps, then even_end with c = 3k
    s = sum(2 * (1 + 3 * j) + 13 for j in range(k))
    return s + 2 * (3 * k) + 20


def orbit(n):
    p, a, t = 2, 7, 62
    out = [(0, p, a, t)]
    for i in range(1, n + 1):
        r = nxt(p, a)
        if r is None:
            out.append((i, None, None, t))
            break
        t += steps_of(p, a)
        p, a = r
        out.append((i, p, a, t))
    return out


def run(n):
    p, a = 2, 7
    lo = p
    for i in range(n):
        r = nxt(p, a)
        if r is None:
            return i, None, lo
        p, a = r
        lo = min(lo, p)
    return n, p, lo, a.bit_length()


def check(maxsteps):
    """Simulate the machine directly and compare the tape at every predicted step count."""
    sys.path.insert(0, __file__.rsplit("/", 2)[0] + "/../../tools/py")
    from bbtools.machine import Machine
    m = Machine.parse("1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA")
    pts = [x for x in orbit(40) if x[1] is not None and x[3] <= maxsteps]
    tape, pos, st, t = {}, 0, 0, 0
    for i, p, a, target in pts:
        while t < target:
            w, d, s = m.table[st][tape.get(pos, 0)]
            tape[pos] = w
            pos += d
            st = s
            t += 1
        lo = min(k for k, v in tape.items() if v) if any(tape.values()) else pos
        cells = "".join(str(tape.get(x, 0)) for x in range(lo, pos))
        want = "1" * p + "0" + "1" * a + "0" + "11"
        ok = st == 1 and cells == want and all(v == 0 for k, v in tape.items() if k >= pos)
        print(i, p, a, target, "ok" if ok else "MISMATCH")
        if not ok:
            return 1
    return 0


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "orbit":
        for row in orbit(int(sys.argv[2])):
            print(*row)
    elif cmd == "run":
        print(run(int(sys.argv[2])))
    elif cmd == "check":
        sys.exit(check(int(float(sys.argv[2]))))
