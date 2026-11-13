"""The token model of 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD and of its twin 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA.

At the times the head is in state D (twin: A) on the first cell of a pair `00`, read the tape in pairs:
  left of the head   11 = 1, 00 = 0, 0101 = X (a mark);   right of the head's 00   11 = 1, 10 = 0, then blank.
A frame is  L | R  (two words).  The machine then follows five rewriting rules (k, j >= 0; every rule is proved for
all parameters and all contexts in lean/Rules.lean, and the map below is lean/Tokens.lean `next`):

  R1  L 0 1^k           | 0 r       ->  L | 1^(k+2) r                    4k + 10 steps
  R4  L 0 X (1 X)^j 1^k | 0 r       ->  L | 0 0 (1 0 0)^j 1^(k+2) r      8j + 4k + 14
  R2  L                 | 1^d 0 0 r ->  L 1 0^(d-1) X | r     (d >= 1)   8 (d = 1), 10d - 2 (d >= 2)
  R3  L                 | 1^d 0 1 r ->  L 1 0^(d-2) | 0 0 0 r (d >= 2)   24 (d = 2), 10d + 4 (d >= 3)
  R5  L 0 X (1 X)^j     | 1 0 1 r   ->  L | 0 0 (1 0 0)^j 1 0 0 0 r      8j + 22
  R5a L 0               | 1 0 1 r   ->  L | 1 0 0 0 r                    18
(a 0 at the bottom of L may be blank tape).  No rule applies when the right word is a block of 1s at the right end
of the tape (`1^d 0` or `1^d` and nothing more): there the machine rewrites the tape in one long pass (a "reset");
this script then runs the machine itself until the next frame.

usage (from the repository root):
  python3 holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/tokens.py run EVENTS [twin]
      run the model for EVENTS frames from blank tape; print the resets, the rule counts and the machine steps
  python3 .../tokens.py check EVENTS [twin]
      the same, and compare every rule application (next frame and step count) with the machine
  python3 .../tokens.py probe
      what the machine does from frames no rule covers (right word used up), for a few left words
"""
import collections
import sys

MACHINES = {False: ("1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD", "D"),
            True: ("1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA", "A")}


def table(m):
    T = {}
    for i, p in enumerate(m.split("_")):
        for b in (0, 1):
            t = p[3 * b:3 * b + 3]
            T[(chr(65 + i), b)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, t[2])
    return T


def to_tape(L, R):
    cells = []
    for t in L:
        cells += {"0": [0, 0], "1": [1, 1], "X": [0, 1, 0, 1]}[t]
    pos = len(cells)
    cells += [0, 0]
    for t in R:
        cells += {"1": [1, 1], "0": [1, 0]}[t]
    return cells, pos


def parse_frame(tape, pos, mn, mx):
    """The frame of a tape with the head at `pos` on `00`, or None."""
    R, i = [], pos + 2
    while i <= mx:
        a, b = tape.get(i, 0), tape.get(i + 1, 0)
        if (a, b) == (1, 1):
            R.append("1")
        elif (a, b) == (1, 0):
            R.append("0")
        else:
            break
        i += 2
    if any(tape.get(j, 0) for j in range(i, mx + 1)):
        return None
    L, i = [], pos - 1
    while i >= mn:
        a, b = tape.get(i - 1, 0), tape.get(i, 0)
        if (a, b) == (1, 1):
            L.append("1")
            i -= 2
        elif (a, b) == (0, 0):
            L.append("0")
            i -= 2
        elif (a, b) == (0, 1) and (tape.get(i - 3, 0), tape.get(i - 2, 0)) == (0, 1):
            L.append("X")
            i -= 4
        else:
            return None
    L.reverse()
    while L and L[0] == "0":
        L.pop(0)
    return L, R


def raw_next(T, S, L, R, maxsteps=10 ** 7):
    """Run the machine from the frame L | R to the next frame: (L', R', steps), or ('HALT', steps)."""
    cells, pos = to_tape(L, R)
    tape = {i: c for i, c in enumerate(cells) if c}
    mn, mx, st = 0, len(cells) - 1, S
    for k in range(maxsteps):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return ("HALT", k + 1)
        if t[0]:
            tape[pos] = 1
        else:
            tape.pop(pos, None)
        pos += t[1]
        st = t[2]
        mn, mx = min(mn, pos), max(mx, pos)
        if st == S and tape.get(pos, 0) == 0 and tape.get(pos + 1, 0) == 0:
            f = parse_frame(tape, pos, mn, mx)
            if f:
                return f[0], f[1], k + 1
    raise RuntimeError("no frame reached")


def chain(L):
    """L = rest 0 X (1 X)^j  ->  (rest, j), or None."""
    j, i = 0, len(L)
    while i >= 2 and L[i - 1] == "X" and L[i - 2] == "1":
        j, i = j + 1, i - 2
    if i >= 1 and L[i - 1] == "X" and (i == 1 or L[i - 2] == "0"):
        return L[:max(i - 2, 0)], j
    return None


def step(L, R):
    """One rule: (name, L', R', machine steps), or None when no rule applies."""
    n, d = len(R), 0
    while d < n and R[d] == "1":
        d += 1
    if d == 0:
        if n == 0:
            return None
        k = 0
        while k < len(L) and L[-1 - k] == "1":
            k += 1
        rest = L[:len(L) - k]
        if not rest or rest[-1] == "0":
            return "R1", rest[:-1], ["1"] * (k + 2) + R[1:], 4 * k + 10
        c = chain(rest)
        if c:
            return "R4", c[0], ["0", "0"] + ["1", "0", "0"] * c[1] + ["1"] * (k + 2) + R[1:], 8 * c[1] + 4 * k + 14
        return None
    if d + 1 >= n:
        return None
    if R[d + 1] == "0":
        return "R2", L + ["1"] + ["0"] * (d - 1) + ["X"], R[d + 2:], 8 if d == 1 else 10 * d - 2
    if d >= 2:
        return "R3", L + ["1"] + ["0"] * (d - 2), ["0", "0", "0"] + R[d + 2:], 24 if d == 2 else 10 * d + 4
    if not L or L[-1] == "0":
        return "R5a", L[:-1], ["1", "0", "0", "0"] + R[3:], 18
    c = chain(L)
    if c:
        return "R5", c[0], ["0", "0"] + ["1", "0", "0"] * c[1] + ["1", "0", "0", "0"] + R[3:], 8 * c[1] + 22
    return None


def show(L, R):
    return ("".join(L) or "e") + " | " + ("".join(R) or "e")


def run(events, twin, check):
    m, S = MACHINES[twin]
    T = table(m)
    L, R, steps = ([], [], 0) if twin else ([], ["0", "0"], 5)   # the first frame: twin at step 0, else at step 5
    stats = collections.Counter()
    for it in range(events):
        nx = step(L, R)
        if nx is None or check:
            rn = raw_next(T, S, L, R)
            if rn[0] == "HALT":
                print("the machine halts from", show(L, R))
                return
            if nx is None:
                print(f"reset at frame {it}, step {steps}: {show(L, R)}  ->  {show(rn[0], rn[1])}  ({rn[2]} steps)")
                nx = ("reset", rn[0], rn[1], rn[2])
            else:
                got = ("".join(nx[1]).lstrip("0"), nx[2], nx[3])
                assert got == ("".join(rn[0]), rn[1], rn[2]), (show(L, R), nx, rn)
        stats[nx[0]] += 1
        L, R, steps = nx[1], nx[2], steps + nx[3]
        while L and L[0] == "0":
            L.pop(0)
    print(f"{events} frames, {steps} machine steps; rules used: {dict(stats)}")
    print("last frame:", show(L, R))
    if check:
        print("every rule application agreed with the machine")


def probe():
    m, S = MACHINES[False]
    T = table(m)
    for R in ["1", "11", "111", "1111", "10", "110", "1110", "11110", "111110", "1111110", "11111110"]:
        print("right word", R, "then blank:")
        for L in ["", "1", "10", "101", "110", "10X", "0X1", "1X0", "10X10X"]:
            rn = raw_next(T, S, list(L), list(R))
            print(f"   {L or 'e':8} ->  " + ("HALT" if rn[0] == "HALT" else show(rn[0], rn[1])) + f"   ({rn[-1]} steps)")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["probe"]:
        probe()
    elif len(a) >= 2 and a[0] in ("run", "check"):
        run(int(a[1]), "twin" in a[2:], a[0] == "check")
    else:
        sys.exit(__doc__)
