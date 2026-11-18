"""The round map `next` of lean/Round.lean, checked against the machine and iterated far.

  python3 py/orbit.py check ROUNDS     simulate the machine from blank tape (plain Python, slow) and compare the
                                        configuration at the start of each of the first ROUNDS rounds with the map
  python3 py/orbit.py rules            the rule table with step counts (round_steps) against direct simulation: a grid
                                        of rounds, and every round of the first 10^7 steps from blank tape
  python3 py/orbit.py iterate ROUNDS   iterate the map (Python big integers) and report the closest approaches to
                                        the halting states i = j and i + 1 = j

State (i, j, J): the tape at the start of a round is 1^(2i) 0 1^(2j) 0 11 B> (J = 0) or 1^(2i) 0 1^(2j) 0 11 0 11 B>
(J = 1).  The orbit starts at (3, 1, 0) (step 74).
"""
import math
import sys


def nxt(i, j, J):
    if i == j or i + 1 == j:
        return None
    if j + 2 <= i:
        return (i - j - 1, 3 * j + (3 if J else 2), J)
    if i == j + 1:
        return (3 * i, 1, 0) if J else (3 * i - 3, 3, 1)
    if i + 2 == j:
        return (3 * i + 3, 3, 1) if J else (3 * i + 3, 1, 0)
    return (j - i - 2, 3 * i + (5 if J else 3), 1 - J)


M = "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"


def machine_rounds(rounds):
    """The (i, j, J) of the machine each time the head extends the tape to the right in state B with the tape in
    round form."""
    T = {}
    for k, s in enumerate(M.split("_")):
        for r in (0, 1):
            t = s[3 * r:3 * r + 3]
            T[(k, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    tape = bytearray(1 << 20)
    pos = lo = hi = 1 << 19
    st, n, out = 0, 0, []
    while len(out) < rounds:
        t = T[(st, tape[pos])]
        if t is None:
            out.append(("halt", n))
            break
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        n += 1
        if pos > hi:
            hi = pos
            if st == 1:
                s = bytes(tape[lo:pos]).strip(b"\0")
                for J, suf in ((1, b"\0\1\1\0\1\1"), (0, b"\0\1\1")):
                    if s.endswith(suf):
                        parts = s[:-len(suf)].split(b"\0")
                        if len(parts) == 2 and all(p and p.count(1) == len(p) and len(p) % 2 == 0 for p in parts):
                            out.append((len(parts[0]) // 2, len(parts[1]) // 2, J))
                            break
        lo = min(lo, pos)
    return out


def check(rounds):
    got = machine_rounds(rounds)
    s = (3, 1, 0)
    for k, g in enumerate(got):
        if g != s:
            print("MISMATCH at round", k, g, s)
            return
        s = nxt(*s)
    print(f"the first {len(got)} rounds of the machine agree with the map; last {got[-1]}")


def iterate(rounds):
    s = (3, 1, 0)
    best = []
    for k in range(rounds):
        i, j, J = s
        d = i - j
        if k > 10:
            m = max(i, j)
            # |d - (-1/2)| relative to the size: how close to the halting pair {0, -1}
            closeness = math.log2(abs(2 * d + 1)) - math.log2(m) if d not in (0, -1) else -999
            best.append((round(closeness, 2), k, ('-' if d < 0 else '+') + str(abs(d).bit_length()), m.bit_length()))
            best = sorted(best)[:8]
        s2 = nxt(*s)
        if s2 is None:
            print("HALTS in round", k, s)
            return
        s = s2
        if k % 100000 == 0 and k:
            print(f"round {k}: i has {s[0].bit_length()} bits, j {s[1].bit_length()} bits", flush=True)
    print(f"{rounds} rounds, no halt; i has {s[0].bit_length()} bits, j has {s[1].bit_length()} bits")
    print("closest approaches (log2 |2(i-j)+1| - log2 max(i,j), round, sign and bits of i-j, bits of max(i,j)):")
    for b in best:
        print("  ", b)


def round_steps(i, j, J):
    """Machine steps of the round from R1(i, j) (J = 0) or R2(i, j) (J = 1) to the next round start, or to the halt
    (counting the halting step).  These are the sums of the step counts of the pieces of lean/Pieces.lean that
    round_ok in lean/Round.lean puts together."""
    if j + 2 <= i:
        return 12 * i * j + 24 * j + (27 if J else 11)
    if i == j + 1:
        return 12 * j * j + (36 * j + 27 if J else 72 * j + 50)
    if i == j:
        return 12 * j * j - 6 * j + (8 if J else 5)
    if i + 1 == j:
        return 12 * j * j - 18 * j + (17 if J else 14)
    if i + 2 == j:
        return 12 * j * j + (36 * j + 14 if J else -9)
    return 12 * i * j + 12 * i + 12 * j + (35 if J else 15)


def table():
    T = {}
    for k, s in enumerate(M.split("_")):
        for r in (0, 1):
            t = s[3 * r:3 * r + 3]
            T[(k, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def round_form(tape, lo, pos):
    s = bytes(tape[lo:pos]).strip(b"\0")
    for J, suf in ((1, b"\0\1\1\0\1\1"), (0, b"\0\1\1")):
        if s.endswith(suf):
            parts = s[:-len(suf)].split(b"\0")
            if len(parts) == 2 and all(p and p.count(1) == len(p) and len(p) % 2 == 0 for p in parts):
                return (len(parts[0]) // 2, len(parts[1]) // 2, J)
    return None


def sim_round(i, j, J, limit=10 ** 7):
    """Direct simulation from R1(i, j) / R2(i, j) to the next round start or the halt: (target or 'halt', steps)."""
    T = table()
    w = bytes([1] * (2 * i) + [0] + [1] * (2 * j) + [0, 1, 1] + ([0, 1, 1] if J else []))
    N = 8 * (len(w) + 200)
    tape = bytearray(N)
    lo = N // 2
    tape[lo:lo + len(w)] = w
    pos = hi = lo + len(w)
    st = 1
    for n in range(limit):
        t = T[(st, tape[pos])]
        if t is None:
            return "halt", n + 1
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = round_form(tape, lo, pos)
                if r:
                    return r, n + 1
    return "?", limit


def check_rules():
    bad = n = halts = 0
    for J in (0, 1):
        for i in range(1, 41):
            for j in range(2 if J else 1, 41):
                r, k = sim_round(i, j, J)
                want = nxt(i, j, J)
                n += 1; halts += r == "halt"
                if (r == "halt") != (want is None) or (want is not None and r != want) or k != round_steps(i, j, J):
                    bad += 1; print("differs at", (i, j, J), r, k, want, round_steps(i, j, J))
    print(f"rules grid: {n} rounds ({halts} halting), {bad} failures")
    T = table()
    N = 10 ** 7
    tape = bytearray(1 << 16)
    pos = lo = hi = 1 << 15
    st, s, acc, nr = 0, (3, 1, 0), 74, 0
    for k in range(N):
        t = T[(st, tape[pos])]
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = round_form(tape, lo, pos)
                if r is None:
                    continue
                if nr:
                    acc += round_steps(*s); s = nxt(*s)
                nr += 1
                if r != s or acc != k + 1:
                    bad += 1; print("run differs at step", k + 1, r, s, acc); s, acc = r, k + 1
    print(f"rules run: {nr} round starts in the first {N:.0e} steps, the last at step {acc}, "
          f"{'all at the predicted step' if not bad else 'FAILED'}")
    return bad


if __name__ == "__main__":
    if sys.argv[1] == "rules":
        sys.exit(1 if check_rules() else 0)
    {"check": check, "iterate": iterate}[sys.argv[1]](int(sys.argv[2]))
