"""The round map `next` of lean/Round.lean, checked against the machine and iterated far.

  python3 py/orbit.py check ROUNDS     simulate the machine from blank tape (plain Python, slow) and compare the
                                        configuration at the start of each of the first ROUNDS rounds with the map
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


if __name__ == "__main__":
    {"check": check, "iterate": iterate}[sys.argv[1]](int(sys.argv[2]))
