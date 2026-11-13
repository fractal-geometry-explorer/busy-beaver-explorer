"""The round map of 1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD as lean/Reduction.lean defines it (`roundMap`).

After the sweeps of a round the tape is  A> 0 11 0 11 0 111 (0111)^t 0 1^c T.  Keep one copy of 0111 on each side;
the t - 2 copies between are "the block".  The head works cell by cell in the left zone or the right zone and
crosses the block whole by one of six shift rules, so the computation never looks at t:

    roundMap(n, T) = (4 (t - 2) + N, T')    with (N, T') = tail_map(T, c),  n = c + 3t,  c in {1, 2, 3},

or 'halt', or 'stuck' (the head met the block in a way no rule covers, or the fuel ran out; never seen).
lean/Zone.lean proves that whatever this simulator answers is what the machine does (for every t).

usage:
  python3 zonemap.py check TAILS     compare with roundmap.py (plain simulation) on the first TAILS tails of its graph
  python3 zonemap.py orbit ROUNDS    iterate from (11, empty tail), the second round start of the run from blank tape
"""
import sys

M = "1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD"
A, B, C, D, E, F = range(6)


def parse(text):
    tab = []
    for g in text.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s[2] not in "ABCDEF" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        tab.append(row)
    return tab


TAB = parse(M)
# (state, u, w, v): rightwards  L u q> w^k R -> L v^k u q> R  (u, v nearest the head first);
#                   leftwards   L w^k q> u R -> L q> u v^k R  (w nearest the head first)
RULES_R = [(A, [], [0, 1, 1, 1], [1, 0, 0, 1]), (D, [], [1, 1, 0, 1], [0, 1, 1, 0])]
RULES_L = [(A, [1], [1, 0, 0, 1], [1, 1, 0, 1]), (F, [0], [0, 1, 1, 0], [1, 1, 1, 1]),
           (C, [1], [1, 0, 0, 1], [1, 1, 1, 1]), (D, [0], [0, 1, 1, 0], [0, 1, 1, 1])]
HEAD = [0, 0, 1, 1, 1, 0]


def find(rules, q, m, ctx):
    for r in rules:
        if r[0] == q and r[2] == m and ctx[:len(r[1])] == r[1]:
            return r
    return None


def decode(z, a, b, m, o, q):
    if not (z == "L" and q == D and not a and m == [1, 1, 1, 1] and b[:6] == HEAD and all(b[6:])):
        return None
    j = 0
    while j < len(o) and o[j] == 1:
        j += 1
    t = o[j:]
    while t and t[-1] == 0:
        t = t[:-1]
    return (len(b) - 6 + j, tuple(t))


def tail_map(tail, c):
    """(N, T'), ('halt',) or ('stuck',) for the tail and c = 1, 2, 3 ones left."""
    z, a, b, m, q = "L", [], [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 1, 1], A
    o = [0, 1, 1, 1, 0] + [1] * c + list(tail)
    for _ in range(100 * (len(tail) + 10) ** 2):
        if z == "L":
            if not b:
                r = find(RULES_R, q, m, a)
                if r is None:
                    return ("stuck",)
                z, a, b, m, o = "R", list(r[1]), o, r[3], a[len(r[1]):]
            else:
                tr = TAB[q][b[0]]
                if tr is None:
                    return ("halt",)
                w, d, q = tr
                if d > 0:
                    a, b = [w] + a, b[1:]
                else:
                    a, b = a[1:], [a[0] if a else 0, w] + b[1:]
        else:
            r = find(RULES_L, q, m, b) if not a else None
            if r is not None:
                z, a, b, m, o = "L", o, list(r[1]), r[3], b[len(r[1]):]
            else:
                tr = TAB[q][b[0] if b else 0]
                if tr is None:
                    return ("halt",)
                w, d, q = tr
                if d > 0:
                    a, b = [w] + a, b[1:]
                elif not a:
                    return ("stuck",)
                else:
                    a, b = a[1:], [a[0], w] + b[1:]
        r = decode(z, a, b, m, o, q)
        if r is not None:
            return r
    return ("stuck",)


MEMO = {}


def round_map(n, tail):
    if n < 7:
        return ("stuck",)
    t, c = divmod(n - 1, 3)
    key = (tail, c)
    if key not in MEMO:
        MEMO[key] = tail_map(tail, c + 1)
    r = MEMO[key]
    return r if len(r) == 1 else (4 * (t - 2) + r[0], r[1])


def blocks(tail):
    s = "".join(map(str, tail))
    return [len(x) for x in s[1:].split("0")] if s else []


def orbit(rounds):
    n, tail = 11, ()
    seen = {}
    for i in range(1, rounds + 1):
        r = round_map(n, tail)
        if len(r) == 1:
            print(f"{r[0].upper()} in round {i}: tail {blocks(tail)}, (n - 1) mod 3 = {(n - 1) % 3}")
            return
        n, tail = r
        seen[tail] = seen.get(tail, 0) + 1
        if i <= 12:
            print(f"orbit {i}: n = {n}, tail blocks {blocks(tail)}")
        if i % 100000 == 0:
            print(f"round {i}: n has {int(n.bit_length() * 0.30103) + 1} digits, {len(seen)} tails so far", flush=True)
    print(f"{rounds} rounds: no halt, never stuck; n has {int(n.bit_length() * 0.30103) + 1} digits; "
          f"{len(seen)} distinct tails")
    for tl, k in sorted(seen.items(), key=lambda x: -x[1]):
        print(f"  {k:9d}  {blocks(tl)}")


def check(limit):
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import roundmap
    dist, queue, bad, halts, cases = {(): 0}, [()], 0, 0, 0
    while queue and len(dist) < limit:
        tl = queue.pop(0)
        for c in range(3):
            want = roundmap.trans(tl, c)          # (d, T') with n' = 4t + d
            got = tail_map(tl, c + 1)
            got = got if len(got) == 1 else (got[0] - 8, got[1])
            cases += 1
            if want != got:
                bad += 1
                print("MISMATCH", blocks(tl), c, want, got)
            if want[0] == "halt":
                halts += 1
            elif want[1] not in dist:
                dist[want[1]] = dist[tl] + 1
                queue.append(want[1])
    print(f"{cases} cases (tail, c) from {len(dist)} tails: {bad} mismatches, {halts} halting cases, none stuck"
          if not bad else f"{bad} MISMATCHES")


if __name__ == "__main__":
    {"orbit": orbit, "check": check}[sys.argv[1]](int(sys.argv[2]))
