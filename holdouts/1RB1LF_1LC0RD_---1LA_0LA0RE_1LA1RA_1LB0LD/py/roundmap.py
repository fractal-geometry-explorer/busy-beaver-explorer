"""The round map of 1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD, by simulation of one round per tail, and its orbit.

A round starts at  D> 0 0 111 0 1^n T  (head at the left end, blank on both sides; T a word that starts with 0 and
ends with 1, the "tail").  Write n = c + 1 + 3t with c in {0, 1, 2}.  The sweeps take the ones three at a time
(t sweeps), then the end of the round works on the last 1..3 ones and on the tail, and the next round starts at
D> 0 0 111 0 1^(4t + d) T'  where (d, T') depends only on (c, T) (checked here for two values of t each time).
The rounds for the tails empty, 011 and 010111 are proved in lean/Round.lean.

usage:
  python3 roundmap.py orbit ROUNDS        iterate the map from the blank-tape round start (n = 3, T empty)
  python3 roundmap.py graph TAILS         breadth-first search of the tails reachable for any c; reports halts
  python3 roundmap.py check ROUNDS        compare the map with the plain simulation of the machine
"""
import sys

M = "1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD"


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
HEAD = [0, 0, 1, 1, 1, 0]


def run_round(n, tail, maxsteps=10 ** 8):
    """Run from D> 0 0 111 0 1^n tail; return ('halt', steps) or (n', tail', steps)."""
    cells = HEAD + [1] * n + list(tail)
    tape = dict(enumerate(cells))
    p, s, lo, hi, steps = 0, 3, 0, len(cells) - 1, 0
    while steps < maxsteps:
        tr = TAB[s][tape.get(p, 0)]
        if tr is None:
            return ("halt", steps + 1)
        w, d, s = tr
        tape[p] = w
        p += d
        steps += 1
        lo, hi = min(lo, p), max(hi, p)
        if s == 3 and p == lo:
            c = [tape.get(i, 0) for i in range(lo, hi + 1)]
            while c and c[-1] == 0:
                c.pop()
            if c[:6] == HEAD:
                j = 6
                while j < len(c) and c[j] == 1:
                    j += 1
                if j - 6 >= 6:
                    return (j - 6, tuple(c[j:]), steps)
    raise RuntimeError("no round end")


MEMO = {}


def trans(tail, c):
    """(d, tail') with n' = 4t + d, or ('halt',) — for n = c + 1 + 3t, t large enough."""
    key = (tail, c)
    if key not in MEMO:
        outs = []
        for t in (len(tail) + 8, len(tail) + 13):
            r = run_round(c + 1 + 3 * t, tail)
            outs.append(("halt",) if r[0] == "halt" else (r[0] - 4 * t, r[1]))
        assert outs[0] == outs[1], (tail, c, outs)
        MEMO[key] = outs[0]
    return MEMO[key]


def blocks(tail):
    s = "".join(map(str, tail))
    return [len(x) for x in s[1:].split("0")] if s else []


def digits(n):
    return int(n.bit_length() * 0.30103) + 1


def orbit(rounds):
    n, tail = 3, ()
    seen, maxlen = {}, 0
    for i in range(1, rounds + 1):
        t, c = divmod(n - 1, 3)
        r = trans(tail, c)
        if r[0] == "halt":
            print("HALT in round", i)
            return
        n, tail = 4 * t + r[0], r[1]
        seen[tail] = seen.get(tail, 0) + 1
        if len(tail) > maxlen:
            maxlen = len(tail)
            print(f"round {i}: n has {digits(n)} digits, new longest tail {blocks(tail)}", flush=True)
        if i % 100000 == 0:
            print(f"round {i}: n has {digits(n)} digits, {len(seen)} tails so far", flush=True)
    print(f"{rounds} rounds, no halt; n has {digits(n)} digits; {len(seen)} distinct tails:")
    for tl, k in sorted(seen.items(), key=lambda x: -x[1]):
        print(f"  {k:9d}  {blocks(tl)}")


def graph(limit):
    start = ()
    dist = {start: 0}
    queue = [start]
    halts = []
    while queue and len(dist) < limit:
        tl = queue.pop(0)
        for c in range(3):
            r = trans(tl, c)
            if r[0] == "halt":
                halts.append((blocks(tl), c, dist[tl] + 1))
                continue
            if r[1] not in dist:
                dist[r[1]] = dist[tl] + 1
                queue.append(r[1])
    print(f"{len(dist)} tails; halting (tail blocks, c, rounds from the empty tail):")
    for h in halts[:20]:
        print("  ", h)


def check(rounds):
    """The orbit of the map against the machine itself."""
    sys.path.insert(0, __file__.rsplit("/", 1)[0])
    n, tail = 3, ()
    tape = {}
    p, s, steps = 0, 0, 0
    lo = hi = 0
    want = []
    for i in range(rounds):
        t, c = divmod(n - 1, 3)
        r = trans(tail, c)
        n, tail = 4 * t + r[0], r[1]
        want.append((n, tail))
    got = []
    while len(got) < rounds:
        tr = TAB[s][tape.get(p, 0)]
        w, d, s = tr
        tape[p] = w
        p += d
        steps += 1
        if p < lo:
            lo = p
        hi = max(hi, p)
        if s == 3 and p == lo and tape.get(p + 1, 0) == 0 and tape.get(p + 2, 0) == 1:
            cc = [tape.get(i, 0) for i in range(lo, hi + 1)]
            while cc and cc[-1] == 0:
                cc.pop()
            if cc[:6] == HEAD:
                j = 6
                while j < len(cc) and cc[j] == 1:
                    j += 1
                if (j - 6, tuple(cc[j:])) != (3, ()):
                    got.append((j - 6, tuple(cc[j:])))
    print("map and machine agree for", rounds, "rounds:", got == want[:len(got)], "last step", steps)


if __name__ == "__main__":
    cmd, arg = sys.argv[1], int(sys.argv[2])
    {"orbit": orbit, "graph": graph, "check": check}[cmd](arg)
