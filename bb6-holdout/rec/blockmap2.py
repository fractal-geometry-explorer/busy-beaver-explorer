"""Block-to-block step from the state  G1, B r, W R  (width w), built directly with every residue class of
(r, R, w) mod 2^K allowed on a real tape (r even, R odd, w even) and huge random values (r ≈ 0.4w, R ≈ w - D).
Runs to the next round start that holds a block, records the path, and fits exact affine formulas per path."""
import sys, random, collections, itertools
from fractions import Fraction as F
import tracecycle as T
T.HOOK = None
def v2(x):
    c = 0
    while x and x % 2 == 0: x //= 2; c += 1
    return c
def shape(ms): return " ".join(m[0] for m in ms)
def step_to_next_block(r, R, w, max_rounds=80):
    marks = [["G", 1], ["B", r], ["W", R]]; path = []
    for _ in range(max_rounds):
        w, marks, ev = T.round_events(w, marks)
        ms = sorted(([a, b] for a, b in marks), key=lambda m: m[1])
        if len(ms) == 2 and ms[1] == ["M", w - 2]: return path, "cycle ends (clean tape)", None, w
        s = shape(ms)
        if "B" in s: return path, s, ms, w
        path.append(s)
    return path, "too long", None, w
K = int(sys.argv[1]); M = 1 << K; random.seed(3)
groups = collections.defaultdict(list)
for r0 in range(0, M, 2):
    for R0 in range(1, M, 2):
        for w0 in range(0, M, 2):
            for lift in range(3):
                W = (random.getrandbits(46) | (1 << 46)) * M + w0
                r = (W * 2 // 5) // M * M + r0
                D = (random.getrandbits(36) | (1 << 36)) * M
                R = (W - D) // M * M + R0
                path, nxt, ms, w1 = step_to_next_block(r, R, W)
                key = (tuple(path), nxt, v2(r) if v2(r) < 6 else 6)
                groups[key].append((r, R, W, ms, w1))
def solve(rows):
    """Fit y = a r + b R + c w + d exactly; rows = [(r, R, w, y)]."""
    for combo in itertools.combinations(range(len(rows)), 4):
        Mx = [[F(rows[i][0]), F(rows[i][1]), F(rows[i][2]), F(1), F(rows[i][3])] for i in combo]
        ok = True
        for c in range(4):
            p = next((i for i in range(c, 4) if Mx[i][c] != 0), None)
            if p is None: ok = False; break
            Mx[c], Mx[p] = Mx[p], Mx[c]; Mx[c] = [x / Mx[c][c] for x in Mx[c]]
            for i in range(4):
                if i != c and Mx[i][c] != 0: Mx[i] = [a - Mx[i][c] * b for a, b in zip(Mx[i], Mx[c])]
        if not ok: continue
        co = [Mx[i][4] for i in range(4)]
        return co if all(co[0] * x[0] + co[1] * x[1] + co[2] * x[2] + co[3] == x[3] for x in rows) else None
    return None
def fmt(co):
    parts = []
    for c, nm in zip(co, ["r", "R", "w", ""]):
        if c: parts.append(f"{c}{'·' + nm if nm else ''}")
    return " + ".join(parts) if parts else "0"
tot = sum(len(v) for v in groups.values())
print(f"K = {K}: {tot} runs from block states")
for (path, nxt, z), rows in sorted(groups.items(), key=lambda kv: -len(kv[1]))[:12]:
    share = 100 * len(rows) / tot
    desc = (" → ".join(path) + " → " if path else "") + nxt
    line = f"{share:5.1f}%  r with {z}{'+' if z == 6 else ''} trailing zeros:  {desc}"
    if rows[0][3] is not None:
        sh = [m[0] for m in rows[0][3]]
        if all([m[0] for m in rw[3]] == sh for rw in rows):
            fits = []
            for i, t in enumerate(sh):
                if i == 0: continue
                co = solve([(rw[0], rw[1], rw[2], rw[3][i][1]) for rw in rows])
                fits.append(f"{t}' = {fmt(co) if co else '?'}")
            cw = solve([(rw[0], rw[1], rw[2], rw[4]) for rw in rows])
            fits.append(f"w' = {fmt(cw) if cw else '?'}")
            line += "\n           " + ";  ".join(fits)
    print(line)
