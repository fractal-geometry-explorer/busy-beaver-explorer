"""Clock test, general form: visits of an end of the tape in state X, the tape read from the head outward is
`hv PRE U^n W`.  Within a phase (n grows by one per visit), is W at the visit with n0+k+1 units equal to W at the
visit before after 2^k applications of the base map (the run from the visit with n0 units to the next visit)?

usage: python3 clocktest2.py MACHINE SIDE(L|R) X STEPS START_STEP HV PRE U [MAXV]   (TMRUN: path of tools/c/tmrun.c built, default ./tmrun)
e.g.   python3 clocktest2.py 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF R C 3000000000 877024813 0 01 1111 14
  PRE may be '-' for empty.  SIDE R: the machine is mirrored and its left end used."""
import os, re, subprocess, sys

def mirror(m):
    return "_".join("".join({"L": "R", "R": "L"}.get(ch, ch) for ch in g) for g in m.split("_"))

def table(m):
    T = {}
    for s, g in enumerate(m.split("_")):
        for y in (0, 1):
            x = g[3 * y:3 * y + 3]
            T[(s, y)] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2]))
    return T

def cells_of(s):
    c = []
    for x in re.sub(r"[A-F]>", "", s).split():
        v, _, n = x.partition('^'); c += [int(v)] * int(n or 1)
    return c

def parse(c, hv, PRE, U):
    if c[0] != hv or c[1:1 + len(PRE)] != PRE: return None
    i = 1 + len(PRE); n = 0
    while c[i:i + len(U)] == U: i += len(U); n += 1
    if n == 0: return None
    W = c[i:]
    while W and W[-1] == 0: W.pop()
    return n, W

def tick1(T, st, hv, PRE, U, n0, W, maxt=10 ** 9):
    pad = 64
    tp = bytearray(pad) + bytearray([hv] + PRE + U * n0 + W) + bytearray(64)
    pos = lo = pad; s = st; t = 0
    while t < maxt:
        tr = T[(s, tp[pos])]
        if tr is None: return None
        w, d, q = tr; tp[pos] = w; pos += d; s = q; t += 1
        if pos >= len(tp) - 5: tp += bytearray(len(tp))
        if pos < lo:
            lo = pos
            if lo < 2: tp = bytearray(pad) + tp; pos += pad; lo += pad
        if s == st and pos == lo and tp[pos] == hv:
            r = parse(list(tp[lo:]), hv, PRE, U)
            if r: return (r[0], r[1], t)
    return None

if __name__ == "__main__":
    M, side, X, N, a, hv, PRE, U = sys.argv[1:9]
    maxv = int(sys.argv[9]) if len(sys.argv) > 9 else 12
    a = int(a); hv = int(hv)
    PRE = [] if PRE == "-" else [int(ch) for ch in PRE]; U = [int(ch) for ch in U]
    m = mirror(M) if side == "R" else M
    T = table(m); S = "ABCDEF".index(X)
    out = subprocess.run([os.environ.get("TMRUN", "./tmrun"), m, N, "at", X, "L", "1000000"], capture_output=True, text=True).stdout.split("\n")
    vis = []
    for l in out:
        if l and l[0].isdigit():
            t, tape = l.split(None, 1)
            if int(t) >= a and tape.startswith(X + ">" + str(hv)):
                r = parse(cells_of(tape), hv, PRE, U)
                if r: vis.append((int(t), r[0], r[1]))
    t0, n0, W0 = vis[0]; print("start", t0, "units", n0, "visits parsed", len(vis))
    cur = W0; n = n0
    for (t2, n2, W2) in vis[1:maxv]:
        print("visit", t2, "units", n2, end=": ", flush=True)
        if n2 != n + 1: print("not +1"); break
        k = 0
        while k < 100000:
            r = tick1(T, S, hv, PRE, U, n0, cur)
            if r is None: print("halt/timeout"); cur = None; break
            if r[0] != n0 + 1: print("base map gave", r[0], "after", k); cur = None; break
            cur = r[1]; k += 1
            if cur == W2: print("matched after", k, "base maps"); break
        if cur != W2: print("no match"); break
        n = n2
