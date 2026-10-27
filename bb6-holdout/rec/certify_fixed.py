"""For every fixed class v <= 260: (1) certified run (proven rules only, exact tape checks) of two concrete n with
v2(n+2) = v and n = 2 mod 3, compared with the symbolic jump; (2) smallest constant spacing between two marks that
share the same m-coefficient during the symbolic run (marks with different coefficients are about m apart)."""
import json, random, time
import symjump as S, cycles
res = {int(k): v for k, v in json.load(open("fixed_260.json")).items()}
random.seed(1)
def rep(v):
    while True:
        m = random.getrandbits(48) | (1 << 47) | 1
        n = (m << v) - 2
        if n % 3 == 2: return n
def min_spacing(v):
    w0 = S.P(2 ** (v + 1), 2) if v else S.P(2, 2)
    w = w0; marks = [["G", S.P(0, 1)], ["M", w0 - 2]]; best = 10 ** 9
    for r in range(1, 2000):
        w, marks = S.round_events(w, marks)
        ms = sorted(marks, key=lambda k: k[1].key())
        for (t1, p1), (t2, p2) in zip(ms, ms[1:]):
            if p1.a == p2.a: best = min(best, int(p2.b - p1.b))
        if len(marks) == 2 and marks[1][0] == "M" and marks[1][1] == w - 2: return best
t0 = time.time(); bad = 0; spac = {}
for v in sorted(res):
    J = res[v][0]
    for _ in range(2):
        n = rep(v); out = cycles.cycle(n)
        if out[0] != "clean" or out[1] - n != J: bad += 1; print("MISMATCH", v, n, out[:3])
    spac[v] = min_spacing(v)
print(f"certified 2 x {len(res)} representatives, mismatches: {bad}, {time.time()-t0:.0f}s")
print("smallest same-coefficient spacing over all classes:", min(spac.values()),
      " classes reaching it:", [v for v in spac if spac[v] == min(spac.values())][:12])
