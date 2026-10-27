"""Start from the round-start state G1, M x, B r (a marker at the left, a block waiting at the right end), width w.
For every residue class of (x, r, w) mod 2^K with the parities a real tape forces, run two huge random lifts in the
mark model and measure the cascade length. Classes whose outcome differs between lifts depend on higher bits."""
import sys, random, collections
import tracecycle as T
def pred(d): return (d - 2) // 2 if d % 4 == 2 else d // 2 + 4
def run(x, r, w, max_rounds=600):
    marks = [["G", 1], ["M", x], ["B", r]]; meets = []
    def hook(ms, label, xx):
        if label != "gap": return
        s = sorted(ms, key=lambda m: m[1]); rr = [m for m in s if m[1] > xx]
        if rr and rr[0][0] == "M" and rr[0] is s[-1]: meets.append(rr[0][1] - xx - 3)
    T.HOOK = hook
    for _ in range(max_rounds):
        w, marks, ev = T.round_events(w, marks)
        if len(marks) == 2 and marks[1] == ["M", w - 2]: break
        if len(meets) >= 2 and meets[-1] != pred(meets[-2]): break
    L = 1 if meets else 0
    for a, b in zip(meets, meets[1:]):
        if b == pred(a): L += 1
        else: break
    return L
K = int(sys.argv[1]); M = 1 << K; random.seed(7)
lens = collections.Counter(); und = 0; total = 0
for x0 in range(0, M, 2):
    for r0 in range(1, M, 2):
        for w0 in range(0, M, 2):
            out = []
            for lift in range(2):
                X = random.getrandbits(40) | (1 << 40); R = random.getrandbits(40) | (1 << 42); Wd = random.getrandbits(40) | (1 << 44)
                x = x0 + M * X; r = r0 + M * R; w = w0 + M * Wd
                out.append(run(x, r, w))
            total += 1
            if out[0] != out[1]: und += 1
            else: lens[out[0]] += 1
print(f"K = {K}: {total} classes; cascade lengths in classes fixed by the low bits: {dict(sorted(lens.items()))}; depend on higher bits: {und} ({und/total:.2%})")
