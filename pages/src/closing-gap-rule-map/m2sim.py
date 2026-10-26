"""Simulator and step classifier for 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE."""
MACHINE = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
SN = "ABCDEF"
TR = {}
for s, g in enumerate(MACHINE.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        TR[(SN[s], y)] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, x[2], x)

class TM:
    def __init__(self):
        self.t = {}; self.pos = 0; self.st = "A"; self.steps = 0; self.lo = 0; self.hi = 0; self.halted = False
    def read(self, p=None):
        return self.t.get(self.pos if p is None else p, 0)
    def key(self):
        return f"{self.st}{self.read()}"
    def rule(self):
        r = TR[(self.st, self.read())]
        return "---" if r is None else r[3]
    def step(self):
        r = TR[(self.st, self.read())]
        if r is None:
            self.halted = True; return False
        w, d, n, _ = r
        self.t[self.pos] = w; self.pos += d; self.st = n; self.steps += 1
        self.lo = min(self.lo, self.pos); self.hi = max(self.hi, self.pos)
        return True
    def run_to(self, n):
        while self.steps < n and self.step(): pass
        return self
    def cells(self, a, b):
        return "".join(str(self.t.get(i, 0)) for i in range(a, b + 1))
    def content(self):
        ones = [i for i, v in self.t.items() if v]
        return (min(ones), max(ones)) if ones else (0, 0)

def trace(a, b):
    """Run from blank to step a, then record (step, pos, key, rule) for steps a..b-1 and pos at b."""
    m = TM().run_to(a)
    rec = []
    while m.steps < b:
        rec.append((m.steps, m.pos, m.key(), m.rule()))
        if not m.step(): break
    return m, rec

CYC = {"L": ["A1", "E1", "B0", "C0"], "S": ["A0", "B1"], "R": ["E0", "F1"]}
def tokens(keys):
    """Greedy split of a key list into cycle runs and event words: list of (kind, start_index, length)."""
    lab = ["x"] * len(keys)
    for name in ("L", "S", "R"):
        p = CYC[name]; i = 0
        while i + len(p) <= len(keys):
            if all(lab[i + j] == "x" and keys[i + j] == p[j] for j in range(len(p))):
                for j in range(len(p)): lab[i + j] = name
                i += len(p)
            else:
                i += 1
    out = []; i = 0
    while i < len(keys):
        j = i
        while j + 1 < len(keys) and lab[j + 1] == lab[i]: j += 1
        out.append((lab[i], i, j - i + 1))
        i = j + 1
    return out

def classify(keys):
    """Per-step kind: crawl (carry left), run (pass right), recode (shift right), fill (gap step),
    append (turn at a marker or wall), fixed (other fixed sequence), halt."""
    toks = tokens(keys)
    kind = [None] * len(keys)
    words = [" ".join(keys[s:s + n]) if k == "x" else k for k, s, n in toks]
    for ti, (k, s, n) in enumerate(toks):
        w = words[ti]
        nxt = words[ti + 1] if ti + 1 < len(toks) else ""
        prv = words[ti - 1] if ti > 0 else ""
        if k == "L": kk = "crawl"
        elif k == "R": kk = "run"
        elif k == "S":
            if n == 2 and (nxt == "A1" or nxt.startswith("A1 E0 F0 D0")) and prv in ("L", "") or (n == 2 and prv.endswith("C0") and nxt.startswith("A1")):
                kk = "fill"
            elif n == 2 and prv == "E1 B1 A0 B0 C1 D0":
                kk = "append"
            elif n == 2 and prv == "A1 E1 B0 C1 D0" and nxt == "L":
                kk = "fixed"   # merge
            else:
                kk = "recode"
        else:
            if w == "A1" and prv == "S": kk = "fill"
            elif w.startswith("A1 E0 F0 D0") and prv == "S": kk = None  # split below
            elif w == "E1 B1 A0 B0 C1 D0": kk = "append"
            elif w == "E0 F0 D0": kk = "append"
            elif w.endswith("D1"): kk = "halt"
            else: kk = "fixed"
        for q in range(s, s + n): kind[q] = kk
        if kk is None:
            kind[s] = "fill"
            for q in range(s + 1, s + n): kind[q] = "fixed"
    return kind, toks, words
