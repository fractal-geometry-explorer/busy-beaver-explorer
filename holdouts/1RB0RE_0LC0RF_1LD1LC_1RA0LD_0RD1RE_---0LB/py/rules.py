"""Generate lean/Rules.lean and lean/Visits.lean for 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB.

Every rule is found by running the machine on a small concrete instance (`visit`), replacing the long blocks by
variables, and proving the resulting statement along the symbolic run of tools/py/bbtools/symtm.py (single steps by
`rfl`, shift rules by TM.cross_r/cross_l, re-bracketing by TM.rep_rotate).  Lean is the judge: a statement that does
not hold for every value of the variables fails to check.

usage (from the repo root):
  python3 holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/py/rules.py          # writes lean/Rules.lean, lean/Visits.lean
  python3 holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/py/rules.py --list   # prints the rules as a table
"""
import itertools
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
import bbtools.symtm as symtm  # noqa: E402
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB"
NS = next(l.split()[1] for l in open(os.path.join(HERE, "..", "lean", "Machine.lean")) if l.startswith("namespace "))

TABLE = {}
for _s, _part in enumerate(M.split("_")):
    for _r in range(2):
        _t = _part[3 * _r:3 * _r + 3]
        TABLE[(_s, _r)] = None if _t[2] == "-" else (int(_t[0]), 1 if _t[1] == "R" else -1, ord(_t[2]) - 65)

LEFT = [0, 0, 1, 1, 1, 1, 1]          # the left end at a sample:  0^inf D> 0 0 1^5 (00111)^a X 0^inf
WORD = [0, 0, 1, 1, 1]


def visit(a, X, maxsteps=10 ** 8):
    """From `0^inf D> 0 0 1^5 (00111)^a X 0^inf` run to the next configuration of that form (state D on a new leftmost
    cell).  Returns (a', X', steps)."""
    pad = 40
    tape = [0] * pad + LEFT + WORD * a + [int(c) for c in X] + [0] * 60
    p, st, lo, n = pad, 3, pad, 0
    while n < maxsteps:
        tr = TABLE[(st, tape[p])]
        if tr is None:
            return ("HALT", n)
        tape[p] = tr[0]
        p += tr[1]
        st = tr[2]
        n += 1
        if p >= len(tape) - 2:
            tape += [0] * 60
        if p < lo:
            lo = p
            if st == 3 and tape[p:p + 7] == LEFT:
                q, a2 = p + 7, 0
                while tape[q:q + 5] == WORD:
                    q += 5
                    a2 += 1
                return a2, "".join(map(str, tape[q:])).rstrip("0"), n
    raise RuntimeError("no sample")


LONG = 9          # a run of at least this many copies of a word is a block (a variable in the rule)


def blocks(X):
    """Parse a tape string into literals and blocks: list of cells '0'/'1' and (word, n) with n >= LONG."""
    out, i = [], 0
    while i < len(X):
        best = None
        for w in range(1, 7):
            word, k = X[i:i + w], 1
            if len(word) < w:
                break
            while X[i + k * w:i + (k + 1) * w] == word:
                k += 1
            if k >= LONG and (best is None or k * w > best[1] * len(best[0])):
                best = (word, k)
        if best:
            out.append(best)
            i += len(best[0]) * best[1]
        else:
            out.append(X[i])
            i += 1
    return out


def lits(s):
    """Literal cells as symtm tokens, runs of 1 compressed for readability."""
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]:
            j += 1
        if s[i] == "1" and j - i >= 5:
            out.append(f"(1)^{j - i}")
        else:
            out.extend(s[i:j])
        i = j
    return out


def expr(v, k):
    return v if k == 0 else f"{v}+{k}"


def cfg(a_expr, toks, counts):
    """Configuration string; toks from `blocks`, counts: expressions for the blocks in order.  a_expr None: no left block."""
    parts = ["0^inf D> 0 0 (1)^5"] + ([f"(00111)^{a_expr}"] if a_expr is not None else [])
    it = iter(counts)
    lit = ""
    for t in toks:
        if isinstance(t, tuple):
            parts += lits(lit)
            lit = ""
            parts.append(f"({t[0]})^{next(it)}")
        else:
            lit += t
    parts += lits(lit) + ["0^inf"]
    return " ".join(parts)


VARS = "cdefgh"
A0 = 12           # size of the left block in the concrete instance


def visit_rule(name, X, doc=None):
    """The rule of one visit from `(00111)^a X`; blocks of X become variables.  Returns (lean, X', info)."""
    a2, X2, _ = visit(A0, X)
    t1 = blocks(X)
    b1 = [t for t in t1 if isinstance(t, tuple)]
    if a2 == A0 + 1:
        t2 = blocks(X2)
        b2 = [t for t in t2 if isinstance(t, tuple)]
        if len(b1) != len(b2):
            raise ValueError(f"{name}: block structure changes: {t1} -> {t2}")
        kind = "visit"
    else:                               # recycle: the left block is rewritten as the first block of X'
        t2 = blocks(X2)
        b2 = [t for t in t2 if isinstance(t, tuple)]
        if a2 != 0 or len(b2) != len(b1) + 1:
            raise ValueError(f"{name}: unexpected recycle {a2} {t2}")
        kind = "recycle"
    last = None
    for offs in sorted(itertools.product(range(7), repeat=len(b1) + 1), key=lambda o: (sum(o), o)):
        oa, ob = offs[0], offs[1:]
        if kind == "visit":
            if any(o + n2[1] - n1[1] < 0 for o, n1, n2 in zip(ob, b1, b2)):
                continue
            s = cfg(expr("a", oa), t1, [expr(v, o) for v, o in zip(VARS, ob)])
            e = cfg(expr("a", oa + 1), t2, [expr(v, o + n2[1] - n1[1]) for v, o, n1, n2 in zip(VARS, ob, b1, b2)])
        else:
            if oa + b2[0][1] - A0 < 0 or any(o + n2[1] - n1[1] < 0 for o, n1, n2 in zip(ob, b1, b2[1:])):
                continue
            s = cfg(expr("a", oa), t1, [expr(v, o) for v, o in zip(VARS, ob)])
            e = cfg(None, t2, [expr("a", oa + b2[0][1] - A0)] +
                    [expr(v, o + n2[1] - n1[1]) for v, o, n1, n2 in zip(VARS, ob, b1, b2[1:])])
        for carry in (3, 10):        # 10: a zigzag that eats a block word by word carries a longer word along
            symtm.MAX_CARRY = carry
            try:
                th, _ = prove(M, name, s, e, doc=doc or f"One visit of the left end ({kind}).", rotate=True,
                              count_first=True, max_seg=40)
                steps = re.search(r"steps \(([^)]*)\)", th).group(1)
                return th, X2, dict(name=name, kind=kind, start=s, end=e, steps=steps)
            except Exception as ex:      # NeedSplit: a block must be longer; try the next offsets
                last = ex
            finally:
                symtm.MAX_CARRY = 3
    raise RuntimeError(f"{name}: {last}")


def chain(prefix, X, n, stop_at_recycle=True):
    """Rules for n successive visits from X (fewer if a recycle comes first)."""
    out = []
    for i in range(n):
        th, X2, info = visit_rule(f"{prefix}{i + 1}", X)
        out.append((th, info))
        X = X2
        if info["kind"] == "recycle" and stop_at_recycle:
            break
    return out, X


C = "100"
P = "10011110111100111"       # tails after the block (10111)^b at the start of a level
Q = "1001111011110111"
S = "100111101111001"
R = "10011110111110111"
N = 16            # block size of the concrete instances (>= LONG all along)

# name prefix, start X, visits, description
E6 = "111100"

# name prefix, start X, visits, description
CHAINS = [
    ("enterP", C * N + P[3:], 5, "after the grow phase with tail P = 100 1111 0 1111 00 111: five visits to state 11 of the drain cycle"),
    ("enterQ", C * N + Q[3:], 18, "the same with tail Q = 100 1111 0 1111 0 111: 18 visits to state 9 of the drain cycle"),
    ("drain", C * N + "11100111", 14, "the drain cycle: 14 visits, the block (100)^c loses four words"),
    ("end0_", C * 4 + "11100111", 40, "end of the drain phase from (100)^4 111 00 111, up to and including the recycle"),
    ("end1_", C * 5 + "11100111", 40, "the same from (100)^5"),
    ("end2_", C * 6 + "11100111", 40, "the same from (100)^6"),
    ("end3_", C * 7 + "11100111", 40, "the same from (100)^7"),
    ("enterR", C * N + R[3:], 5, "tail R = 100 1111 0 11111 0 111: four visits and an early recycle that leaves the block (100)^c in the tail"),
    ("enterS", C * N + S[3:], 5, "tail S = 100 1111 0 1111 00 1: five visits into the pour cycle"),
    ("pourS", C * N + E6 * N + "1111", 2, "the pour cycle with the end 1111: two visits, two words 100 go and one word 111100 comes"),
    ("endS0_", C * 3 + E6 * N + "1111", 10, "end of the pour phase from (100)^3, up to and including the recycle"),
    ("endS1_", C * 4 + E6 * N + "1111", 10, "the same from (100)^4"),
]

HAND = [
    ("grow",
     "0^inf D> 0 0 (1)^5 (00111)^a (100)^a+1 (10111)^b+1 R",
     "0^inf D> 0 0 (1)^5 (00111)^a+1 (100)^a+2 (10111)^b R",
     "Grow phase, one visit of the left end: a word `10111` of the right block becomes one `00111` and one `100` on the left (the tape further right, R, is not read)."),
    ("pour",
     "0^inf D> 0 0 (1)^5 (00111)^a (100)^c+4 (111100)^e 0 0^inf",
     "0^inf D> 0 0 (1)^5 (00111)^a+2 (100)^c+2 (111100)^e+1 0 0^inf",
     "Pour phase, two visits of the left end: two words `100` go, the left block gains two words `00111` and the right block one `111100`."),
]


def build():
    hand = []
    for name, a, b, doc in HAND:
        th, _ = prove(M, name, a, b, doc=doc, rotate=True, count_first=True, max_seg=40)
        hand.append((th, dict(name=name, kind="phase", start=a, end=b, steps=re.search(r"steps \(([^)]*)\)", th).group(1))))
    visits = []
    for prefix, X, n, doc in CHAINS:
        rules, _ = chain(prefix, X, n)
        for th, info in rules:
            info["chain"] = doc
        visits += rules
    return hand, visits


def main():
    hand, visits = build()
    if "--list" in sys.argv:
        for _, i in hand + visits:
            print(f"{i['name']:10} {i['steps']:28} {i['start']}  ->  {i['end']}")
        return
    lean = os.path.join(HERE, "..", "lean")
    open(os.path.join(lean, "Rules.lean"), "w").write(rules_file(
        "Machine", NS, [t for t, _ in hand], f"Phase rules of {M}, generated by `py/rules.py`; do not edit by hand."))
    open(os.path.join(lean, "Visits.lean"), "w").write(rules_file(
        "Machine", NS, [t for t, _ in visits],
        f"One-visit rules of {M} (the levels with tails P and Q), generated by `py/rules.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
