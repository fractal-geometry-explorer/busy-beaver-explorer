"""Writes lean/Rules.lean: the building blocks of the phase map and the epoch ends, each proved by bbtools.symtm from
a symbolic trace (shift rules, `rfl`, `omega`).  `lean/Phase.lean` (by hand) composes them.

P c u x is the configuration  0^inf 1^c (01)^u 0 0 (10)^x F> 0^inf  (state F just right of the tape).

usage: python3 rules.py > ../lean/Rules.lean
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, Rep, Blank, canon
from autoprove import find, cfg_str

M = "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"
NS = "H116538"

RULES = [
    ("start", "From blank tape to P 3 3 5 in 139 steps.", "0^inf A> 0^inf", "0^inf 1 1 1 (01)^3 0 0 (10)^5 F> 0^inf"),
    ("first", "From P 3 3 5 (an epoch with no phase) to the next epoch P 20 3 5.",
     "0^inf 1 1 1 (01)^3 0 0 (10)^5 F> 0^inf", None),
    ("bounce", "One bounce of a phase: two units leave the block on the left, three join the block on the right.",
     "L (01)^x+2 0 0 (10)^y+1 F> 0^inf", "L (01)^x 0 0 (10)^y+4 F> 0^inf"),
    ("glue2", "The start of a phase from P (c+4) 2 (x+1): the run of 1s loses 4 and the right block moves to the left.",
     "0^inf 1^c+4 (01)^2 0 0 (10)^x+1 F> 0^inf", "0^inf 1^c (01)^x+7 0 0 (10)^2 F> 0^inf"),
    ("glue3", "The start of a phase from P (c+4) 3 (x+1).",
     "0^inf 1^c+4 (01)^3 0 0 (10)^x+1 F> 0^inf", "0^inf 1^c (01)^x+8 0 0 (10)^2 F> 0^inf"),
    ("end03", "Epoch end P 0 3 (x+16) (the same tape as P 1 2 (x+16)): a new epoch P (2x+37) 3 5.",
     "0^inf (01)^3 0 0 (10)^x+16 F> 0^inf", None),
    ("end32", "Epoch end P 3 2 (x+16): a new epoch P (2x+40) 3 5.",
     "0^inf 1 1 1 (01)^2 0 0 (10)^x+16 F> 0^inf", None),
    ("end33", "Epoch end P 3 3 (x+16): a new epoch P (2x+42) 3 5.",
     "0^inf 1 1 1 (01)^3 0 0 (10)^x+16 F> 0^inf", None),
    ("end02", "Epoch end P 0 2 (x+16): C reads 0 at the left end next, a halt.",
     "0^inf (01)^2 0 0 (10)^x+16 F> 0^inf", "HALT"),
    ("end13", "Epoch end P 1 3 (x+16): a halt.",
     "0^inf 1 (01)^3 0 0 (10)^x+16 F> 0^inf", "HALT"),
    ("end22", "Epoch end P 2 2 (x+16): a halt.",
     "0^inf 1 1 (01)^2 0 0 (10)^x+16 F> 0^inf", "HALT"),
    ("end23", "Epoch end P 2 3 (x+16): a halt.",
     "0^inf 1 1 (01)^3 0 0 (10)^x+16 F> 0^inf", "HALT"),
]


TAIL = [0, 1, 0, 1, 0, 1, 0, 0] + [1, 0] * 5


def new_epoch(c):
    """F just right of the tape, the tape 0^inf 1...1 (01)^3 0 0 (10)^5 with the ones possibly as repeats."""
    if c.state != 5 or len(c.right) != 1 or not isinstance(c.right[0], Blank) or c.steps.is_zero():
        return False
    left = canon(c.left)
    if len(left) < len(TAIL) + 1 or left[len(left) - len(TAIL):] != TAIL:
        return False
    body = left[1:len(left) - len(TAIL)]
    return isinstance(left[0], Blank) and len(body) > 0 and all(t == 1 or (isinstance(t, Rep) and set(t.word) == {1}) for t in body)


def about_to_halt(c):
    """C reading a 0: the next step halts."""
    if c.state != 2:
        return False
    r = c.right[0]
    return r == 0 or isinstance(r, Blank) or (isinstance(r, Rep) and r.word[0] == 0)


def _split_cfg(t):
    """`⟨A, B, .Q⟩` -> (A, B, Q), splitting at top-level commas."""
    assert t.startswith("⟨") and t.endswith("⟩")
    body, parts, depth, cur = t[1:-1], [], 0, ""
    for ch in body:
        if ch in "([⟨":
            depth += 1
        elif ch in ")]⟩":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    parts.append(cur.strip())
    return parts


def _args(s):
    """Split `(a) (b) (c)` into the parenthesized arguments (without their outer parentheses)."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        elif ch == ")":
            depth -= 1
            if depth == 0:
                out.append(cur)
                continue
        if depth > 0:
            cur += ch
    return out


def _sub1(s, old, new):
    assert s.count(old) == 1, (s, old)
    return s.replace(old, new)


def generic_cross(text):
    """Rewrite each `cross_l`/`cross_r` use so that it is checked once for a variable count `k` and variable tapes
    and then instantiated.  Checking it directly at a count like `x + 15` makes the kernel unfold `rep (x + 15)`
    (a deterministic timeout)."""
    lines = text.split("\n")
    for i, l in enumerate(lines):
        m = re.match(r"    (cross_[lr]) trans (c\d+) (.*)$", l)
        if not m:
            continue
        fn, c, rest = m.groups()
        K, Lt, Rt = _args(rest)
        h = re.match(r"  have (h\d+) : steps \(\((.*?)\) \* (\d+)\) (⟨.*⟩) = some (⟨.*⟩) :=$", lines[i - 1])
        assert h and h.group(2) == K, lines[i - 1]
        hn, _, s, a, b = h.groups()
        (l1, r1, q), (l2, r2, _) = _split_cfg(a), _split_cfg(b)
        if fn == "cross_r":
            l1, l2, r1, r2 = _sub1(l1, Lt, "L"), _sub1(l2, Lt, "L"), _sub1(r1, Rt, "R"), "R" if r2 == Rt else _sub1(r2, Rt, "R")
        else:
            l1, l2, r1, r2 = _sub1(l1, Lt, "L"), "L" if l2 == Lt else _sub1(l2, Lt, "L"), _sub1(r1, Rt, "R"), _sub1(r2, Rt, "R")
        gen = f"steps (k * {s}) ⟨{l1}, {r1}, {q}⟩ = some ⟨{l2}, {r2}, {q}⟩"
        gen = gen.replace(f"rep ({K}) ", "rep k ")
        assert K not in gen.replace("rep k", ""), gen
        lines[i] = (f"    (show ∀ k : Nat, ∀ L R : Tape, {gen} from {fn} trans {c}) ({K}) ({Lt}) ({Rt})")
    return "\n".join(lines)


def main():
    out = ["import Machine", "", f"/-! Rules of {M}, generated by `py/rules.py`; do not edit by hand. -/", "",
           f"namespace {NS}", "", "open TM", ""]
    for name, doc, start, end in RULES:
        if end is None:
            end = cfg_str(find(M, start, new_epoch))
        elif end == "HALT":
            end = cfg_str(find(M, start, about_to_halt))
        t, f = prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=60)
        out += [generic_cross(t), ""]
    out.append(f"end {NS}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
