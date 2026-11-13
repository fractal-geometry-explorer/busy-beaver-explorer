"""generic_cross: rewrite cross_l/cross_r uses in symtm proofs so they are checked once for a variable count and
then instantiated (copied from holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/py/rules.py)."""
import re


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
        if K.strip().isdigit():
            continue
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
