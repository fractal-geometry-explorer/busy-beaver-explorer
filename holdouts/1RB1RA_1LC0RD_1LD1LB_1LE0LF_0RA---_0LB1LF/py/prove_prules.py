"""Prove the halving-chain engine's learned parametric rules (hce.cpp `export`) with bbtools.symtm.

hce.cpp learns a rule for a window of tokens whose big counts are n = base + 6 t (t >= 0) from five probe runs and an
affine fit.  That is a heuristic.  This script states each rule for the original machine
1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF (G's state E is the machine's F, G's D0 = 1RA is the detour D0 1LE, E0 0RA,
A1 1RA) for every t and every tape around the window, and asks symtm to prove it; Lean then checks the proofs.

usage: python3 prove_prules.py RULES.txt OUT.lean [MAXRULES [SKIP]]   (RULES.txt from `hce export N RULES.txt`)
Rules are numbered by how often the run used them (most used first); MAXRULES keeps the first ones, SKIP is a
comma-separated list of numbers left out of OUT.lean (rules whose proof Lean's kernel rejects on time).
Prints how many rules (and how many of their uses) symtm proved.

lean/LearnedRules.lean: python3 py/prove_prules.py rules13.txt lean/LearnedRules.lean 100 (with the rules of
`NOBLK=1 NOCYC=1 c/hce export 1e13 rules13.txt`).
"""
import os
import sys

REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF"
STATE = "ABCDF"  # G state index -> the machine's state name


def read_rules(path):
    lines = open(path).read().split("\n")
    i, out = 0, []
    while i < len(lines):
        if not lines[i].startswith("RULE"):
            i += 1
            continue
        h = lines[i].split()
        r = dict(uses=int(h[1]), mode=h[2], q=int(h[3]), dir=int(h[4]), lend=h[5] == "1", rend=h[6] == "1")
        i += 1
        r["P"] = [tuple(map(int, x.split(":"))) for x in lines[i].split()[1:]]
        i += 1

        def toks(tag, out_kind):
            nonlocal i
            n = int(lines[i].split()[1]); assert lines[i].startswith(tag)
            i += 1
            v = []
            for _ in range(n):
                p = lines[i].split(); i += 1
                if out_kind:
                    v.append((p[0], int(p[1]), "" if p[2] == "-" else p[2], [int(x) for x in p[3:]]))
                else:
                    v.append((p[0], int(p[1]), "" if p[2] == "-" else p[2]))
            return v
        r["lt"] = toks("LT", False); r["rt"] = toks("RT", False)
        r["lo"] = toks("LO", True); r["ro"] = toks("RO", True)
        e = lines[i].split(); i += 1
        r.update(m2=e[1], q2=int(e[2]), d2=int(e[3]), keepL=int(e[4]), keepR=int(e[5]), s0=int(e[6]), sa=[int(x) for x in e[7:]])
        out.append(r)
    return out


def expr(c0, coef):
    """c0 + sum coef[j] * t_j as a symtm expression; None if a coefficient is negative."""
    if any(a < 0 for a in coef):
        return None
    parts = [f"{a}*t{j}" for j, a in enumerate(coef) if a]
    return "+".join(parts + [str(c0)]) if parts else str(c0)


# a piece is ('bits', '0101') or ('rep', word, c0, coef)
def pieces(kind, c0, w, coef):
    if kind == "B":
        return [("bits", w)]
    if kind == "S":  # 1 (01)^(n+1)
        return [("bits", "1"), ("rep", "01", c0 + 1, coef)]
    if kind == "D":  # 1 (11)^n 00
        return [("bits", "1"), ("rep", "11", c0, coef), ("bits", "00")]
    if kind == "U":
        return [("rep", w, c0, coef)]
    raise ValueError(kind)


def variant(ps, g, peel):
    """Rewrite each parametric repeat (w)^(c0 + 6 t) as (w^g)^(...) and optionally peel one copy off an end, so that
    symtm's shift rules stop where the rule's end is (a run can pass its end inside the last copy of a repeat)."""
    out = []
    for p in ps:
        if p[0] != "rep" or not any(p[3]):
            out.append(p)
            continue
        _, w, c0, coef = p
        gg = g if all(a % g == 0 for a in coef) else 1
        q, rem = divmod(c0, gg)
        W, co = w * gg, [a // gg for a in coef]
        if peel and q >= 1:
            if peel == "last":
                out += [("rep", W, q - 1, co), ("bits", W + w * rem)]
            else:
                out += [("bits", w * rem + W), ("rep", W, q - 1, co)]
        else:
            out += [("rep", W, q, co), ("bits", w * rem)]
    return out


def render(ps):
    out = []
    for p in ps:
        if p[0] == "bits":
            out.extend(p[1])
        else:
            e = expr(p[2], p[3])
            if e is None:
                return None
            if e == "0":
                continue
            if not any(p[3]):
                out.extend(p[1] * p[2])
                continue
            out.append(f"({p[1]})^{e}")
    return " ".join(out)


def pop_last_cell(ps):
    """Split off the last cell of a piece list (the counts are >= 1 where a repeat ends the list)."""
    ps = list(ps)
    while ps:
        p = ps.pop()
        if p[0] == "bits":
            if not p[1]:
                continue
            if len(p[1]) > 1:
                ps.append(("bits", p[1][:-1]))
            return ps, p[1][-1]
        if p[2] == 0 and not any(p[3]):
            continue
        if p[2] < 1:
            return None, None
        ps.append(("rep", p[1], p[2] - 1, p[3]))
        if len(p[1]) > 1:
            ps.append(("bits", p[1][:-1]))
        return ps, p[1][-1]
    return None, None


GAD = {"R": "0100", "L": "1", "J": "100"}


def config(left, mode, q, d, right, lend, rend, g=1, peel=None):
    """symtm string: left/right piece lists (tape order), head gadget of the mode."""
    left, right = variant(left, g, peel), variant(right, g, peel)
    lctx = "0^inf" if lend else "L"
    rctx = "0^inf" if rend else "R"
    if mode == "R":
        st, lp, head, rp = "A", left, "", [("bits", "0100")] + right
    elif mode in "LJ":
        lp, c = pop_last_cell(left)
        if lp is None and lend and not render(left):
            lp, c = [], "0"
        if lp is None:
            return None
        st = "B" if mode == "L" else "C"
        rp = [("bits", c + GAD[mode])] + right
    elif d > 0:
        st, lp, rp = STATE[q], left, right
    elif lend and not left:
        st, lp, rp = STATE[q], [], [("bits", "0")] + right
    else:
        lp, c = pop_last_cell(left)
        if lp is None:
            return None
        st, rp = STATE[q], [("bits", c)] + right
    a, b = render(lp), render(rp)
    if a is None or b is None:
        return None
    return f"{lctx} {a} {st}> {b} {rctx}".replace("  ", " ")


def statement(r, g=1, peel=None):
    np_ = len(r["P"])
    zero = [0] * np_
    par = {(s, i): j for j, (s, i) in enumerate(r["P"])}

    def inp(side, toks):
        ps = []
        for i, (k, n, w) in enumerate(toks):
            coef = list(zero)
            if (side, i) in par:
                coef[par[(side, i)]] = 6
            ps += pieces(k, n, w, coef)
        return ps
    lt, rt = inp(0, r["lt"]), inp(1, [t for t in r["rt"]])
    start = config(lt, r["mode"], r["q"], r["dir"], rt, r["lend"], r["rend"], g, peel)
    # end: lt[:keepL] lo  gadget  ro rt[keepR:]
    keepR = len(r["rt"]) if r["keepR"] < 0 else r["keepR"]
    kl = inp(0, r["lt"][:r["keepL"]]) if r["keepL"] else []
    lo = [p for (k, c0, w, a) in r["lo"] for p in pieces(k, c0, w, a)]
    ro = [p for (k, c0, w, a) in r["ro"] for p in pieces(k, c0, w, a)]
    rest = []
    for i in range(keepR, len(r["rt"])):
        k, n, w = r["rt"][i]
        coef = list(zero)
        if (1, i) in par:
            coef[par[(1, i)]] = 6
        rest += pieces(k, n, w, coef)
    left_end = kl + lo
    if (r["m2"] in "LJ" or r["d2"] < 0) and not r["lend"] and not left_end:
        # the head ends on the last cell of L: give the state and the tape right of it
        st = {"L": "B", "J": "C"}.get(r["m2"], STATE[r["q2"]])
        right = variant(([("bits", GAD[r["m2"]])] if r["m2"] in GAD else []) + ro + rest, g, None)
        b = render(right)
        return start, (st, b), "left-exit"
    end = config(left_end, r["m2"], r["q2"], r["d2"], ro + rest, r["lend"], r["rend"], g, None)
    return start, end, None


import itertools


def concrete(cfg, val):
    """The configuration as a string for the variable values `val` (contexts and the head as markers)."""
    def side(toks):
        out = []
        for t in toks:
            if isinstance(t, int):
                out.append(str(t))
            elif isinstance(t, symtm.Rep):
                n = t.n.k + sum(a * val[v] for v, a in t.n.c.items())
                if n < 0:
                    return None
                out.append("".join(map(str, t.word)) * n)
            elif isinstance(t, symtm.Blank):
                out.append("[")
            else:
                out.append("<" + t.name + ">")
        return "".join(out)
    a, b = side(cfg.left), side(cfg.right)
    if a is None or b is None:
        return None
    a = a.replace("[", "^").lstrip("^0")  # blank tape absorbs zeros
    b = b.replace("[", "$")
    b = b[:b.index("$")].rstrip("0") + "$" if "$" in b else b
    return a + "|" + symtm.STATES[cfg.state] + "|" + b


def same_numeric(c1, c2, vs):
    for vals in itertools.product((0, 1, 2, 5), repeat=len(vs)):
        val = dict(zip(vs, vals))
        x, y = concrete(c1, val), concrete(c2, val)
        if x is None or x != y:
            return False
    return True


def run_to(m, start, end):
    """Run from start until the configuration equals `end` for all tested values (or the head touches a context,
    if end is None).  Returns the final configuration."""
    c = symtm.Config.parse(start)
    vs = sorted(c.vars() | (end.vars() if end is not None else set()))
    tr = []
    if end is None:
        try:
            symtm.run(m, c, lambda x: False, max_moves=200000, trace=tr, rotate=True)
        except symtm.TouchContext:
            return tr[-1][2] if tr else symtm.Config.parse(start)
        raise symtm.ProofError("no exit")
    try:
        return symtm.run(m, c, lambda x: not x.steps.is_zero() and same_numeric(x, end, vs), max_moves=200000,
                         rotate=True)
    except symtm.TouchContext as e:
        raise symtm.ProofError("passed the end") from e


def prove_left_exit(m, name, start, claim, doc):
    """The rule ends with the head on the last cell of L.  Prove the run up to the step before it (the head on the first
    cell of the window) and check that step here: a move left into state `claim[0]` that leaves the tape `claim[1]`
    right of the head."""
    st, rtape = claim
    pre = run_to(m, start, None)
    cell = pre.right[0]
    if not isinstance(cell, int):
        raise symtm.ProofError("head on a repeat")
    q = symtm.STATES[pre.state]
    w, d, q2 = step_of(q, cell)
    if d != "L" or q2 != st:
        raise symtm.ProofError(f"last step {q}{cell} -> {w}{d}{q2}, rule says {st}")
    after = symtm.Config([symtm.Ctx("L")], 0, [w] + pre.right[1:])
    claimc = symtm.Config([symtm.Ctx("L")], 0, symtm.tokens(rtape + " R"))
    if not same_numeric(after, claimc, sorted(after.vars() | claimc.vars())):
        raise symtm.ProofError(f"tape {after} vs {claimc}")
    text, fin = symtm.prove(m, name, start, pre, doc=doc + f" Stated one step before its end: then {q} reads {cell} and moves left into {st}.",
                            rotate=True, count_first=True, max_seg=40)
    return text


TBL = {}


def step_of(q, c):
    if not TBL:
        for i, s in enumerate(M.split("_")):
            for b in range(2):
                x = s[3 * b:3 * b + 3]
                TBL[("ABCDEF"[i], b)] = None if x == "---" else (int(x[0]), x[1], x[2])
    return TBL[(q, c)]


VARIANTS = [(1, None), (1, "last"), (1, "first"), (2, None), (2, "last"), (2, "first"), (3, None), (3, "last"),
            (6, None), (6, "last"), (6, "first"), (3, "first")]


def prove_rule(m, idx, r):
    last = None
    for g, peel in VARIANTS:
        start, end, note = statement(r, g, peel)
        if start is None or end is None or (note is None and isinstance(end, str) is False):
            last = "unstated"
            continue
        doc = f"Learned rule {idx} ({r['uses']} uses on the way to 10^13)."
        try:
            if note == "left-exit":
                if end[1] is None:
                    last = "unstated"; continue
                return prove_left_exit(m, f"prule{idx}", start, end, doc), None
            fin = run_to(m, start, symtm.Config.parse(end))
            text, fin = symtm.prove(m, f"prule{idx}", start, fin, doc=doc + f" Engine form of the end: {end}.", rotate=True,
                                    count_first=True, max_seg=40)
            return text, None
        except Exception as e:
            last = type(e).__name__ + ": " + str(e)[:120]
    return None, last


def main():
    rules = read_rules(sys.argv[1])
    out = sys.argv[2]
    maxr = int(sys.argv[3]) if len(sys.argv) > 3 else len(rules)
    skip = set(int(x) for x in sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()
    rules.sort(key=lambda r: -r["uses"])
    m = Machine.parse(M)
    th, ok, okuse, why = [], 0, 0, {}
    tot = sum(r["uses"] for r in rules[:maxr])
    fails = []
    for idx, r in enumerate(rules[:maxr]):
        text, err = prove_rule(m, idx, r)
        if text is None:
            k = err.split(":")[0] + ":" + (err.split(":")[2][:25] if err.count(":") > 1 else "")
            why[k] = why.get(k, 0) + 1
            fails.append((idx, r["uses"], err))
            if os.environ.get("VERBOSE"):
                print("FAIL", idx, r["uses"], statement(r)[:2], err)
            continue
        ok += 1; okuse += r["uses"]
        if idx not in skip:
            th.append(text)
    print(f"proved {ok} of {min(maxr, len(rules))} rules, {okuse} of {tot} uses; not proved: {why}")
    with open(out, "w") as f:
        f.write(symtm.rules_file("Machine", "H99431", th,
                                 "# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF: the halving-chain engine's most used learned rules\n\n"
                                 "c/hce.cpp learns a rule for a window of tokens with a large count n = base + 6 t from five probe runs; "
                                 "here each rule is stated for this machine (with its detours) for every t and every tape around it, "
                                 "numbered by how often the run to 10^13 steps used it. A rule whose run ends on the cell left of the window "
                                 "is stated one step before.\n\nWritten by `py/prove_prules.py` with `tools/py/bbtools/symtm.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
