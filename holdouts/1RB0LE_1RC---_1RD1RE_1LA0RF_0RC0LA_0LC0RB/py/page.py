"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/page.py
    python3 holdouts/build_pages.py 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB

The sections are hand-written HTML (each with its own inline script; page/levels.html defines the shared library
`window.PW`). This file only puts the proof's data into page/levels.html in place of `__DATA__`: the phase forms
(py/ends.py FORMS, the same strings the Lean files are generated from), the 27 rules with their step counts
(py/macro.py RULES), the replay of the branch table (py/macro.py, the 196 moves that lean/Table.lean checks) and
the invariant's inequalities (parsed from lean/Closed.lean), so the page shows exactly what Lean checks.
The section "shape" (written by holdouts/gen.py) is kept after the hand-written ones.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DIR = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import ends   # noqa: E402
import macro  # noqa: E402

SECTIONS = [
    ("levels", "Four levels", "From six states to a list of inequalities"),
    ("p-halt", "Level 1", "The machine, and the only way it can halt"),
    ("p-forms", "Level 1 to level 2", "The tape is a list of numbers"),
    ("p-passes", "Level 2", "Crossing a run in one move"),
    ("p-rules", "Level 2", "One rule, for any size"),
    ("p-branch", "Level 2 to level 3", "Ten forms and twenty cases"),
    ("p-replay", "Level 3", "Following the map from the blank tape"),
    ("p-invariant", "Level 4", "Why the moves never run out"),
    ("bottom", "The bottom line", "It never halts"),
]
KEEP = ["shape"]          # generated sections kept after the hand-written ones
GOOD = {"O": "gOp", "O0": "gO0", "S1": "gS1", "RF": "gRF", "EF": "gEF", "T3": "gT3", "T2": "gT2", "U3": "gU3",
        "RG": "gRG", "RG3": "gRG3"}
SHAPE_OLD = "the macro structure behind them is the next thing to find.</p>"
SHAPE_NEW = ("the macro structure behind them is the subject of the levels above, and the Lean proof settles "
             "the question.</p>")


def form(f):
    fn = ends.FORMS[f]
    vs = list(fn.__code__.co_varnames[:fn.__code__.co_argcount])
    s = fn(*["{%s}" % v for v in vs]).split()
    assert s[0] == "0^inf" and s[-1] == "0^inf"
    s = s[1:-1]
    hi = [i for i, t in enumerate(s) if t.endswith(">")]
    assert len(hi) == 1
    h = hi[0]
    side = "L" if h == 0 else "R"
    assert side == "L" or h == len(s) - 1
    toks = []
    for t in (s[1:] if side == "L" else s[:-1]):
        m = re.fullmatch(r"\(([01]+)\)\^\{(\w+)\}", t)
        if m:
            toks.append([m.group(1), m.group(2)])
        else:
            assert re.fullmatch(r"[01]", t), t
            if toks and isinstance(toks[-1], str):
                toks[-1] += t
            else:
                toks.append(t)
    return {"vars": vs, "state": s[h][0], "side": side, "toks": toks}


def lin(s):
    out = {}
    for term in s.split("+"):
        term = term.strip()
        m = re.fullmatch(r"(\d+) \* (\w+)", term)
        if m:
            out[m.group(2)] = int(m.group(1))
        elif term.isdigit():
            out["1"] = int(term)
        else:
            out[term] = 1
    return out


def goods():
    src = open(os.path.join(DIR, "lean", "Closed.lean")).read()
    out = {}
    for f, g in GOOD.items():
        m = re.search(r"def %s \(([\w ]+) : Nat\) : Prop :=\n((?:  .*\n)+)" % g, src)
        ineq = []
        for line in m.group(2).splitlines():
            line = line.strip().rstrip("∧").strip()
            lhs, rhs = line.split("≤")
            ineq.append([lin(lhs), lin(rhs), line])
        out[f] = {"name": g, "vars": m.group(1).split(), "ineq": ineq}
    return out


def replay():
    used = []
    ap, it = macro.apply, macro.iterate

    def apply(rule, P):
        used.append([rule, 1])
        return ap(rule, P)

    def iterate(rule, P, k):
        n = len(used)
        r = it(rule, P, k)
        del used[n:]                # iterate calls apply once; record the k turns instead
        used.append([rule, k])
        return r
    macro.apply, macro.iterate = apply, iterate
    rows, esc = macro.replay(1e30)
    macro.apply, macro.iterate = ap, it
    assert esc is None
    moves = []
    for i, (t, f, P) in enumerate(rows):
        moves.append({"t": str(t), "f": f, "P": [str(p) for p in P]})
    # the move out of state i is the rule recorded i-th (the t3_s1 re-reading records none)
    k = 0
    for i in range(len(rows) - 1):
        f, P = rows[i][1], rows[i][2]
        if f == "T3" and P[1] == P[2] == P[3] == 0:
            moves[i]["r"] = ["t3_s1", 1]
            continue
        moves[i]["r"] = used[k]
        k += 1
    assert k == len(used) - 1      # the replay also computes the move out of its last state
    return moves


def data():
    forms = {f: form(f) for f in ends.FORMS}
    rules = {k: {"from": v[0], "fa": v[1], "to": v[2], "ta": v[3], "steps": v[4]} for k, v in macro.RULES.items()}
    return {"machine": "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB", "forms": forms, "rules": rules,
            "replay": replay(), "good": goods()}


def main():
    blob = json.dumps(data(), separators=(",", ":"), ensure_ascii=False).replace("</", "<\\/")
    secs = []
    for sid, eyebrow, heading in SECTIONS:
        body = open(os.path.join(DIR, "page", sid + ".html")).read().rstrip("\n")
        if "__DATA__" in body:
            body = body.replace("__DATA__", blob)
        secs.append({"id": sid, "eyebrow": eyebrow, "heading": heading, "html": body.split("\n")})
    p = os.path.join(DIR, "status.json")
    spec = json.load(open(p))
    old = {s["id"]: s for s in spec["explainer"].get("sections", [])}
    kept = []
    for k in KEEP:
        if k in old:
            s = json.loads(json.dumps(old[k]))
            s["html"] = [line.replace(SHAPE_OLD, SHAPE_NEW) for line in s["html"]]
            kept.append(s)
    spec["explainer"]["sections"] = secs + kept
    nl = open(p).read().endswith("\n")
    with open(p, "w") as f:
        json.dump(spec, f, indent=1, ensure_ascii=False)
        if nl:
            f.write("\n")
    print("wrote %d sections" % len(secs + kept))


if __name__ == "__main__":
    main()
