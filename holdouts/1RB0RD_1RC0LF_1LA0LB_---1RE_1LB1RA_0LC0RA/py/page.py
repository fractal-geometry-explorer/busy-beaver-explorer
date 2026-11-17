"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py

In page/levels.html, `/*CORE*/` is replaced by page/core.js (the plain machine and the rule templates, shared by all
panels) and `/*DATA*/` by what the panels check, read from the Lean files: the cycle rules and shift rules of
lean/ExecData.lean, the 1,144 classes of lean/ClassData.lean (the tails numbered in order of first appearance) and
the start tail of lean/Arrive.lean. The sections "shape", "try-cycles" (the stepper), "trust" and
"related-machines" (written by holdouts/related.py) are kept from status.json as they are.
"""
import json
import os
import re

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
SECTIONS = [
    ("levels", "Four levels", "From six states to 1,144 classes"),
    ("shape", None, None),
    ("words", "Level 1 to level 2", "Two blocks and a tail"),
    ("cycles", "Level 2 to level 3", "The tail runs in a cycle"),
    ("try-cycles", None, None),
    ("rounds", "Level 3 to level 4", "When the left block is empty"),
    ("closed", "Level 4", "A closed set of 1,144 classes"),
    ("trust", None, None),
    ("neighbours", "A warning", "Nearby tapes do halt"),
    ("bottom", "The bottom line", "It never halts"),
]
EYEBROW = {"shape": "Level 1 · First look", "try-cycles": "Level 3 · Try it"}


def bits(s):
    return "".join("1" if x.strip() == "true" else "0" for x in s.split(",") if x.strip())


def lean_data():
    src = open(os.path.join(D, "lean", "ExecData.lean")).read()
    rules = []
    for m in re.finditer(r"/-- Cycle rule (\d+) \((\d+) events a cycle, modulus (\d+)\): `[^`]*`.*?-/\n"
                         r"def rule\d+ : CRule := ⟨(\d+),\s*\[(.*?)\]⟩\n\n"
                         r"theorem rule\d+_ok : RuleOK rule\d+ := ruleOK_of_run T0_ok (\d+)", src, re.S):
        assert m.group(3) == m.group(4)
        toks = []
        for t in re.finditer(r"\.(cell|fix|var) (?:(true|false)|\[([^\]]*)\] (\d+)(?: (\d+))?)", m.group(5)):
            if t.group(1) == "cell":
                toks.append(["c", "1" if t.group(2) == "true" else "0"])
            elif t.group(1) == "fix":
                toks.append(["f", bits(t.group(3)), int(t.group(4))])
            else:
                toks.append(["v", bits(t.group(3)), int(t.group(4)), int(t.group(5))])
        rules.append({"n": int(m.group(1)), "ev": int(m.group(2)), "mod": int(m.group(4)), "moves": int(m.group(6)), "t": toks})
    shift = [{"d": m.group(1), "i": int(m.group(2)), "q": m.group(3), "w": bits(m.group(4)), "k": int(m.group(5)),
              "u": bits(m.group(6)), "v": bits(m.group(7)), "s": int(m.group(8))}
             for m in re.finditer(r"def sh([RL])(\d+) : SRule := ⟨\.(\w), \[([^\]]*)\], (\d+), \[([^\]]*)\], "
                                  r"\[([^\]]*)\], (\d+)⟩", src)]
    assert len(rules) == 6 and len(shift) == 15, (len(rules), len(shift))
    cls = re.findall(r'⟨bits "([01]*)", (\d+), (\d+), (\d+), bits "([01]*)", (\d+), (\d+)⟩',
                     open(os.path.join(D, "lean", "ClassData.lean")).read())
    tails, idx = [], {}

    def ti(t):
        if t not in idx:
            idx[t] = len(tails)
            tails.append(t)
        return idx[t]
    for c in cls:
        ti(c[0])
    # [tail, r0, m, K, next tail, k, c]: the class B = r0 + m x, one round in K + 1 moves, to B' = k + c x
    classes = [[ti(c[0]), int(c[1]), int(c[2]), int(c[3]), ti(c[4]), int(c[5]), int(c[6])] for c in cls]
    assert len(classes) == 1144 and len(tails) == 62, (len(classes), len(tails))
    start = re.search(r'def startTail : List Bool := bits "([01]*)"', open(os.path.join(D, "lean", "Arrive.lean")).read()).group(1)
    return {"rules": rules, "shift": shift, "tails": tails, "classes": classes, "start": start}


def page(name):
    s = open(os.path.join(D, "page", name + ".html")).read()
    if "/*CORE*/" in s:
        s = s.replace("/*CORE*/", open(os.path.join(D, "page", "core.js")).read().rstrip("\n"))
        s = s.replace("/*DATA*/", json.dumps(lean_data(), separators=(",", ":")))
    return s.rstrip("\n").split("\n")


path = os.path.join(D, "status.json")
spec = json.load(open(path))
old = {s["id"]: s for s in spec["explainer"]["sections"]}
out = []
for i, e, h in SECTIONS:
    if e is None:
        s = dict(old[i])
        s["eyebrow"] = EYEBROW.get(i, s["eyebrow"])
        out.append(s)
    else:
        out.append({"id": i, "eyebrow": e, "heading": h, "html": page(i)})
out += [s for s in spec["explainer"]["sections"] if s["id"] == "related-machines"]
spec["explainer"]["sections"] = out
with open(path, "w") as f:
    json.dump(spec, f, indent=1, ensure_ascii=False)
    f.write("\n")
