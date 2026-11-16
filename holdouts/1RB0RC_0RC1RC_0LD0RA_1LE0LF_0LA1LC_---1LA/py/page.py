"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py

In page/levels.html, `/*CORE*/` is replaced by page/core.js (the plain machine and the rule templates, shared by all
panels) and `/*DATA*/` by the cycle rules and shift rules read from lean/ExecData.lean, with the two phases of
lean/Phases.lean, so that the panels check exactly the statements of the Lean files. The sections "shape" and
"try-cycle" (the stepper) are kept from status.json as they are.
"""
import json
import os
import re

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
SECTIONS = [
    ("levels", "Four levels", "From six states to one number"),
    ("shape", None, None),
    ("words", "Level 1 to level 2", "Seven-cell words on the left, three-cell words on the right"),
    ("phases", "Level 2 to level 3", "Collect, expand, drain"),
    ("cycle", "Level 3 to level 4", "The left part comes back to the same state"),
    ("try-cycle", None, None),
    ("near", "A narrow escape", "Almost the same tape halts"),
    ("bottom", "The bottom line", "It never halts"),
]
EYEBROW = {"shape": "Level 1 · First look", "try-cycle": "Level 4 · Try it"}


def bits(s):
    return "".join("1" if x.strip() == "true" else "0" for x in s.split(",") if x.strip())


def lean_data():
    src = open(os.path.join(D, "lean", "ExecData.lean")).read()
    rules = []
    for m in re.finditer(r"/-- Cycle rule (\d+) \((\d+) events a cycle\): `[^`]*`.*?-/\ndef rule\d+ : List TT :=\s*"
                         r"\[(.*?)\]\n\ntheorem rule\d+_ok : RuleOK rule\d+ := ruleOK_of_run T0_ok (\d+)", src, re.S):
        toks = []
        for t in re.finditer(r"\.(cell|fix|var) (?:(true|false)|\[([^\]]*)\] (\d+)(?: (\d+))?)", m.group(3)):
            if t.group(1) == "cell":
                toks.append(["c", "1" if t.group(2) == "true" else "0"])
            elif t.group(1) == "fix":
                toks.append(["f", bits(t.group(3)), int(t.group(4))])
            else:
                toks.append(["v", bits(t.group(3)), int(t.group(4)), int(t.group(5))])
        rules.append({"n": int(m.group(1)), "ev": int(m.group(2)), "mod": 2, "moves": int(m.group(4)), "level": "native", "t": toks})
    shift = [{"d": m.group(1), "i": int(m.group(2)), "q": m.group(3), "w": bits(m.group(4)), "k": int(m.group(5)),
              "u": bits(m.group(6)), "v": bits(m.group(7)), "s": int(m.group(8))}
             for m in re.finditer(r"def sh([RL])(\d+) : SRule := ⟨\.(\w), \[([^\]]*)\], (\d+), \[([^\]]*)\], "
                                  r"\[([^\]]*)\], (\d+)⟩", src)]
    assert len(rules) == 12 and len(shift) == 31, (len(rules), len(shift))
    # lean/Phases.lean, with counts b + x (any x): colCfg (p+1) (a+1) (b+1) -> colCfg (p+3) a (b+1) in
    # 48a + 48b + 72p + 476 steps (collect2); expCfg (p+3) (c+1) (b+1) -> expCfg (p+1) (c+8) (b+1) in
    # 240b + 240c + 144p + 2812 steps (expand4). x1, x2, x3 are p, a (or c), b.
    W, V = "1011001", "110110"
    lean = [
        {"name": "collect2", "level": "kernel", "ev": 2, "mod": 1, "steps": [476, 72, 48, 48],
         "t": [["c", "0"], ["v", W, 1, 3], ["f", "101101101101101" "10" "0110110", 1], ["v", V, 1, 0], ["f", "000", 1],
               ["v", V, 1, 1], ["f", "110", 1]]},
        {"name": "expand4", "level": "kernel", "ev": 4, "mod": 1, "steps": [2812, 144, 240, 240],
         "t": [["c", "0"], ["v", W, 3, 1], ["f", "101100" "00011011001101010", 1], ["v", V, 1, 8], ["f", "000", 1],
               ["v", V, 1, 1], ["f", "110", 1]]},
    ]
    return {"lean": lean, "rules": rules, "shift": shift}


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
