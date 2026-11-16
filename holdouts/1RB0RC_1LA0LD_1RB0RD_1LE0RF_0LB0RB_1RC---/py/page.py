"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py

The page's own simulators need X, the 222,182 cells of lean/Data.lean: the placeholder @XHEX@ in page/levels.html
is replaced by the hex string Xhex of that file, so the page always runs on the stretch Lean uses.
"""
import json
import os
import re

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
STEPPER = {
    "tape": "0^inf A> 0 (1010001000100)^{k} X 0^inf",
    "vars": [{"name": "k", "label": "blocks k", "start": "7"}],
    "counters": [{"name": "t", "label": "step", "start": "16730681219"}],
    "rules": [{"name": "One period", "level": "native",
               "text": "C k reaches C (k+1) in exactly 184k + 3,029,040 steps, for every k &ge; 1 (<code>period</code>, "
                       "<code>lean/Period.lean</code>; the passes by the kernel, the two excursions through X by "
                       "<code>native_decide</code>).",
               "guard": [{"form": {"k": 1, "_": -1}, "text": "k &ge; 1"}],
               "set": {"k": {"k": 1, "_": 1}}, "add": {"t": {"k": 184, "_": 3029040}}}],
    "note": "Starts at C 7, where the run from blank tape arrives (<code>reach_C7</code>, <code>lean/Reach.lean</code>). "
            "X is the fixed stretch of 222,182 cells. The stepper does the arithmetic of the rule; it does not simulate "
            "the machine."}
SECTIONS = [
    ("levels", "Five levels", "From six states to one number", {}),
    ("shape", "First look", "The shape of the run", {}),
    ("blocks", "Level 1 to level 2", "Blocks of 16 cells", {}),
    ("tape", "Levels 3 to 5: the form", "What the tape is made of", {}),
    ("pieces", "Level 3", "One period, piece by piece", {}),
    ("window", "Level 3 to level 4", "The excursions, computed once for every n", {}),
    ("count", "Level 5", "The number k", {"stepper": STEPPER, "html_after": "count_after"}),
    ("history", "Aside: before the bouncer", "How it gets there: five epochs", {}),
    ("bottom", "The bottom line", "It never halts", {}),
]


def lines(name, xhex):
    return open(os.path.join(D, "page", name + ".html")).read().replace("@XHEX@", xhex).rstrip("\n").split("\n")


data = open(os.path.join(D, "lean", "Data.lean")).read()
xhex = re.search(r'def Xhex : String :=\s*"([0-9a-f]+)"', data).group(1)
path = os.path.join(D, "status.json")
spec = json.load(open(path))
out = []
for i, e, h, extra in SECTIONS:
    s = {"id": i, "eyebrow": e, "heading": h, "html": lines(i, xhex)}
    if "stepper" in extra:
        s["stepper"] = extra["stepper"]
    if "html_after" in extra:
        s["html_after"] = lines(extra["html_after"], xhex)
    out.append(s)
spec["explainer"]["sections"] = out
with open(path, "w") as f:
    json.dump(spec, f, indent=1, ensure_ascii=False)
    f.write("\n")
