"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

The sections follow the proof down five levels (the machine, the tape as a list, the 62 templates, epochs, the
potential) and end with the bottom line. page/lib.js is the shared code of the panels (the plain machine, the
shift-rule simulator and the tables); it is inlined into the first section together with the certificate's tables
(py/cert_data.json and the lists of lean/Tables.lean), so the page shows exactly the numbers Lean checks.

    python3 holdouts/1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC/py/page.py
    python3 holdouts/build_pages.py 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DIR = os.path.dirname(HERE)
SECTIONS = [
    ("levels", "Five levels", "From six states to one number"),
    ("l1-machine", "Level 1", "The machine, and the one way it could halt"),
    ("l2-sweep", "Level 1 to level 2", "Crossing a stretch in one move"),
    ("l3-round", "Level 2 to level 3", "One round trip, for any size"),
    ("l3-regimes", "Level 3", "62 templates in four cycles"),
    ("l4-epoch", "Level 3 to level 4", "When the countdown runs out: from one epoch to the next"),
    ("l4-setup", "Into level 4", "Before the first template: the setup"),
    ("l5-potential", "Level 4 to level 5", "Why there is always enough room"),
    ("bottom", "The bottom line", "It never halts"),
]
KEEP = ["shape", "related-machines"]     # sections written by holdouts/gen.py and holdouts/related.py


def lean_list(src, name):
    m = re.search(r"def %s : List Nat := \[([^\]]*)\]" % name, src)
    return [int(x) for x in m.group(1).split(",")]


def data():
    cd = json.load(open(os.path.join(HERE, "cert_data.json")))
    tables = open(os.path.join(DIR, "lean", "Tables.lean")).read()
    tpl = []
    for R in ["R0", "R1", "R2", "R3"]:
        for i, d in enumerate(cd["phases"][R]):
            tpl.append({"name": "%s_%d" % (R, i), "reg": R, "i": i, "sep": d["sep"], "beta": d["B"] % 3 + 6,
                        "rest": d["rest"], "A": d["A"], "B": d["B"]})
    out = {"machine": "1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC", "tpl": tpl,
           "dA": {R: cd["phases"][R + "_dA"] for R in ["R0", "R1", "R2", "R3"]},
           "dB": {R: cd["phases"][R + "_dB"] for R in ["R0", "R1", "R2", "R3"]}}
    for n in ["nxt", "dj", "potL", "endT", "endC1", "endC2"]:
        out[n] = lean_list(tables, n)
    assert all(len(out[n]) == len(tpl) for n in ["nxt", "dj", "potL", "endT", "endC1", "endC2"])
    return out


def main():
    lib = open(os.path.join(DIR, "page", "lib.js")).read().strip()
    secs = []
    for sid, eyebrow, heading in SECTIONS:
        body = open(os.path.join(DIR, "page", sid + ".html")).read().rstrip("\n")
        if sid == "levels":
            body = body.replace("__LIB__", lib).replace("__DATA__", json.dumps(data(), separators=(",", ":")))
        secs.append({"id": sid, "eyebrow": eyebrow, "heading": heading, "html": body.split("\n")})
    p = os.path.join(DIR, "status.json")
    spec = json.load(open(p))
    old = {s["id"]: s for s in spec["explainer"].get("sections", [])}
    spec["explainer"]["sections"] = secs + [old[k] for k in KEEP if k in old]
    with open(p, "w") as f:
        json.dump(spec, f, indent=1, ensure_ascii=False)
    print("wrote %d sections" % len(secs))


if __name__ == "__main__":
    main()
