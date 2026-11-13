"""Write the step-by-step proof walkthrough into status.json (explainer.sections), from proof_page.html.

The walkthrough is hand-written HTML with one script; this file only splits it into sections at the
`<!--SECTION id | eyebrow | heading-->` markers and puts the certificate's tables (py/cert_data.json and the
lists of lean/Tables.lean) into it as JSON, so the page shows exactly the numbers Lean checks.

usage: python3 holdouts/1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC/py/proof_page.py
       then python3 holdouts/build_pages.py 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DIR = os.path.dirname(HERE)
KEEP = ["shape"]          # generated sections kept after the walkthrough


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
           "dB": {R: cd["phases"][R + "_dB"] for R in ["R0", "R1", "R2", "R3"]},
           "moves": [cd["ends"][str(t)][0] for t in range(len(tpl))]}
    for n in ["nxt", "dj", "potL", "endT", "endC1", "endC2"]:
        out[n] = lean_list(tables, n)
    assert all(len(out[n]) == len(tpl) for n in ["nxt", "dj", "potL", "endT", "endC1", "endC2"])
    return out


def main():
    src = open(os.path.join(HERE, "proof_page.html")).read()
    src = src.replace("__DATA__", json.dumps(data(), separators=(",", ":")))
    parts = re.split(r"<!--SECTION (.*?)-->\n", src)
    secs = []
    for head, body in zip(parts[1::2], parts[2::2]):
        sid, eyebrow, heading = [x.strip() for x in head.split("|")]
        secs.append({"id": sid, "eyebrow": eyebrow, "heading": heading, "html": body.rstrip("\n").split("\n")})
    p = os.path.join(DIR, "status.json")
    spec = json.load(open(p))
    old = {s["id"]: s for s in spec["explainer"].get("sections", [])}
    spec["explainer"]["sections"] = secs + [old[k] for k in KEEP if k in old]
    with open(p, "w") as f:
        json.dump(spec, f, indent=1, ensure_ascii=False)
    print("wrote %d sections" % len(secs))


if __name__ == "__main__":
    main()
