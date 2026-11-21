#!/usr/bin/env python3
"""Build pages/holdouts/collatz-family.html and tools/collatz/TRIAGE.md from triage.json, hunts.json and maps.js.

usage: python3 tools/collatz/build.py [--check]     (--check: exit 1 if either output is not current)
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
PAGE = os.path.join(REPO, "pages", "holdouts", "collatz-family.html")
MD = os.path.join(HERE, "TRIAGE.md")

BUCKETS = [
    ("hunt", "Halt hunt", "The map is fixed (proved, or checked against the machine) and a halt, if there is one, might "
     "come early enough to compute. Run it far."),
    ("external", "Outside proof", "A busycoq pull request claims a decision. Compile it."),
    ("prove-map", "Prove the map", "The map is explicit but not yet a Lean halts-iff. Proof engineering would make the "
     "question exactly a question about the map."),
    ("decode", "Decode", "The round or phase map is not closed yet and has to be read off the machine first."),
    ("number-theory", "Number theory", "Lean already reduces halting to the map. What is left is a Collatz-type question "
     "about one orbit, beyond current methods; only a lucky halt hunt could change that."),
]


def load(name):
    with open(os.path.join(HERE, name)) as f:
        return json.load(f)


def page(data, hunts):
    with open(os.path.join(HERE, "page_head.html")) as f:
        head = f.read()
    with open(os.path.join(HERE, "page_body.html")) as f:
        body = f.read()
    with open(os.path.join(HERE, "maps.js")) as f:
        maps = f.read()
    js = lambda x: json.dumps(x, ensure_ascii=False).replace("</", "<\\/")
    body = body.replace("__DATA__", js(data)).replace("__HUNTS__", js(hunts)).replace("__MAPS__", maps)
    return head + body


def md(data, hunts):
    out = ["# Triage of the Collatz-like holdouts (family R15)", "",
           "The 98 machines of family R15 in [`holdouts/FAMILIES.md`](../../holdouts/FAMILIES.md): runs that are, "
           "provably or apparently, the orbit of an explicit Collatz-like map. Each is sorted by its most useful next "
           "step. The records are read from each machine's `status.json` and `README.md` (`triage.json`); the sort is a "
           "judgement, not a result. Interactive version, with a map runner: "
           "[`pages/holdouts/collatz-family.html`](../../pages/holdouts/collatz-family.html). "
           "Written by `build.py`; edit `triage.json` or `hunts.json` and rebuild.", ""]
    out += ["| bucket | machines | meaning |", "|---|---|---|"]
    for b, name, text in BUCKETS:
        out.append(f"| {name} | {sum(1 for x in data if x['bucket'] == b)} | {text} |")
    out += ["", "## Halt hunts run for this triage", "",
            "| machine | what was run | before | now |", "|---|---|---|---|"]
    for h in hunts:
        out.append(f"| `{h['m']}` | {h['what']} | {h['before']} | {h['now']} |")
    for b, name, text in BUCKETS:
        rows = [x for x in data if x["bucket"] == b]
        out += ["", f"## {name} ({len(rows)})", "", text, ""]
        for x in rows:
            out.append(f"### [`{x['m']}`](../../holdouts/{x['m']}/README.md)")
            out.append("")
            out.append(f"*{x['tier']}, outlook {x['outlook']}" + (f", table set {x['set']}" if x.get("set") not in (None, "", "-") else "") + "*")
            out.append("")
            for k, label in (("map", "Map"), ("halt", "Halts when"), ("start", "From blank tape"), ("proved", "Proved"),
                             ("checked", "Checked"), ("odds", "Odds"), ("next", "Next step")):
                if x.get(k):
                    out.append(f"- **{label}:** {x[k]}")
            out.append("")
    return "\n".join(out).rstrip() + "\n"


def main():
    data, hunts = load("triage.json"), load("hunts.json")
    outs = {PAGE: page(data, hunts), MD: md(data, hunts)}
    if "--check" in sys.argv:
        bad = [p for p, s in outs.items() if not os.path.exists(p) or open(p).read() != s]
        for p in bad:
            print("not current:", os.path.relpath(p, REPO))
        sys.exit(1 if bad else 0)
    for p, s in outs.items():
        with open(p, "w") as f:
            f.write(s)
        print("wrote", os.path.relpath(p, REPO))


if __name__ == "__main__":
    main()
