"""Fold the logs of c/abfast.c into this folder: c/abfast_log.txt, the progress table of README.md and the
long-run claim of status.json.

usage: python3 abfast_report.py LOG [LOG ...] [--section SECTION.html]
LOGs are abfast outputs (one run, possibly restarted from its prog lines); lines are merged by visit index.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.dirname(HERE)


def sci(n):
    """10^k or m·10^k, as HTML and as plain text."""
    e = len(str(n)) - 1
    m = n / 10 ** e
    ms = ("%g" % m)
    if ms == "1":
        return "10<sup>%d</sup>" % e, "10^%d" % e
    return "%s&middot;10<sup>%d</sup>" % (ms, e), "%s*10^%d" % (ms, e)


def main():
    args = sys.argv[1:]
    section = None
    if "--section" in args:
        k = args.index("--section")
        section = open(args[k + 1]).read()
        del args[k:k + 2]
    near, reset, prog = {}, {}, {}
    halt = None
    for p in args:
        for ln in open(p):
            m = re.match(r"(near|reset|prog) i=(\d+) (.*)", ln.strip())
            if ln.startswith("HALT"):
                halt = ln.strip()
            if not m:
                continue
            kind, i, rest = m.group(1), int(m.group(2)), m.group(3)
            if kind == "prog":
                rest = re.sub(r" fast=.*", "", rest)
                prog[i] = rest
            else:
                (near if kind == "near" else reset)[i] = rest
    top = max(prog)
    with open(os.path.join(M, "c", "abfast_log.txt"), "w") as f:
        f.write("# c/abfast.c from A(2, 9): every near visit (1 <= b - a <= 8), every reset, the state every 10^12 visits.\n")
        f.write("# Visits 0 to %d, no halt.\n" % top if not halt else "# " + halt + "\n")
        ev = [(i, "near", r) for i, r in near.items()] + [(i, "reset", r) for i, r in reset.items()] + \
             [(i, "prog", r) for i, r in prog.items() if i % 10 ** 12 == 0 or i == top]
        for i, k, r in sorted(ev, key=lambda x: (x[0], x[1] != "near")):
            f.write("%s i=%d %s\n" % (k, i, r))
    # milestones: 10^12, 3*10^12, 10^13, ..., and the latest
    ms = []
    e = 12
    while True:
        for c in (1, 3):
            n = c * 10 ** e
            if n <= top and n in prog:
                ms.append(n)
        if 10 ** e > top:
            break
        e += 1
    if top not in ms:
        ms.append(top)
    rows = []
    for n in ms:
        a, b = re.match(r"a=(\d+) b=(\d+)", prog[n]).groups()
        nn = sum(1 for i in near if i < n)
        rows.append("| %s | A(%s, %s) | %d | %.1e |" % (sci(n)[1], a, b, nn, 0.6806 * n ** 3))
    rd = open(os.path.join(M, "README.md")).read()
    rd = re.sub(r"(<!-- abfast-progress -->\n\|[^\n]*\n\|[^\n]*\n)(.*?)(<!-- /abfast-progress -->)",
                lambda m: m.group(1) + "\n".join(rows) + "\n" + m.group(3), rd, flags=re.S)
    rd = rd.replace("| ROWS\n", "")
    if "\nROWS\n" in rd:
        rd = rd.replace("\nROWS\n", "\n" + "\n".join(rows) + "\n")
    nh, nt = sci(top)
    steps = 0.6806 * top ** 3
    se = int(("%e" % steps).split("e")[1])
    sm = steps / 10 ** se
    sh, st = "%.1f&middot;10<sup>%d</sup>" % (sm, se), "%.1f*10^%d" % (sm, se)
    rd = re.sub(r"C \(`c/abfast\.c`[^)]*\): not in the first [^ ]+ visits \(about [^ ]+ steps\)\. ", "", rd)
    rd = rd.replace("C (`c/abrun.c`): not in the first 3*10^12 visits",
                    "C (`c/abfast.c`, blocks proved sound by `block_ok` in `lean/Block.lean`): not in the first %s visits "
                    "(about %s steps). C (`c/abrun.c`): not in the first 3*10^12 visits" % (nt, st))
    open(os.path.join(M, "README.md"), "w").write(rd)

    js = json.load(open(os.path.join(M, "status.json")))
    title = "No halt in the first %s visits (about %s steps)" % (nh, sh)
    a, b = re.match(r"a=(\d+) b=(\d+)", prog[top]).groups()
    nn = sum(1 for i in near if i < top)
    claim = {
        "level": "trusted",
        "title": title,
        "text": ("<code>c/abfast.c</code> follows the rules from A(2, 9) up to 48 visits at a time: it reads the next grow/swap "
                 "digits off the binary expansion of b / (a + b), applies them formally and keeps the block only if both "
                 "coordinates end at least 16&middot;2<sup>K</sup>, which <code>block_ok</code> in <code>lean/Block.lean</code> "
                 "proves sound for any guessed digits (refused blocks are redone one visit at a time). %s visits without "
                 "b = 3, ending at A(%s, %s); %d near visits (1 &le; b &minus; a &le; 8), none with a even and b &minus; a = 4. "
                 "It reproduces <code>c/abrun.c</code>'s states and near visits at 10<sup>11</sup> and 3&middot;10<sup>12</sup> "
                 "visits. Steps by T &asymp; 0.68&nbsp;N<sup>3</sup>." % (nh, a, b, nn)),
        "where": "<code>gcc -O3 -march=native -o abfast c/abfast.c && ./abfast %d 100000000000</code> (about 1.7&middot;10<sup>9</sup> visits a second; resumable from any <code>prog</code> line of <code>c/abfast_log.txt</code>)" % top,
    }
    cl = [c for c in js["claims"] if "abfast" not in c.get("text", "")]
    k = next(i for i, c in enumerate(cl) if c["title"].startswith("No halt in the first 3&middot;10<sup>12</sup> visits"))
    cl.insert(k + 1, claim)
    js["claims"] = cl
    kern = {"level": "kernel", "title": "Blocks of visits are sound",
            "text": "<code>block_ok</code>: for any list of grow/swap digits, if their formal run from a visit A(a, b) ends with "
                    "both coordinates at least 16&middot;2<sup>K</sup>, the next K visits of the rules are that run; "
                    "<code>block_far</code>: none of them has 1 &le; b &minus; a &le; 27. No <code>native_decide</code>.",
            "where": "<code>lean/Block.lean</code>"}
    js["claims"] = [c for c in js["claims"] if c["title"] != kern["title"]]
    k = next(i for i, c in enumerate(js["claims"]) if c is claim)
    js["claims"].insert(k, kern)
    fa = js["explainer"]["facts"]
    fa[0] = {"level": "trusted", "value": "%s steps" % sh,
             "text": "No halt in the first %s visits of the wiki's rules (blocks of visits proved sound in Lean)." % nh}
    v = js["verdict"][2]
    v = re.sub(r"Iterated in C, the rules give no halt in the first [^.]*?visits \(about [^)]*\)\.",
               "Iterated in C, up to 48 visits at a time with a block check proved sound in Lean (<code>block_ok</code>), "
               "the rules give no halt in the first %s visits (about %s steps)." % (nh, sh), v)
    js["verdict"][2] = v
    js["summary"] = re.sub(r"no halt in [^ ]+ steps by the rules", "no halt in %s steps by the rules" % ("%.0e" % steps).replace("e+", "e"), js["summary"])
    if section is not None:
        secs = [s for s in js["explainer"]["sections"] if s.get("id") != "blocks"]
        k = next(i for i, s in enumerate(secs) if s.get("id") == "invariant")
        secs.insert(k + 1, {"id": "blocks", "eyebrow": "The long run", "heading": "Many visits at once",
                            "html": section.replace("PROGRESS", "%s visits, no halt, ending at A(%s, %s)" % (nh, a, b)).split("\n")})
        js["explainer"]["sections"] = secs
    with open(os.path.join(M, "status.json"), "w") as f:
        json.dump(js, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print("top", top, "near", nn, "milestones", ms)


if __name__ == "__main__":
    main()
