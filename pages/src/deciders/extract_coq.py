"""Extract the hardcoded machines and certificates of Coq-BB5 into JSON for the deciders page.

Usage: python3 extract_coq.py PATH/TO/Coq-BB5 > data/coq_hardcoded.json

Reads CoqBB5/BB5/BB5_Deciders_Hardcoded_Parameters/*.v and converts each `makeTM A0 A1 ... E1` to the standard text
format (`BR0` = go to B, move right, write 0 becomes `0RB`; `HR1` and friends, the halting transitions, become `---`).
"""
import json
import os
import re
import subprocess
import sys

TRANS = re.compile(r"\b([A-EH])([LR])([01])\b")


def tm_text(args):
    out = []
    for a in args:
        m = TRANS.fullmatch(a)
        if not m:
            raise ValueError(a)
        st, d, w = m.groups()
        out.append("---" if st == "H" else w + d + st)
    return "_".join(out[i] + out[i + 1] for i in range(0, 10, 2))


def entries(text):
    """Yield (machine, decider-text) for each `(makeTM ...,DECIDER)::` item of a list."""
    for chunk in text.split("(makeTM")[1:]:
        body = chunk[:chunk.rindex(")::")]
        args, _, decider = body.partition(",")
        yield tm_text(args.split()), " ".join(decider.split())


def pairs(s):
    return [[int(a), int(b)] for a, b in re.findall(r"\((\d+),(\d+)\)", s)]


def wpairs(s):
    return [[int(a), int(b), int(c), int(d)] for a, b, c, d in
            re.findall(r"\((\d+),(-?\d+);(\d+),(-?\d+)\)", s)]


def main(root):
    d = os.path.join(root, "CoqBB5", "BB5", "BB5_Deciders_Hardcoded_Parameters")
    read = lambda f: open(os.path.join(d, f)).read()
    out = {}
    commit = subprocess.run(["git", "-C", root, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    out["source"] = {"repo": "https://github.com/ccz181078/Coq-BB5", "commit": commit,
                     "dir": "CoqBB5/BB5/BB5_Deciders_Hardcoded_Parameters"}
    out["halt"] = [tm for tm, p in entries(read("Decider_Halt_Hardcoded_Parameters.v")) if p.strip() == "Ha"]
    out["loop"] = [tm for tm, p in entries(read("Decider_Loop_Hardcoded_Parameters.v")) if p.strip() == "Lp1"]
    ng = []
    for tm, p in entries(read("Decider_NGramCPS_Hardcoded_Parameters.v")):
        m = re.fullmatch(r"NG (\d+) (\d+)", p.strip())
        if m:
            ng.append([tm, "hist", int(m.group(1)), int(m.group(2))])
            continue
        m = re.fullmatch(r"NG_LRU (\d+)", p.strip())
        if not m:
            raise ValueError(p)
        ng.append([tm, "lru", 0, int(m.group(1))])
    out["ngram"] = ng
    rwl = []
    for tm, p in entries(read("Decider_RepWL_Hardcoded_Parameters.v")):
        m = re.fullmatch(r"RWL (\d+) (\d+)", p.strip())
        if not m:
            raise ValueError(p)
        rwl.append([tm, int(m.group(1)), int(m.group(2))])
    out["repwl"] = rwl
    far = []
    for tm, p in entries(read("Verifier_FAR_Hardcoded_Certificates.v")):
        m = re.fullmatch(r"DNV (\d+) \(DFA_from_list \((.*)\)\)", p.strip(), re.S)
        if not m:
            raise ValueError(p)
        far.append([tm, int(m.group(1)), pairs(m.group(2))])
    out["far"] = far
    wfar = []
    for tm, p in entries(read("Verifier_WFAR_Hardcoded_Certificates.v")):
        m = re.fullmatch(r"WA (-?\d+)\s+(\d+) \(WDFA_from_list \((.*?)\)\)\s+(\d+) \(WDFA_from_list \((.*?)\)\)",
                         p.strip(), re.S)
        if not m:
            raise ValueError(p)
        wfar.append([tm, int(m.group(1)), int(m.group(2)), wpairs(m.group(3)), int(m.group(4)), wpairs(m.group(5))])
    out["wfar"] = wfar
    counts = {k: len(v) for k, v in out.items() if isinstance(v, list)}
    sys.stderr.write(json.dumps(counts) + "\n")
    json.dump(out, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main(sys.argv[1])
