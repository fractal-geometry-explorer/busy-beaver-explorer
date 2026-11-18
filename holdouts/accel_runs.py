"""Record long accelerated runs in the machines' status.json files.

usage: python3 holdouts/accel_runs.py            apply holdouts/accel_runs.json to every machine it lists
       python3 holdouts/accel_runs.py --check    exit 1 if some status.json is not what applying would give

holdouts/accel_runs.json lists runs made with the generic accelerators (tools/py/bbtools/rleaccel.py and its C++
port tools/c/rleaccel.cpp, both run-length coded block macro machines whose cycle jumps are used only after a
symbolic proof of the one-cycle rule; and the F07 rope simulator rsim). For each one this adds (or replaces) one
claim "No halt in the first ... steps (accelerated run, ...)", one fact on the explainer, and one closing sentence of
the index summary. A machine's file is marked "generated": false, since it is no longer what gen.py writes.
"""
import json
import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TAG = "accelerated run"          # every title this script writes ends with "(accelerated run, ...)"
SUMMARY_RE = re.compile(r" ?Accelerated run: no halt in \S+ steps\.$")

TOOLS = {
    "rleaccel.py": ("<code>tools/py/bbtools/rleaccel.py</code>", "python3 tools/py/bbtools/rleaccel.py {m} {K} {macro}"),
    "rleaccel.cpp": ("<code>tools/c/rleaccel.cpp</code>", "g++ -O2 -o rleaccel tools/c/rleaccel.cpp && ./rleaccel {m} {K} {macro}"),
    "rleaccel_rec.py": ("<code>tools/py/bbtools/rleaccel_rec.py</code>", "python3 tools/py/bbtools/rleaccel_rec.py {m} {K} --macro {macro}"),
    "Quick_Sim": ("Shawn Ligocki's <code>Quick_Sim.py</code> (github.com/sligocki/busy-beaver, commit cc35611)",
                  "python3 Code/Quick_Sim.py -r --max-loops={macro} {m}"),
}
QS_TEXT = ("{tool} with recursive rules (<code>-r</code>: a macro machine with a block size it picks itself and a back "
           "symbol, rules proved symbolically from repeated tape shapes, and rules whose proofs use earlier rules) runs "
           "{macro:,} loops from blank tape without a halt, in {seconds:,} seconds of a 2-minute screen. That is more than "
           "{depth} machine steps. It is an outside program, run here without changes; it reported no rule that "
           "repeats forever, so it does not decide the machine.")
REC_TEXT = ("The run-length simulator {tool} (blocks of {K} cells, runs crossed in one step, cycle jumps used only after "
            "a symbolic proof of the one-cycle rule, and proofs that may themselves apply earlier rules to symbolic "
            "lengths, with exact polynomial step counts; tested cell for cell against direct runs) runs {macro:,} macro "
            "steps from blank tape without a halt, in {seconds:,} seconds. That is more than {depth} machine steps. "
            "It found no rule that repeats forever, so it does not decide the machine.")


def sci_html(log10):
    """10^log10 as 'a.bc&middot;10<sup>n</sup>' (rounded down, so the claim stays true)"""
    n = math.floor(log10)
    a = math.floor(10 ** (log10 - n) * 100) / 100
    if a >= 10:
        a, n = 1.0, n + 1
    sup = f"{n:,}"
    return f"{a:.2f}&middot;10<sup>{sup}</sup>" if a != 1 else f"10<sup>{sup}</sup>"


def sci_text(log10):
    n = math.floor(log10)
    a = math.floor(10 ** (log10 - n) * 100) / 100
    return f"{a:.2f}e{n}"


def claim_for(r):
    m, K, macro = r["machine"], r["K"], r["macro"]
    tool, cmd = TOOLS[r["tool"]]
    depth = sci_html(r["log10"])
    if r["tool"] == "Quick_Sim":
        text = QS_TEXT.format(tool=tool, macro=macro, seconds=r["seconds"], depth=depth)
    elif r["tool"] == "rleaccel_rec.py":
        text = REC_TEXT.format(tool=tool, K=K, macro=macro, seconds=r["seconds"], depth=depth)
    else:
        text = (f"The run-length simulator {tool} (blocks of {K} cells, runs of a block crossed in one step, and cycle "
            f"jumps, each used only after its one-cycle rule has been proved symbolically for all lengths above the "
            f"minimums it needs; tested cell for cell against direct runs) runs {macro:,} macro steps from blank tape "
            f"without a halt, in {r['seconds']:,} seconds. That is more than {depth} machine steps. "
            f"It found no rule that repeats forever, so it does not decide the machine.")
    what = "Quick_Sim" if r["tool"] == "Quick_Sim" else f"blocks of {K}"
    return {"level": "trusted", "title": f"No halt in the first {depth} steps ({TAG}, {what})", "text": text,
            "where": "<code>" + cmd.format(m=m, K=K, macro=macro) + "</code>"}


def apply(spec, r):
    claims = [c for c in spec["claims"] if f"({TAG}" not in c.get("title", "")]
    new = claim_for(r)
    # after the last trusted "No halt in ..." claim, else before the first heuristic/open one
    at = None
    for i, c in enumerate(claims):
        if c.get("title", "").startswith("No halt in") and c.get("level") in ("kernel", "native", "trusted"):
            at = i + 1
    if at is None:
        at = next((i for i, c in enumerate(claims) if c.get("level") in ("heuristic", "open")), len(claims))
    claims.insert(at, new)
    spec["claims"] = claims
    ex = spec.get("explainer")
    if isinstance(ex, dict) and isinstance(ex.get("facts"), list):
        facts = [f for f in ex["facts"] if not f.get("text", "").startswith(("No halt in the run-length accelerator", "No halt in an accelerated run"))]
        facts.insert(0, {"level": "trusted", "value": sci_html(r["log10"]) + " steps",
                         "text": ("No halt in an accelerated run (Quick_Sim, an outside program)." if r["tool"] == "Quick_Sim"
                                  else f"No halt in the run-length accelerator (proved cycle jumps, blocks of {r['K']}).")})
        ex["facts"] = facts
    s = SUMMARY_RE.sub("", spec.get("summary", "")).rstrip()
    spec["summary"] = (s + " " if s else "") + f"Accelerated run: no halt in {sci_text(r['log10'])} steps."
    spec["generated"] = False
    return spec


def main(check=False):
    with open(os.path.join(HERE, "accel_runs.json")) as f:
        runs = json.load(f)["runs"]
    stale = []
    for r in runs:
        p = os.path.join(HERE, r["machine"], "status.json")
        with open(p) as f:
            old = f.read()
        spec = apply(json.loads(old), r)
        new = json.dumps(spec, indent=1, ensure_ascii=False) + "\n"
        if new != old:
            stale.append(r["machine"])
            if not check:
                with open(p, "w") as f:
                    f.write(new)
    if check and stale:
        print("not current:", *stale)
        return 1
    print(len(runs), "runs,", len(stale), "files", "stale" if check else "written")
    return 0


if __name__ == "__main__":
    sys.exit(main("--check" in sys.argv))
