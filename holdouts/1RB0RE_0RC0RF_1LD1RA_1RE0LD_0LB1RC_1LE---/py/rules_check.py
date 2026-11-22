"""The hybrid run of `model.py run`, with every directly simulated sub-round checked against the Lean rules.

`model.py run` takes regular sub-rounds by arithmetic and gives the rest to the machine (c/trans.c).  This runs the
same thing with c/rules_check.c in place of c/trans.c: at each sub-round the machine simulates, it decides from the
cells near the head which rule of lean/Subround.lean applies (glong, gshort, gzero, single, singleone) and checks that the
next sub-round comes exactly that rule's number of steps later; where no rule applies it records the sub-round.
So it measures what the Lean rules leave uncovered in the transients after the rebuilds.

usage: python3 py/rules_check.py K [LOG]     K rebuilds (243 take about 8 minutes); LOG gets the uncovered sub-rounds
"""
import collections, os, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model  # noqa: E402

BIN = os.path.join(tempfile.mkdtemp(), "rules_check")
subprocess.run(["gcc", "-O2", "-o", BIN, os.path.join(model.HERE, "..", "c", "rules_check.c")], check=True)
TOT = collections.Counter()
LOG = None


def trans(I, l, gaps, R=40, maxsteps=10 ** 11):
    inp = " ".join(map(str, I + [l])) + "\n" + " ".join(map(str, gaps)) + "\n"
    r = subprocess.run([BIN, model.M, str(maxsteps), repr(float(R)), "3", "2", "4", "1", "0"], input=inp,
                       capture_output=True, text=True)
    for line in r.stderr.splitlines():
        if line.startswith("SUM"):
            for kv in line.split()[1:]:
                k, v = kv.split("="); TOT[k] += int(v)
        elif line.startswith("EXC"):
            TOT["exc " + line.split()[1]] += 1
            if LOG: LOG.write(line + "\n")
        elif line.startswith("BAD"):
            TOT["bad"] += 1; print(line)
    out = r.stdout.split("\n"); h = out[0].split()
    if h[0] not in ("reg", "part"): return h[0], int(h[1]), None, None, None
    a, b, c = out[1].split("|")
    return h[0], int(h[1]), [int(x) for x in a.split()], int(b), [int(x) for x in c.split()]


if __name__ == "__main__":
    K = int(sys.argv[1])
    if len(sys.argv) > 2: LOG = open(sys.argv[2], "w")
    model.trans = trans
    st, nreb, subs, dsteps = model.run(*model.START, K, verbose=False)
    print(f"{st}: {nreb} rebuilds, {dsteps} steps simulated directly")
    print(f"directly simulated sub-rounds: {TOT['moments']}; covered by a Lean rule with the exact step count: "
          f"{TOT['moments'] - TOT['exc']}; uncovered: {TOT['exc']} "
          f"({', '.join(f'{k[4:]} {v}' for k, v in sorted(TOT.items()) if k.startswith('exc '))}); "
          f"rule predictions wrong: {TOT['bad']}")
    sys.exit(1 if TOT["bad"] else 0)
