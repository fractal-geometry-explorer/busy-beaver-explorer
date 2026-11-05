"""Run NGramCPS (tools/c/ngramcps.c) on the holdout from blank tape over a grid of window widths and augmentations.

usage: python3 run.py OUTDIR [plain|history|lru|asym|all] [-s STEPS] [-m MAXCONF] [-t SECONDS]

plain, lru: equal widths 1, 2, ... until a run hits a limit; history: lengths 1 to 3 the same way, lengths 4 to 8
at widths 1 to 16; asym: every NL != NR with 1 <= NL, NR <= 16.

Writes OUTDIR/results.tsv (one line per run: augmentation, history length, widths, result, set sizes, time, memory,
derivation length, first unreal step) and OUTDIR/deriv/*.txt (the derivation of each halt, with every configuration
marked real or not against a direct run of STEPS steps).  Widths are raised until a run hits MAXCONF configurations
or SECONDS seconds; a run that hits the limit is recorded as LIMIT.
"""
import os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "..", "tools", "c", "ngramcps.c")
MACHINE = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
COLS = ["aug", "hist", "nl", "nr", "result", "configs", "processed", "left_grams", "right_grams", "symbols",
        "seconds", "maxrss_mb", "derivation_length", "first_unreal_step"]


def build(out):
    exe = os.path.join(out, "ngramcps")
    subprocess.run(["gcc", "-O2", "-o", exe, SRC], check=True)
    return exe


def run(exe, out, nl, nr, aug, hist, steps, maxconf, tmax):
    tag = f"{aug}{hist if aug == 'history' else ''}_{nl}_{nr}"
    cmd = [exe, MACHINE, str(nl), str(nr), "-m", str(maxconf), "-s", str(steps),
           "-w", os.path.join(out, "deriv", tag + ".txt")]
    if aug == "history":
        cmd += ["-H", str(hist)]
    if aug == "lru":
        cmd += ["-U"]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=tmax)
        d = dict(l.split(" ", 1) for l in p.stdout.splitlines() if " " in l)
        if p.returncode:
            d["result"] = "ERROR(" + p.stderr.strip().replace(" ", "_") + ")"
    except subprocess.TimeoutExpired:
        d = {"result": "TIMEOUT", "seconds": f"{time.time() - t0:.1f}"}
    d.update(aug=aug, hist=str(hist), nl=str(nl), nr=str(nr))
    line = "\t".join(d.get(c, "") for c in COLS)
    with open(os.path.join(out, "results.tsv"), "a") as f:
        f.write(line + "\n")
    print(line, flush=True)
    return d


def sweep(exe, out, aug, hist, steps, maxconf, tmax, widths):
    for nl, nr in widths:
        d = run(exe, out, nl, nr, aug, hist, steps, maxconf, tmax)
        if d["result"] not in ("UNKNOWN", "NONHALT"):
            break


def main():
    out = sys.argv[1]
    what = sys.argv[2] if len(sys.argv) > 2 else "all"
    args = sys.argv[3:]
    opt = {"-s": 100_000_000, "-m": 200_000_000, "-t": 1800}
    for i in range(0, len(args), 2):
        opt[args[i]] = int(args[i + 1])
    os.makedirs(os.path.join(out, "deriv"), exist_ok=True)
    if not os.path.exists(os.path.join(out, "results.tsv")):
        with open(os.path.join(out, "results.tsv"), "w") as f:
            f.write("\t".join(COLS) + "\n")
    exe = build(out)
    s, m, t = opt["-s"], opt["-m"], opt["-t"]
    sym = [(n, n) for n in range(1, 191)]
    if what in ("plain", "all"):
        sweep(exe, out, "none", 0, s, m, t, sym)
    if what in ("asym", "all"):
        for nl in range(1, 17):
            for nr in range(1, 17):
                if nl != nr:
                    run(exe, out, nl, nr, "none", 0, s, m, t)
    if what in ("history", "all"):
        for h in range(1, 4):
            sweep(exe, out, "history", h, s, m, t, sym)
        for h in range(4, 9):
            sweep(exe, out, "history", h, s, m, t, sym[:16])
    if what in ("lru", "all"):
        sweep(exe, out, "lru", 0, s, m, t, sym)


if __name__ == "__main__":
    main()
