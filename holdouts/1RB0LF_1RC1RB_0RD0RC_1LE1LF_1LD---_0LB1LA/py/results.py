"""Writes results/phases.tsv and results/summary.json from the --log file of py/phasemap.py.
usage: python3 py/results.py phases.log"""
import json
import math
import os
import sys

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def log10(x):
    return math.log10(x) if x < 10 ** 300 else (x.bit_length() - 60) * math.log10(2) + math.log10(x >> (x.bit_length() - 60))


def main():
    rows = [json.loads(l) for l in open(sys.argv[1]) if l.startswith('{"n"')]
    os.makedirs(os.path.join(D, "results"), exist_ok=True)
    with open(os.path.join(D, "results/phases.tsv"), "w") as f:
        f.write("# 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA, py/phasemap.py from blank tape: one line per phase start\n"
                "# n: phase; c = K_n - 2 K_(n-1); len: cells of the counter word w; log10_t: step; K_bits: bits of K\n"
                "n\tc\tlen\tlog10_t\tK_bits\n")
        for r in rows:
            f.write(f"{r['n']}\t{r['c']}\t{r['len']}\t{log10(r['t']):.4f}\t{r['K'].bit_length()}\n")
    last = rows[-1]
    lt = log10(last["t"])
    e = math.floor(lt)
    sm = {"phases": last["n"], "log10_t": e, "t_text": f"{10 ** (lt - e):.2f}&middot;10<sup>{e}</sup>",
          "events": [r["n"] for r in rows if r["c"] != 2 and r["n"] > 1], "len": last["len"],
          "K_bits": last["K"].bit_length()}
    json.dump(sm, open(os.path.join(D, "results/summary.json"), "w"), indent=1)
    print(sm)


if __name__ == "__main__":
    main()
