"""Data for the explainer's phase viewer: the counter word w at the start of phases 1..N as run lengths (hex).
usage: python3 py/page_data.py N > /tmp/phases.json   (then py/build_page.py puts it in status.json)"""
import itertools
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import phasemap  # noqa: E402


def runs(w):
    return [len(list(g)) for _, g in itertools.groupby(w)]


def main():
    N = int(sys.argv[1])
    out = []
    for n, t, K, Z, w, c in phasemap.phases():
        # w starts with a 1; runs alternate 1s, 0s, 1s, ..., in hex, joined by '.'
        out.append({"n": n, "lt": round(math.log10(t), 4), "c": c,
                    "w": ".".join(format(r, "x") for r in runs(w))})
        if n >= N:
            break
    json.dump(out, sys.stdout, separators=(",", ":"))


if __name__ == "__main__":
    main()
