"""Collect the triage runs into holdouts/triage.json.

usage: python3 holdouts/make_triage.py HOLDOUT_LIST DIR_OF_JSON

HOLDOUT_LIST is bbchallenge's list ("id machine" per line, BB6_holdouts_608.txt); DIR_OF_JSON holds the output of
tools/c/triage.c for each machine, as MACHINE.json:

  awk '{print $2}' BB6_holdouts_608.txt | xargs -P 4 -I{} sh -c './triage {} 1000000000 400 > tri/{}.json'
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "tools", "py"))

from bbtools.triage import features  # noqa: E402


def main(lst, d):
    out = []
    for line in open(lst):
        if not line.strip():
            continue
        i, m = line.split()
        with open(os.path.join(d, m + ".json")) as f:
            raw = json.loads(f.read())
        r = {"id": int(i)}
        r.update(features(raw))
        r["cp"] = raw["cp"]
        out.append(r)
    with open(os.path.join(HERE, "triage.json"), "w") as f:
        f.write("[\n" + ",\n".join(json.dumps(r, separators=(",", ":")) for r in out) + "\n]\n")
    print(len(out), "machines")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
