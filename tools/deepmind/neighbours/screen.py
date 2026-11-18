#!/usr/bin/env python3
"""Holdouts one transition away from a table DeepMind proved never halts.

usage: python3 tools/deepmind/neighbours/screen.py BB6_holdouts_608.txt tools/deepmind/neighbours/nonhalt_tables.txt OUT.json

nonhalt_tables.txt has one line per (table, source): the table in bbchallenge notation, then where the proof is
(`lean:<path in google-deepmind/cryptids, commit 3647718>` or `rocqPR:<busycoq pull request>`).  A holdout matches a
table when some renaming of its states, possibly with left and right exchanged, gives a table that differs from the
DeepMind one in at most one transition.  The renaming may send the holdout's start state A to any state, so a match
can be "the DeepMind table with one transition changed, started in another state".  OUT.json lists every match.
"""
import collections
import itertools
import json
import sys


def transform(m, perm, flip):
    rows = m.split('_')
    new = [None] * 6
    for q in range(6):
        row = ""
        for b in range(2):
            t = rows[q][3 * b:3 * b + 3]
            if t[0] == '-':
                row += "---"
                continue
            d = t[1]
            if flip:
                d = 'L' if d == 'R' else 'R'
            row += t[0] + d + "ABCDEF"[perm[ord(t[2]) - 65]]
        new[perm[q]] = row
    return "_".join(new)


def slots(m):
    return [r[3 * b:3 * b + 3] for r in m.split('_') for b in (0, 1)]


def main(hfile, dfile, out):
    H = [l.split()[-1] for l in open(hfile) if l.strip() and len(l.split()[-1]) == 41]
    D = collections.defaultdict(set)
    for l in open(dfile):
        m, src = l.split()
        D[m.replace('HHH', '---')].add(src)
    idx = collections.defaultdict(list)
    for d in D:
        s = slots(d)
        for i in range(12):
            idx[tuple(s[:i] + ['*'] + s[i + 1:])].append(d)
    res = []
    for h in H:
        seen = set()
        for perm in itertools.permutations(range(6)):
            for flip in (0, 1):
                t = transform(h, perm, flip)
                s = slots(t)
                for i in range(12):
                    for d in idx.get(tuple(s[:i] + ['*'] + s[i + 1:]), []):
                        if (d, t) in seen:
                            continue
                        seen.add((d, t))
                        sd = slots(d)
                        diff = [x for x in range(12) if sd[x] != s[x]]
                        res.append({"holdout": h, "frame": t, "start": "ABCDEF"[perm[0]], "mirror": bool(flip),
                                    "deepmind": d, "sources": sorted(D[d]),
                                    "changed": [{"slot": "ABCDEF"[x // 2] + str(x % 2), "deepmind": sd[x],
                                                 "holdout": s[x]} for x in diff]})
    json.dump(res, open(out, 'w'), indent=1)
    print(len(res), "matches;", len({r["holdout"] for r in res if r["changed"]}), "holdouts one transition away")


if __name__ == "__main__":
    main(*sys.argv[1:4])
