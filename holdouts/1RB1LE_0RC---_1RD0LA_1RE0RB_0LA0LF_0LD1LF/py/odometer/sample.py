"""Thin out the far run's visits for the explainer page and the README.

    python3 sample.py VISITS.jsonl [OUT]     (OUT default: ../../data/odometer/visits_sample.json)

Keeps the visits near a run-out of the first block and about 100 more, evenly spread.  Each kept visit:
[visit number, step (leading digits and number of digits), arrival state, number of walls, left end glyph,
 blocks, walls] for the first 60 blocks: a block is its exact length below 10^6 and otherwise the text 'eD' (a number
 of D+1 decimal digits); a wall is the number r of walls 1010 merged into it ((1010)^r at a visit), 0 if it is
 another glyph."""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
src = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, '..', '..', 'data', 'odometer', 'visits_sample.json')
V = [json.loads(l) for l in open(src)]
def n1(v):
    t = v[3]
    if len(t) < 2: return 0
    x = t[1]
    return x if isinstance(x, int) else 10**int(x[1:])
runs = [i for i in range(1, len(V)) if n1(V[i]) > n1(V[i - 1]) + 10]
keep = set(range(0, len(V), max(1, len(V) // 100))) | {len(V) - 1}
for i in runs:
    keep |= set(range(max(0, i - 3), min(len(V), i + 8)))
def wall(g):
    return len(g) // 4 if g and g == '1010' * (len(g) // 4) else 0
def comp(i):
    st, s, k, t = V[i]
    return [i + 1, st[:4], len(st), s, k, t[0], t[1:121:2], [wall(g) for g in t[2:121:2]]]
ev = [comp(i) for i in sorted(keep)]
json.dump({'total': len(V), 'runouts': [[i + 1, len(V[i][0])] for i in runs], 'visits': ev},
          open(out, 'w'), separators=(',', ':'))
print(len(V), 'visits,', len(ev), 'kept, run-outs of the first block at visits', [i + 1 for i in runs])
