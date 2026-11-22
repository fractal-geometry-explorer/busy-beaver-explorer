"""Which pairs of neighbouring blocks make an F05 machine halt: scan two blocks of a real left-end list.

Take the list [6, t0, t1, ...] the machine's run has at its left-end event EVENT (fast.py), replace the two
neighbours at positions POS, POS+1 by (a, b) for even a < A and even b < B, and run the machine exactly from that
left-end configuration (fast.run_list) for at most 12 more left-end events.  Record which (a, b) halt.  Since a
round lowers block j by 18*5^j, a small a is a block about to run out; the drift b - 5a and the residue a mod 18
are the two numbers a round keeps (lean/Family.lean, `visit_conserves`), so the halting pairs, written as
(a mod 18, b - 5a), are the dangerous values of those conserved numbers.

usage: python3 f05_danger.py MACHINE EVENT POS A B [OUT.json] [PROCS=4]
"""
import collections
import json
import multiprocessing as mp
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fast  # noqa: E402
import frames  # noqa: E402

G = {}


def one(ab):
    a, b = ab
    L = list(G["base"])
    L[G["pos"]], L[G["pos"] + 1] = a, b
    h, out = fast.run_list(G["fa"], L, 1e60, events=12)
    return a, b, out


def scan(machine, event, pos, A, B, procs=4):
    fr, fa, st = frames.info(machine)
    h, r, s = fast.run(machine, 1e45)
    event = min(event, len(h.top) - 1)
    base = list(h.top[event][2])
    G.update(fa=fa, base=base, pos=pos)
    jobs = [(a, b) for a in range(0, A, 2) for b in range(0, B, 2)]
    t0 = time.time()
    with mp.Pool(procs) as p:
        res = p.map(one, jobs, chunksize=16)
    halts = [(a, b) for a, b, o in res if o == "halt"]
    other = collections.Counter(o for a, b, o in res)
    return {
        "machine": machine, "frame_a": fa, "event": event, "position": pos,
        "base_first_blocks": [str(x) for x in base[:6]], "blocks": len(base),
        "a_range": [0, A, 2], "b_range": [0, B, 2], "runs": len(res), "outcomes": dict(other),
        "halts": [{"a": a, "b": b, "drift": b - 5 * a, "a_mod_18": a % 18} for a, b in halts],
        "halting_classes": sorted({(a % 18, b - 5 * a) for a, b in halts}),
        "drift_range": [min(b - 5 * a for a, b in halts), max(b - 5 * a for a, b in halts)] if halts else None,
        "seconds": round(time.time() - t0),
    }


if __name__ == "__main__":
    m, ev, pos, A, B = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    procs = int(sys.argv[7]) if len(sys.argv) > 7 else 4
    res = scan(m, ev, pos, A, B, procs)
    if len(sys.argv) > 6 and sys.argv[6] != "-":
        with open(sys.argv[6], "w") as f:
            json.dump(res, f, indent=1)
            f.write("\n")
    print(m, "event", res["event"], "pos", pos, res["outcomes"], "drift range of halts", res["drift_range"],
          "classes", res["halting_classes"])
