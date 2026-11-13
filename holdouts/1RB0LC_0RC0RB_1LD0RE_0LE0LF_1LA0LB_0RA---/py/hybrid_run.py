"""Run the exact visit-map simulator (hybrid.py) of one family machine far, check it against the direct run, and
write data/hybrid.json.

The check: every left-end event (step, block list) and every F-event (step, cell read) of data/trajectory.json
(the run-length simulation of the machine itself, ~1e11 steps) must equal the hybrid's events up to that step.
Big numbers are stored as decimal strings.

usage: python3 hybrid_run.py MACHINE [STEPS=1e100]
"""
import sys, os, json, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hybrid  # noqa: E402

HERE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main(m, N):
    h, r, secs = hybrid.run_machine(m, N)
    tr = json.load(open(os.path.join(HERE, m, "data", "trajectory.json")))
    M = tr["steps"]
    ta = [(t["step"], t["blocks"]) for t in tr["top_events"]]
    tb = [(t[0], t[2]) for t in h.top if t[0] <= M]
    fa = [(f["step"], f["reads"]) for f in tr["f_events"]]
    fb = [(f[0], f[1]) for f in h.fev if f[0] <= M]
    # the two logs may differ by one event in the first 10 steps (the X machine's first visit, to [0])
    extra = [e for e in ta + tb if e[0] < 10 and (e in ta) != (e in tb)]
    top_ok = [e for e in ta if e not in extra] == [e for e in tb if e not in extra]
    f_ok = fa == fb
    reads = collections.Counter((f[1], f[2]) for f in h.fev)
    out = {
        "machine": m, "target_steps": "%.0e" % N, "steps": str(h.sim.steps), "steps_approx": "%.4e" % h.sim.steps,
        "halted": h.halted, "seconds": round(secs, 1),
        "validated_against": {"trajectory_steps": M, "left_end_events": len(ta), "left_end_match": top_ok,
                              "left_end_extra_initial": extra, "f_events": len(fa), "f_match": f_ok},
        "left_end_events": len(h.top), "f_events_count": len(h.fev),
        "f_reads_one": sum(1 for f in h.fev if f[1] == 1),
        "f_contexts": [{"reads": y, "context": c, "count": n} for (y, c), n in reads.most_common()],
        "stats": h.stats,
        "f_events": [{"step": str(t), "reads": y} for (t, y, c) in h.fev],
        "left_end": [{"step": str(t), "pos": p, "blocks": len(l), "first": [str(x) for x in l[:3]]}
                     for (t, p, l) in h.top],
    }
    json.dump(out, open(os.path.join(HERE, m, "data", "hybrid.json"), "w"), indent=0)
    print(m, out["steps_approx"], "halt" if h.halted else "no halt", "top", len(h.top), "F", len(h.fev),
          "F reads 1:", out["f_reads_one"], "valid", top_ok, f_ok, extra, f"{secs:.0f}s")


if __name__ == "__main__":
    main(sys.argv[1], float(sys.argv[2]) if len(sys.argv) > 2 else 1e100)
