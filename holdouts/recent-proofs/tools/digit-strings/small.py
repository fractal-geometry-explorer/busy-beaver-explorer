"""run an F05 machine; whenever a left-end event shows a new drift with far fewer digits than its blocks' index scale,
save the previous and the current list.  usage: small.py MACHINE STEPS OUT.jsonl"""
import json
import os
import sys
PY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..",
                  "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "py")
sys.path.insert(0, PY)
import f05_timing as ft, fast, frames, hybrid, rle
def run(machine, N, out):
    fr, fa, st = frames.info(machine)
    cls = fast.Fast2 if fast.f05_run.needs_raw(fa) else fast.Fast
    h = cls(fa); sim = hybrid.FastRLE(fa); sim.q = ord(st) - 65; h.sim = sim; h.top = []
    f = open(out, "w"); S = {"prev": None, "n": 0, "pd": {}}
    def ev(s, l):
        if not all(all(c == 0 for c in w) for w, n in s.left): return
        S["n"] += 1
        T = l[1:]; cur = {}; hit = []
        for j in range(len(T) - 1):
            d = T[j + 1] - 5 * T[j]; cur[d] = cur.get(d, 0) + 1
            if S["pd"].get(d, 0): S["pd"][d] -= 1; continue
            if S["n"] > 40 and j > 20 and abs(d).bit_length() < 0.5 * (5 ** j).bit_length(): hit.append(j)
        if hit:
            f.write(json.dumps({"event": S["n"], "steps_digits": len(str(s.steps)), "hit": hit,
                                "prev": [str(x) for x in S["prev"]], "cur": [str(x) for x in l]}) + "\n"); f.flush()
        S["prev"] = list(l); S["pd"] = cur
        if S["n"] % 200 == 0: print("event", S["n"], "digits", len(str(s.steps)), "k", len(l), flush=True)
    try:
        r = h._run(sim, 0, stop_left=False, N=N, on_event=ev)
    except rle.Halt:
        r = "halt"
    print("done", r, S["n"])
if __name__ == "__main__":
    run(sys.argv[1], ft.steps_arg(sys.argv[2]), sys.argv[3])
