"""run an F05 machine; at every left-end event, for each drift d = t(j+1) - 5 t(j) that is new, count the leading
base-5 digits that cancel (digits of max(5 t(j), t(j+1)) minus digits of d).  Save the histogram and every case with
at least MINC cancelled digits (with the blocks around it).   usage: canc.py MACHINE STEPS OUT.json [MINC=6]"""
import json
import os
import sys
PY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..",
                  "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "py")
sys.path.insert(0, PY)
import f05_timing as ft, fast, frames, hybrid, rle
def nd5(x):
    x = abs(x); n = 0
    while x: x //= 5; n += 1
    return n
def run(machine, N, out, minc):
    fr, fa, st = frames.info(machine)
    cls = fast.Fast2 if fast.f05_run.needs_raw(fa) else fast.Fast
    h = cls(fa); sim = hybrid.FastRLE(fa); sim.q = ord(st) - 65; h.sim = sim; h.top = []
    S = {"prev": None, "n": 0, "pd": {}, "hist": {}, "hits": [], "new": 0}
    def ev(s, l):
        if not all(all(c == 0 for c in w) for w, n in s.left): return
        S["n"] += 1
        T = l[1:]; cur = {}
        for j in range(len(T) - 1):
            d = T[j + 1] - 5 * T[j]; cur[d] = cur.get(d, 0) + 1
            if S["pd"].get(d, 0): S["pd"][d] -= 1; continue
            if S["n"] <= 40 or j < 12: continue
            S["new"] += 1
            c = max(nd5(5 * T[j]), nd5(T[j + 1])) - nd5(d)
            S["hist"][c] = S["hist"].get(c, 0) + 1
            if c >= minc:
                S["hits"].append({"event": S["n"], "steps_digits": len(str(s.steps)), "j": j, "k": len(T), "c": c,
                                  "d": str(d), "cur": [str(x) for x in T[max(0, j - 3):j + 4]],
                                  "prev_tail": [str(x) for x in S["prev"][-8:]], "cur_tail": [str(x) for x in T[-8:]]})
        S["prev"] = list(T); S["pd"] = cur
    try:
        r = h._run(sim, 0, stop_left=False, N=N, on_event=ev)
    except rle.Halt:
        r = "halt"
    json.dump({"machine": machine, "steps": sys.argv[2], "result": str(r), "events": S["n"], "new_drifts": S["new"],
               "hist": S["hist"], "hits": S["hits"]}, open(out, "w"))
if __name__ == "__main__":
    run(sys.argv[1], ft.steps_arg(sys.argv[2]), sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 6)
