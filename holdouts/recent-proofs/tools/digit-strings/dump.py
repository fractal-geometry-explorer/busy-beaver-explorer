"""dump left-end event lists of an F05 machine (frame A) to a jsonl file: step, list"""
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
    f = open(out, "w")
    def ev(s, l):
        if all(all(c == 0 for c in w) for w, n in s.left):
            f.write(json.dumps([str(s.steps), [str(x) for x in l]]) + "\n")
    try:
        r = h._run(sim, 0, stop_left=False, N=N, on_event=ev)
    except rle.Halt:
        r = "halt"
    f.close(); return h, r
if __name__ == "__main__":
    h, r = run(sys.argv[1], ft.steps_arg(sys.argv[2]), sys.argv[3])
    print(r, len(h.fev))
