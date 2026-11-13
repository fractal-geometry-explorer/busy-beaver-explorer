"""Run a machine of the family from blank tape with the exact run-length simulator (rle.py), in its frame-A form
(frames.py), and record

  * the *top events*: the head back at the left end of the visited tape (frame A), in state A on a 0 after a
    move left, with the tape right of it  0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1 0^inf  -- the list [b1, ..., bk];
  * the *F-events*: every entry into state F (frame A), the only state that can halt, with the cells around the
    head and the cell F reads (a 1 there is the halt).

usage: python3 trajectory.py MACHINE STEPS OUT.json
"""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rle, frames  # noqa: E402


def run(machine, N, log=None):
    fr, fa, st = frames.info(machine)
    sim = rle.RLE(fa)
    sim.q = ord(st) - 65
    top, fev = [], []
    lo = 0
    lastd = 0
    t0 = time.time()
    halted = None
    nextlog = 1e8
    while sim.steps < N:
        p0, q0 = sim.pos, sim.q
        try:
            crossed = sim.try_cross()
            if not crossed:
                sim.step()
        except rle.Halt:
            halted = sim.steps
            l, r = rle.near(sim, 24)
            fev.append({"step": sim.steps, "left": l, "right": r, "reads": int(r[0]), "halt": True})
            break
        d = sim.pos - p0
        if d:
            lastd = 1 if d > 0 else -1
        if sim.pos < lo:
            lo = sim.pos
        if not crossed and sim.q == 5 and q0 != 5:
            l, r = rle.near(sim, 24)
            fev.append({"step": sim.steps, "left": l, "right": r, "reads": int(r[0])})
        if sim.q == 0 and lastd == -1 and sim.pos <= lo and (not sim.right or sim.right[-1][0][0] == 0):
            L = rle.suffix_list(sim)
            if L is not None and (not top or top[-1]["step"] != sim.steps):
                top.append({"step": sim.steps, "left_end": sim.pos, "blocks": L})
        if log and sim.steps >= nextlog:
            log(f"{machine} {sim.steps:.3e} steps, {len(top)} top events, {len(fev)} F-events, {time.time() - t0:.0f} s")
            nextlog *= 10
    return {"machine": machine, "frame": fr, "frame_a": fa, "start": st, "steps": sim.steps, "halted": halted,
            "top_events": top, "f_events": fev, "seconds": round(time.time() - t0)}


if __name__ == "__main__":
    m, N, out = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    res = run(m, N, log=lambda s: print(s, flush=True))
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, "w") as f:
        json.dump(res, f, indent=1)
    print("done", m, res["steps"], "halted" if res["halted"] else "no halt", len(res["top_events"]), len(res["f_events"]))
