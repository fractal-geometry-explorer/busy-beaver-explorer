"""Fast unproved simulator: bbtools.macro + linear cycle jumps at tape-end samples (no Lean proofs).
Calls on_end(run) each time the head faces blank tape (after any jump)."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
from bbtools.macro import MacroRun
from bbtools.cycles import snapshot, detect

def run(machine, k, max_steps, on_end=None, margin=2, NF=1):
    r = MacroRun(machine, k)
    hist = {}
    while r.steps < max_steps:
        if not r.step(): return r
        front = r.right if r.dir == 1 else r.left
        if len(front) > NF: continue
        s = snapshot(r); key = s.key()
        h = hist.setdefault(key, []); h.append(s); del h[:-3]
        if len(h) == 3:
            cyc = detect(h)
            if cyc is not None:
                nl = len(s.left); cs = s.counts()
                kk = None
                for c, d in zip(cs, cyc.delta):
                    if d < 0:
                        room = (c - margin - 8) // (-d)
                        kk = room if kk is None else min(kk, room)
                if kk is not None and kk >= 2:
                    D = cyc.dsteps[1] - cyc.dsteps[0]; S = cyc.dsteps[1] + D
                    n = kk * S + D * kk * (kk - 1) // 2
                    for i, d in enumerate(cyc.delta):
                        if d:
                            ent = r.left[1 + i] if i < nl else r.right[1 + i - nl]
                            ent[1] += kk * d
                    r.steps += n; r.pos += kk * cyc.dpos
                    hist[key] = []
        if on_end: 
            if on_end(r) is False: return r
    return r
