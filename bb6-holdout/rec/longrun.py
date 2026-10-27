"""Run the certified macro simulation (casesim) for a fixed time, logging progress."""
import sys, time, json
import casesim, proofs
from symtm import Config, Blank, try_lemma, step

limit = float(sys.argv[1]); every = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
t0 = time.time()
cfg = Config([Blank()], "A", [Blank()])
while not proofs.is_pass_position(cfg):
    if not try_lemma(cfg): step(cfg)
phase = "gap"; rounds = 0; cleans = 0; last_clean = None; macro = 0
log = open("longrun.log", "w")


def report(final=False):
    w, mk = casesim.marks_of(cfg)
    print(json.dumps(dict(final=final, rounds=rounds, steps=cfg.steps.k, w=w, cleans=cleans, last_clean=last_clean,
                          macro=macro, secs=round(time.time() - t0))), file=log, flush=True)


while time.time() - t0 < limit:
    if phase == "gap":
        cfg = casesim.gap_phase(cfg); macro += 1
        phase = "gap" if proofs.is_pass_position(cfg) else "packet"
    else:
        probe = cfg.copy(); try_lemma(probe, use=("CARRY",))
        if casesim.ends_with_blank(probe.left) and len(casesim.canon(probe.left)) == 1:
            bl, segs, br = casesim.signature(probe.right)
            if len(segs) == 4 and segs[0] == segs[1] == segs[3] == (1, 1, 1) and segs[2][:2] == (1, 1) and br:
                cleans += 1; last_clean = (probe.steps.k - 1, (segs[2][2] - 1) // 2)
        cfg, kind = casesim.packet_phase(cfg); macro += 1
        if kind == "round":
            rounds += 1
            if rounds % every == 0: report()
            phase = "gap"
        elif kind is None: phase = "gap"
        else: phase = "packet"
report(final=True)
