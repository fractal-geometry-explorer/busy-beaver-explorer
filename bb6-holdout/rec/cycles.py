"""For each n, start from the clean tape 0^inf A> 1 1 (10)^n 1 1 0^inf (the packet at the left end) and run the
certified macro simulation to the next clean tape. Outcomes: clean (next n), halt, uncovered (no rule matches)."""
import sys, json, time
import casesim, proofs
from symtm import Config, Blank, Rep, Lin, try_lemma

def clean_cfg(n):
    return Config([Blank()], "A", [1, 1, Rep((1, 0), Lin(n)), 1, 1, Blank()])

def is_clean(cfg):
    probe = cfg.copy(); try_lemma(probe, use=("CARRY",))
    if casesim.ends_with_blank(probe.left) and len(casesim.canon(probe.left)) == 1:
        bl, segs, br = casesim.signature(probe.right)
        if len(segs) == 4 and segs[0] == segs[1] == segs[3] == (1, 1, 1) and segs[2][:2] == (1, 1) and br:
            return (segs[2][2] - 1) // 2
    return None

def cycle(n, max_macro=100000):
    cfg = clean_cfg(n); phase = "packet"; rounds = 0; first = True
    for _ in range(max_macro):
        try:
            if phase == "gap":
                cfg = casesim.gap_phase(cfg); phase = "gap" if proofs.is_pass_position(cfg) else "packet"
            else:
                if not first:
                    m = is_clean(cfg)
                    if m is not None: return ("clean", m, rounds, cfg.steps.k)
                first = False
                cfg, kind = casesim.packet_phase(cfg)
                if kind == "round": rounds += 1
                phase = "packet" if kind == "packet" else "gap"
        except casesim.Uncovered as e:
            msg = str(e)
            return ("halt" if "halt" in msg else "uncovered", msg[:300], rounds, cfg.steps.k)
        except AssertionError as e:
            return ("uncovered", "assert " + str(e)[:300], rounds, cfg.steps.k)
    return ("budget", None, rounds, cfg.steps.k)

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = open(sys.argv[3], "w"); t0 = time.time()
    for n in range(lo, hi):
        r = cycle(n)
        print(json.dumps([n] + list(r)), file=out, flush=True)
    print("done", hi - lo, round(time.time() - t0, 1), "s")
