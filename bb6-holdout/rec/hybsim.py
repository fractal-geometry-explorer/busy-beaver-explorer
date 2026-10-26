"""Run the real machine from a round-start configuration given by marks, at any width: proven macro rules (casesim)
where they apply, and plain transitions accelerated by the three cycle lemmas where they don't (contacts).
usage: python3 hybsim.py STATEFILE   (file: a b c d ... E = wall positions then width; gap at cell 1)"""
import sys, time
sys.setrecursionlimit(100000)
from symtm import Config, Rep, Blank, Lin, step, try_lemma, Halted, TouchContext, NeedSplit, _unroll_front
import casesim
from casesim import gap_phase, packet_phase, Uncovered, signature, canon, ends_with_blank
import proofs
import os
VERBOSE = bool(os.environ.get('HYBV')); STOP_CLEAN = not os.environ.get('HYBNOSTOP'); T0 = time.time()

def stretches(marks, Wd):
    """Maximal alternating stretches (first value, length) of the round-start tape, never expanding cells."""
    rep = set()                                # cells equal to their left neighbour
    for t, p in marks:
        ln = {'W': 2, 'G': 3, 'M': 2, 'B': 3}[t]
        for i in range(p + 1, p + ln): rep.add(i)
    cuts = sorted(rep) + [Wd]
    out = []; start = 0; v = 1                  # cell 0 is 1
    for c in cuts:
        n = c - start
        out.append((v, n))
        last = v if n % 2 else 1 - v
        v = last; start = c                    # cell c repeats the previous value
    out[-1] = (out[-1][0], out[-1][1])
    return out

def tokens_of(st):
    toks = []
    for f, n in st:
        if n >= 2: toks.append(Rep((f, 1 - f), Lin(n // 2)))
        if n % 2: toks.append(f)
    return toks

def config_from(marks, Wd):
    # parity: cell i of the stripes is 1 iff i has the parity of the current phase; a 0-run must start on a 0 cell
    ph = 0; prev = 1
    for t, p in sorted(marks, key=lambda m: m[1]):
        ln = {'W': 2, 'G': 3, 'M': 2, 'B': 3}[t]; sym = 0 if t in 'WG' else 1
        expect = 1 if (p % 2 == ph) else 0               # value alternation gives at cell p
        assert expect == sym, f"parity clash for {t} at {p}"
        if ln % 2 == 0: ph ^= 1                          # an even-length run flips the phase
        else: pass
    assert (1 if ((Wd - 1) % 2 == ph) else 0) == 1, "the last cell must be a 1"
    st = stretches(marks, Wd)
    # split at cell 3: left = cells 0..2, right = cells 3..
    left = []; right = []; pos = 0
    for f, n in st:
        if pos + n <= 3: left.append((f, n))
        elif pos >= 3: right.append((f, n))
        else:
            k = 3 - pos; left.append((f, k)); f2 = f if k % 2 == 0 else 1 - f; right.append((f2, n - k))
        pos += n
    return Config([Blank()] + tokens_of(left), "E", tokens_of(right) + [Blank()])

def is_packet_position(cfg):
    if cfg.state != "A": return False
    r = list(cfg.right)
    try:
        a = _unroll_front(r); tail = r[1:]; b = _unroll_front(tail)
    except (TouchContext, NeedSplit):
        return False
    return a == 1 and b == 1

def run(cfg, max_rounds=10 ** 6, max_fallback=10 ** 7, log=print):
    phase = "gap"; rounds = 0; fallback_steps = 0; contacts = 0
    while rounds < max_rounds:
        try:
            if phase == "gap":
                cfg = gap_phase(cfg); phase = "gap" if proofs.is_pass_position(cfg) else "packet"
            else:
                cfg, kind = packet_phase(cfg)
                if kind == "round":
                    rounds += 1; phase = "gap"
                    if STOP_CLEAN:
                        w, mk = casesim.marks_of(cfg)
                        if len(mk) == 2 and mk[1] == ('M', w - 2):
                            return dict(result="clean", n=(w - 6) // 2, steps=cfg.steps.k, rounds=rounds, contacts=contacts, cfg=cfg)
                    if VERBOSE: log(f"  round {rounds}: step {cfg.steps.k}, tokens {len(cfg.left) + len(cfg.right)}, t={time.time() - T0:.1f}")
                elif kind is None: phase = "gap"
                else: phase = "packet"
            continue
        except Uncovered as e:
            msg = str(e)
            if "would halt" in msg:
                return dict(result="halt", rule="PACKET->block", steps=cfg.steps.k + 4, rounds=rounds, contacts=contacts, cfg=cfg)
            contacts += 1; log(f"  round {rounds}: no rule applies ({msg[:90]}...); stepping the machine")
        # fallback: plain transitions with the cycle lemmas until a rule position is reached again
        n = 0
        while True:
            try:
                if not try_lemma(cfg): step(cfg)
            except Halted as h:
                return dict(result="halt", rule=f"state/symbol {h}", steps=cfg.steps.k, rounds=rounds, contacts=contacts, cfg=cfg)
            n += 1; fallback_steps += 1
            if n > max_fallback: return dict(result="fallback limit", steps=cfg.steps.k, rounds=rounds, cfg=cfg)
            if proofs.is_pass_position(cfg): phase = "gap"; break
            if is_packet_position(cfg): phase = "packet"; break
        log(f"    resumed rules after {n} transitions/lemmas")
    return dict(result="round limit", steps=cfg.steps.k, rounds=rounds, cfg=cfg)

if __name__ == '__main__':
    xs = list(map(int, open(sys.argv[1]).read().split()))
    walls, Wd = xs[:-1], xs[-1]
    marks = [('G', 1)] + [('W', p) for p in walls]
    cfg = config_from(marks, Wd)
    t0 = time.time()
    res = run(cfg)
    c = res.pop('cfg')
    print(res, f"({time.time() - t0:.1f} s)")
    if res['result'] == 'halt':
        # describe the tape near the head
        print("  head state", c.state, "; left tail", canon(c.left)[-6:], "; right head", canon(c.right)[:6])
