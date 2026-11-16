"""Cross-checks for 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA.

  python3 check.py STEPS SWEEPS

1. the macro machine (passmachine.py, the transcription of lean/Sweep.lean) against a direct simulation of the
   machine for STEPS steps: at the start of every macro step the same configuration (tape, head, state) at the
   same step;
2. the bit rule (rules.sweep_bits, rules.reset_bits) against the macro machine for SWEEPS turns at the right end:
   the same words at the same steps (resets of words starting 11 have no closed form and are taken from the macro
   machine);
3. the run-length coded digit rule (rules.Runs) and the digit rule against the bit rule;
4. random words: the bit rule against the macro machine, from the turn of the word to the next turn (a sweep, a
   reset or a halt), and how resets of words starting 11 end.
"""
import os
import random
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import passmachine as pm
import rules

INIT = (('rt', []), 3)      # the first turn: the word `x` after 3 steps


def cfg_cells(state, pos):
    """the configuration of a macro state as {cell: 1}, state; the head at pos."""
    kind, v = state
    if kind == 'rt':
        l, r, s = [True], [True], 'D'
        for b in v:
            l += [True, b]
    else:
        l, r, s = v
    d = {}
    for k, b in enumerate(l):
        if b:
            d[pos - 1 - k] = 1
    for k, b in enumerate(r):
        if b:
            d[pos + k] = 1
    return d, s


def check_direct(steps):
    T = pm.TT
    tape, p, s, t = {}, 0, 'A', 0
    state, tm = INIT
    n = 0
    while tm <= steps:
        while t < tm:
            tr = T[(s, tape.get(p, 0))]
            if tr is None:
                print("machine halts at", t + 1)
                return False
            w, d, s = tr
            if w:
                tape[p] = 1
            else:
                tape.pop(p, None)
            p += 1 if d == 'R' else -1
            t += 1
        if cfg_cells(state, p) != (tape, s):
            print("MISMATCH at step", tm)
            return False
        r = pm.mstep(state)
        if r[0] != 'go':
            print("macro machine halts")
            return False
        tm += r[1]
        state = r[2]
        n += 1
    print(f"1. macro machine = machine: {n} macro steps in {steps} steps")
    return True


def to_next_rt(state):
    """macro steps from a state to the next turn configuration: ('rt', out, cost) | ('halt', cost)."""
    cost = 0
    while True:
        r = pm.mstep(state)
        if r[0] == 'halt':
            return 'halt', None, cost + r[1]
        cost += r[1]
        state = r[2]
        if state[0] == 'rt':
            return 'rt', state[1], cost


def check_bits(sweeps):
    state, t = INIT
    W = [1]
    kinds = Counter()
    for s in range(sweeps):
        k, out, cost_m = to_next_rt(state)
        assert k == 'rt'
        r, W2, cost = rules.sweep_bits(W)
        if r == 'reset':
            W2 = rules.reset_bits(W) if len(W) >= 2 else None
            kinds[tuple(W[:2])] += 1
            if W2 is None:            # x, or a word starting 11: no closed form
                W2 = pm.word(out)
            cost = cost_m
        assert r != 'halt'
        if W2 != pm.word(out) or cost != cost_m:
            print("MISMATCH at sweep", s)
            return False
        W, t, state = W2, t + cost, ('rt', out)
    print(f"2. bit rule = macro machine: {sweeps} turns (resets of words starting {dict(kinds)}), step {t}")
    return True


def check_runs(sweeps):
    W, t = [1, 0, 1], 21          # the word after the first reset
    S = rules.Runs(*rules.to_digits(W), t=t)
    for s in range(sweeps):
        r, W2, cost = rules.sweep_bits(W)
        r2 = S.sweep()
        if r == 'reset':
            assert r2 == 'reset'
            W2 = rules.reset_bits(W)
            if W2 is None:
                k, out, cost = to_next_rt(('rt', [bool(b) for b in reversed(W[:-1])]))
                W2 = pm.word(out)
            S = rules.Runs(*rules.to_digits(W2), t=S.t)
            W = W2
            continue
        W, t = W2, t + cost
        if r2 != 'ok' or S.bits() != W or S.t != t:
            print("MISMATCH at sweep", s)
            return False
    W = [1, 0, 1]
    for s in range(min(sweeps, 3000)):
        r, W2, _ = rules.sweep_bits(W)
        rd, d2 = rules.sweep_digits(*rules.to_digits(W))
        if r == 'reset':
            assert rd == 'reset'
            W2 = rules.reset_bits(W)
            if W2 is None:
                W2 = pm.word(to_next_rt(('rt', [bool(b) for b in reversed(W[:-1])]))[1])
            W = W2
            continue
        assert rd == 'ok' and rules.to_bits(*d2) == W2
        W = W2
    print(f"3. run-coded digits = digit rule = bit rule: {sweeps} sweeps (steps counted only between resets)")
    return True


def check_random(trials, seed=1):
    rnd = random.Random(seed)
    ends = Counter()
    for _ in range(trials):
        n = rnd.randint(2, 30)
        W = [rnd.randint(0, 1) for _ in range(n - 1)] + [1]
        if rnd.random() < 0.6:
            for k in range(n - 1):
                if W[k] == 0 and W[k + 1] == 0:
                    W[k + 1] = 1
        r, W2, cost = rules.sweep_bits(W)
        k, out, cm = to_next_rt(('rt', [bool(b) for b in reversed(W[:-1])]))
        if r == 'halt':
            ok = k == 'halt'
        elif r == 'reset':
            R = rules.reset_bits(W)
            if R is None:
                w0 = rules.to_digits(W)[0]
                ends[(w0 if w0 <= 6 else '>6', k)] += 1
                ok = True
            else:
                ok = k == 'rt' and pm.word(out) == R
        else:
            ok = k == 'rt' and pm.word(out) == W2 and cm == cost
        if not ok:
            print("MISMATCH on", W)
            return False
    print(f"4. bit rule = macro machine on {trials} random words; resets of words starting 11, by wall "
          f"(turn or halt): {sorted(ends.items(), key=str)}")
    return True


if __name__ == "__main__":
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 3_000_000
    sweeps = int(float(sys.argv[2])) if len(sys.argv) > 2 else 3000
    ok = check_direct(steps) and check_bits(sweeps) and check_runs(sweeps) and check_random(20000)
    print("ALL OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)
