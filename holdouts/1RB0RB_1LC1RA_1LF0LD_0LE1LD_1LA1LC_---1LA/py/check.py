"""Cross-checks for 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA.

  python3 check.py STEPS SWEEPS

1. the pass machine (passmachine.py, the transcription of lean/Sweep.lean) against a direct simulation of the
   machine for STEPS steps: every turn configuration (C on a 1 after a move right) at the same step, with the
   same tape;
2. the bit rule (rules.sweep_bits, rules.reset_bits) against the pass machine for SWEEPS sweeps: the same words at
   every turn at the right end, at the same steps (a reset takes one or two macro steps of the pass machine);
3. the run-length coded digit rule (rules.Runs) against the bit rule, word and step count, for SWEEPS sweeps.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import passmachine as pm
import rules

M = "1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA"
INIT = ([], [], 2)       # the first turn: the word `x` after 2 steps


def table(m):
    T = {}
    for i, g in enumerate(m.split('_')):
        for r in range(2):
            t = g[3 * r:3 * r + 3]
            T[(chr(65 + i), r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    return T


def tape_of(out, rest, pos):
    """cells of RT out rest, head (on the first cell of the pair 11) at pos."""
    cells = {}
    p = pos
    for b in out:            # nearest first: c2 = 1 at p-1, c1 = b at p-2
        cells[p - 1] = 1
        cells[p - 2] = int(b)
        p -= 2
    cells[pos] = 1
    cells[pos + 1] = 1
    for k, c in enumerate(rest):
        cells[pos + 2 + k] = int(c)
    return {k: v for k, v in cells.items() if v}


def check_direct(steps):
    T = table(M)
    tape, p, s, last = {}, 0, 'A', None
    turns = []
    for t in range(steps):
        r = tape.get(p, 0)
        tr = T[(s, r)]
        if tr is None:
            print("halt at", t + 1)
            return False
        w, d, ns = tr
        if w:
            tape[p] = 1
        else:
            tape.pop(p, None)
        if ns == 'C' and d == -1 and last == 1 and tape.get(p - 1, 0) == 1:
            turns.append((t + 1, p - 1, dict(tape)))
        last = d
        p += d
        s = ns
    out, rest, tm = INIT
    for (t, pos, tp) in turns:
        if t != tm or tape_of(out, rest, pos) != tp:
            print("MISMATCH at turn", t, tm)
            return False
        r = pm.mstep(out, rest)
        if r[0] != 'go':
            print("pass machine halts")
            return False
        tm += r[1]
        out, rest = r[2], r[3]
    print(f"1. pass machine = machine: {len(turns)} turns in {steps} steps")
    return True


def bits_of(out):
    return [int(b) for b in reversed(out)] + [1]


def check_bits(sweeps):
    out, rest, tm = INIT
    W, t = [1], 2
    resets = 0
    for s in range(sweeps):
        r, W2, cost = rules.sweep_bits(W)
        # the pass machine to its next turn at the right end
        r1 = pm.mstep(out, rest)
        assert r1[0] == 'go'
        tm += r1[1]
        out, rest = r1[2], r1[3]
        while rest:
            r1 = pm.mstep(out, rest)
            assert r1[0] == 'go'
            tm += r1[1]
            out, rest = r1[2], r1[3]
        if r == 'reset':
            resets += 1
            W2 = rules.reset_bits(W) if len(W) >= 2 else bits_of(out)   # the one-letter word `x` at the start
            cost = tm - t
        assert r != 'halt'
        W, t = W2, t + cost
        if W != bits_of(out) or t != tm:
            print("MISMATCH at sweep", s)
            return False
    print(f"2. bit rule = pass machine: {sweeps} sweeps ({resets} resets), step {t}")
    return True


def check_runs(sweeps):
    W, t = [1, 0, 0, 0, 1], 30          # the word after the first reset (sweep 1 of the bit rule)
    S = rules.Runs(*rules.to_digits(W), t=t)
    for s in range(sweeps):
        r, W2, cost = rules.sweep_bits(W)
        r2 = S.sweep()
        if r == 'reset':
            assert r2 == 'reset'
            W2 = rules.reset_bits(W)
            S = rules.Runs(*rules.to_digits(W2), t=S.t)
            W = W2
            continue
        W, t = W2, t + cost
        if r2 != 'ok' or S.bits() != W or S.t != t:
            print("MISMATCH at sweep", s)
            return False
    # the digit rule itself
    W = [1, 0, 0, 0, 1]
    for s in range(min(sweeps, 3000)):
        r, W2, _ = rules.sweep_bits(W)
        rd, d2 = rules.sweep_digits(*rules.to_digits(W))
        if r == 'reset':
            assert rd == 'reset'
            W = rules.reset_bits(W)
            continue
        assert rd == 'ok' and rules.to_bits(*d2) == W2
        W = W2
    print(f"3. run-coded digits = digit rule = bit rule: {sweeps} sweeps (steps counted only between resets)")
    return True


def check_random(trials, seed=1):
    """4. random words: the bit rule against the pass machine, from the turn of the word to the next turn at the
    right end (a sweep, a reset, or a halt)."""
    import random
    rnd = random.Random(seed)
    for _ in range(trials):
        n = rnd.randint(2, 40)
        W = [rnd.randint(0, 1) for _ in range(n - 1)] + [1]
        if rnd.random() < 0.5:            # many words without 00, to exercise the resets
            for k in range(n - 1):
                if W[k] == 0 and W[k + 1] == 0:
                    W[k + 1] = 1
        r, W2, cost = rules.sweep_bits(W)
        out, rest, t = [bool(b) for b in reversed(W[:-1])], [], 0
        halted = False
        while True:
            r1 = pm.mstep(out, rest)
            if r1[0] == 'halt':
                halted = True
                break
            t += r1[1]
            out, rest = r1[2], r1[3]
            if not rest:
                break
        if r == 'halt':
            ok = halted
        elif r == 'reset':
            if W[0] == 0 and W[1] == 0:
                continue
            ok = (not halted) and rules.reset_bits(W) == bits_of(out)
        else:
            ok = (not halted) and W2 == bits_of(out) and cost == t
        if not ok:
            print("MISMATCH on", W)
            return False
    print(f"4. bit rule = pass machine on {trials} random words")
    return True


if __name__ == "__main__":
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 3_000_000
    sweeps = int(float(sys.argv[2])) if len(sys.argv) > 2 else 3000
    ok = check_direct(steps) and check_bits(sweeps) and check_runs(sweeps) and check_random(20000)
    print("ALL OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)
