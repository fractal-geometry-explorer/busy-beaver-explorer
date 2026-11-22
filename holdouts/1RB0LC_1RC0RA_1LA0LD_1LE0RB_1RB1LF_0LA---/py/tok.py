"""Token-level simulator of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA--- with jumps over walking rounds.

The tape at an event (state A at the left end) is a list of tokens, left to right: the cells 0 and 1 and runs [n]
meaning (01)^n, in the canonical greedy parse (no literal 0 directly before a literal 1, no two runs side by side).
A round is simulated by engine.Eng on the shortest prefix that the head stays inside.  When the first cursor walks
through a long run, whole double rounds are applied at once:

    m | x1 | ... | a "1" b   ->  m-2j | x1 | ... | a+6j "1" b-2j        (round_one then round_zero, j times)
    m "1" b                  ->  m+4j "1" b-2j                          (first_one then first_zero, j times)

each jump is preceded by two explicit double rounds that must agree with this formula and cost c and c+32 steps.
"""
import sys
from engine import Eng, T as TT

SEP = [0, [1], 1, 0]


class Need(Exception):
    pass


class PEng(Eng):
    """Eng on a prefix of the tape: reading past its end raises Need (unless the prefix is the whole tape)."""
    whole = True

    def step(s):
        if not s.R and not s.whole:
            raise Need()
        Eng.step(s)


def norm(toks):
    out = []
    for x in toks:
        if type(x) is list:
            if x[0] == 0: continue
            if out and type(out[-1]) is list: out[-1] = [out[-1][0] + x[0]]
            else: out.append([x[0]])
        elif x == 1 and out and out[-1] == 0:
            out.pop()
            if out and type(out[-1]) is list: out[-1] = [out[-1][0] + 1]
            else: out.append([1])
        else:
            out.append(x)
    while out and out[-1] == 0: out.pop()
    return out


def cells(toks):
    return ''.join('01' * x[0] if type(x) is list else str(x) for x in toks).rstrip('0')


def show(toks, lim=None):
    """Readable: runs as numbers, separators as |, other cells quoted."""
    out = []; i = 0; buf = ''
    while i < len(toks):
        x = toks[i]
        if toks[i:i + 4] == SEP:
            if buf: out.append('"' + buf + '"'); buf = ''
            out.append('|'); i += 4; continue
        if type(x) is list:
            if buf: out.append('"' + buf + '"'); buf = ''
            out.append(str(x[0]))
        else:
            buf += str(x)
        i += 1
    if buf: out.append('"' + buf + '"')
    s = ' '.join(out)
    return s if lim is None or len(s) <= lim else s[:lim] + ' ...'


def round_(toks, p0=8):
    """One round from an event; returns (new tokens, steps) or (None, steps) on a halt."""
    p = p0
    while True:
        whole = p >= len(toks)
        e = PEng(); e.whole = whole
        for x in reversed(toks[:p]):
            e.R.append([x[0]] if type(x) is list else x)
        try:
            ok = e.run_event()
        except Need:
            p *= 2; continue
        if not ok:
            return None, e.steps
        new = [([x[0]] if type(x) is list else x) for x in reversed(e.R)]
        return norm(new + toks[p:]), e.steps


def walking(toks):
    """(kind, i_m, i_a, i_c, i_b) when the first cursor is a single cell between two runs, else None."""
    if not toks or type(toks[0]) is not list: return None
    i = 1; seps = 0
    while toks[i:i + 4] == SEP:
        seps += 1; i += 4
        if i < len(toks) and type(toks[i]) is list:
            if toks[i + 1:i + 5] == SEP: i += 1
    if seps and i < len(toks) and type(toks[i]) is list: i += 1
    # toks[i] should be the cursor cell, toks[i-1] the run a, toks[i+1] the run b
    if i + 1 >= len(toks) or toks[i] not in (0, 1) or type(toks[i - 1]) is not list or type(toks[i + 1]) is not list:
        return None
    if toks[i] == 0 and toks[i + 1] == [1] and toks[i + 2:i + 4] == [1, 0]:
        return None
    return ('sep' if seps else 'first', i - 1, i, i + 1)


def predict(toks, w, j):
    kind, ia, ic, ib = w
    t = [([x[0]] if type(x) is list else x) for x in toks]
    if kind == 'first':
        t[0][0] += 4 * j
    else:
        t[0][0] -= 2 * j; t[ia][0] += 6 * j
    t[ib][0] -= 2 * j
    return norm(t)


class Sim:
    def __init__(s):
        s.toks = []; s.steps = 0; s.rounds = 0; s.halted = False; s.jumps = 0
        s.log = None   # callback(sim, toks_before, toks_after, kind) for explicit rounds

    def explicit(s):
        before = s.toks
        new, st = round_(s.toks)
        s.steps += st; s.rounds += 1
        if new is None:
            s.halted = True; return False
        s.toks = new
        if s.log: s.log(s, before, new)
        return True

    def jump_if(s, margin=6):
        w = walking(s.toks)
        if not w: return False
        m = s.toks[0][0]; b = s.toks[w[3]][0]
        j = (b - margin) // 2
        if w[0] == 'sep': j = min(j, (m - margin) // 2)
        if j < 3: return False
        pred1 = predict(s.toks, w, 1); pred2 = predict(s.toks, w, 2)
        s0 = s.steps
        for _ in range(2): s.explicit()
        c1 = s.steps - s0
        if s.toks != pred1: raise AssertionError('double round 1 disagrees')
        for _ in range(2): s.explicit()
        c2 = s.steps - s0 - c1
        if s.toks != pred2 or c2 - c1 != 32: raise AssertionError(f'double round 2 disagrees {c1} {c2}')
        k = j - 2
        s.toks = predict(s.toks, walking(s.toks), k)
        s.steps += k * (c2 + 32) + 32 * k * (k - 1) // 2
        s.rounds += 2 * k; s.jumps += 1
        return True

    def run(s, max_steps=None, max_rounds=None):
        while not s.halted:
            if max_steps and s.steps >= max_steps: break
            if max_rounds and s.rounds >= max_rounds: break
            if not s.jump_if():
                s.explicit()
        return s


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if cmd == 'check':
        # compare with the plain engine at every event of the first N steps (tape and step count)
        N = float(sys.argv[2]) if len(sys.argv) > 2 else 3e7
        e = Eng(); s = Sim(); n = 0
        seen = {}
        def log(sim, b, a): seen[sim.steps] = cells(a)
        s.log = log
        s.run(max_steps=N)
        while e.steps < s.steps:
            e.run_event(); n += 1
            if e.steps in seen and seen[e.steps] != e.cells():
                print('MISMATCH at', e.steps); sys.exit(1)
        assert e.steps == s.steps and e.cells() == cells(s.toks), (e.steps, s.steps)
        print(f'agree: {n} events, {s.steps} steps, {len(seen)} explicit rounds compared, {s.jumps} jumps')
    else:
        N = float(sys.argv[2])
        s = Sim(); nxt = 10
        while not s.halted and s.steps < N:
            if not s.jump_if(): s.explicit()
            if s.steps >= nxt:
                print(f'{s.steps:.3e} r={s.rounds} j={s.jumps} n={len(s.toks)}', show(s.toks, 300)); sys.stdout.flush()
                while nxt <= s.steps: nxt *= 10
        print('HALT' if s.halted else 'no halt', s.steps, s.rounds)
