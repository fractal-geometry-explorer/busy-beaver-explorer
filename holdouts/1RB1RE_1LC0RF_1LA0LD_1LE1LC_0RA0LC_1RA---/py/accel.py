"""Accelerated run of 1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA--- from blank tape, sweep by sweep.

A sweep starts with the head at the left end of the tape in state C.  A *normal* configuration there is

    C> a^n0 s(d1) a^n1 s(d2) a^n2 ... s(dk) a^nk REST        a = 001,  s(0)=0, s(1)=011, s(2)=00, s(3)=0101

(REST is whatever follows; in practice the end `01`, or a pair of digits whose block between has run out).  One
sweep adds one to the base-4 number V = d1 + 4 d2 + 16 d3 + ...: the digits 3 at the bottom become 0 and the next
digit goes up by one; n0..nj (the blocks left of that digit) gain one `a`, and the block right of it loses one when
the digit goes 0->1 or 2->3 (lean/Rules.lean: step0..2, sweep0..2, for every value and any number of carries).
The sweep takes 8 (n0 + ... + nj) + 10 j + 6 steps.  So with N_i = n_i + c(d_i), c = (0,1,1,2), N_i is fixed except
that it drops by one each time digit i wraps from 3 to 0, i.e. every 4^i sweeps: a *timer*.

`bulk` applies t sweeps at once (V += t, N_i -= the number of wraps of digit i, n0 += t, the exact step count summed
in closed form) for the largest t that keeps every block >= 1 and keeps the carry out of REST; everything else (the
carry reaching REST, a block running out) is one sweep of the run-length simulator `rlsim.Sim`, which is exact.

usage: python3 accel.py run 1eX         run to 10^X steps (e.g. 1e300), print progress and the catalogue of separators
       python3 accel.py check STEPS      compare every sweep start with the plain simulator (bbtools.machine)
       python3 accel.py fuzz             random test of rlsim.Sim against the plain simulator
"""
import collections
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from rlsim import Sim, canon, tostr, head_first, parse  # noqa: E402

M = "1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---"
S = {0: '0', 1: '011', 2: '00', 3: '0101'}
R = {v: k for k, v in S.items()}
C = [0, 1, 1, 2]
STATE_C = 2


def parse_norm(tok):
    """tok from canon(minrun=1): (n0, digits, timers N, rest) or None."""
    if not tok or tok[0][0] != '001':
        return None
    n0 = tok[0][1]
    d, N, pos = [], [], 1
    while True:
        q, sep = pos, ''
        while q < len(tok) and tok[q][0] != '001':
            sep += tok[q][0]
            q += 1
        if q < len(tok) and sep in R:
            d.append(R[sep])
            N.append(tok[q][1] + C[R[sep]])
            pos = q + 1
        else:
            break
    return n0, d, N, tok[pos:]


def build(n0, d, N, rest):
    tok = [['001', n0]]
    for di, Ni in zip(d, N):
        tok += [[c, 1] for c in S[di]]
        assert Ni - C[di] > 0
        tok.append(['001', Ni - C[di]])
    return tok + [list(x) for x in rest]


def bulk(n0, d, N, rest):
    """t sweeps at once: ((n0', d', N', rest), steps, t), or None if not even one is safe."""
    k = len(d)
    V = sum(di * 4 ** i for i, di in enumerate(d))
    t = 4 ** k - 1 - V              # the sweep at V = 4^k - 1 carries into rest
    for i in range(k):
        P, q, Ni = 4 ** (i + 1), 4 ** i, N[i]
        # the first V at which block i would be < 1 (N_i - c(d_i) < 1)
        if Ni >= 3:
            Vb = (V // P + (Ni - 2)) * P + 3 * q
        elif Ni == 2:
            Vb = (V // P) * P + 3 * q
        else:
            Vb = (V // P) * P + q
        if Vb <= V:
            return None
        t = min(t, Vb - V - 1)
    if t <= 0:
        return None
    V2 = V + t
    steps = 8 * (t * n0 + t * (t - 1) // 2) + 6 * t       # block 0 is crossed every sweep
    N2 = []
    for i in range(k):
        P = 4 ** (i + 1)
        w = V2 // P - V // P                                   # wraps of digit i+1: block i+1 crossed, then n = N-2
        steps += w * (8 * (N[i] - 2) + 10) - 8 * w * (w - 1) // 2
        N2.append(N[i] - w)
    return (n0 + t, [(V2 // 4 ** i) % 4 for i in range(k)], N2, rest), steps, t


def sweep(tok, steps):
    """One sweep of the exact run-length simulator, from C at the left end to C at the left end."""
    s = Sim(M, head_first(tok), STATE_C)
    s.dir, s.steps = -1, steps
    r = s.run(float('inf'), lambda s: s.q == STATE_C and s.h <= 0 and s.steps > steps)
    if r == 'halt':
        raise RuntimeError('HALT at step %d' % s.steps)
    if s.h < 0:
        s.tok.insert(0, ['0', 1])
    return canon(s.tok, minrun=1), s.steps


def first():
    s = Sim(M, [['0', 1]], 0)
    s.dir = 1
    s.run(10 ** 9, lambda s: s.q == STATE_C and s.h == 0 and s.steps > 100)
    return canon(s.tok, minrun=1), s.steps


def run(maxsteps, on_event=None):
    """Yields (kind, steps, sweeps, tok) at each bulk ('B') and each simulated sweep ('F')."""
    tok, steps = first()
    sweeps = 0
    while steps < maxsteps:
        p = parse_norm(tok)
        b = bulk(*p) if p else None
        if b:
            st, ds, t = b
            steps += ds
            sweeps += t
            tok = build(*st)
            yield 'B', steps, sweeps, tok
        else:
            tok, steps = sweep(tok, steps)
            sweeps += 1
            yield 'F', steps, sweeps, tok


def main_run(maxsteps):
    cat = collections.Counter()
    t0, mark, nb, nf = time.time(), 10, 0, 0
    for kind, steps, sweeps, tok in run(maxsteps):
        if kind == 'B':
            nb += 1
            continue
        nf += 1
        cur = ''
        for w, n in tok:
            if w == '001':
                if cur:
                    cat[cur] += 1
                cur = ''
            else:
                cur += w
        cat['END ' + cur] += 1
        while steps >= 10 ** mark:
            print('steps >= 1e%d  sweeps 1e%d  digits %d  bulks %d  simulated sweeps %d  %.0fs' % (
                mark, len(str(sweeps)) - 1, sum(1 for w, n in tok if w == '001') - 1, nb, nf, time.time() - t0),
                flush=True)
            mark += 10 if mark < 300 else 100
    print('no halt; final step count has %d digits' % len(str(steps)))
    print('separators seen right after a simulated sweep (count, cells):')
    for k, v in cat.most_common():
        print(' ', v, k)


def main_check(maxsteps):
    """Every sweep start of the accelerated run must be a sweep start of the plain run, with the same tape."""
    from bbtools.machine import Machine, Run
    r = Run(Machine.parse(M))
    want = {}
    while r.steps < maxsteps:
        r.step()
        if r.state == STATE_C and r.head == r.tape.lo:
            want[r.steps] = ''.join(map(str, r.tape.word(r.tape.lo, r.tape.hi)))
    n = 0
    for kind, steps, sweeps, tok in run(maxsteps):
        if steps > maxsteps:
            break
        cells = ''.join(w * c for w, c in tok)
        assert steps in want, steps
        assert want[steps].rstrip('0') == cells.rstrip('0'), (steps, want[steps][:80], cells[:80])
        n += 1
    print('ok: %d accelerated points agree with the plain simulator up to %d steps' % (n, maxsteps))


def main_fuzz(trials=3000):
    T = parse(M)
    random.seed(1)
    for _ in range(trials):
        tok = []
        for _ in range(random.randint(1, 8)):
            if random.random() < 0.5:
                tok.append([random.choice(['001', '010', '100', '110', '011', '101']), random.randint(2, 9)])
            else:
                tok += [[random.choice('01'), 1] for _ in range(random.randint(1, 4))]
        tok.append([random.choice('01'), 1])
        h = random.choice([i for i, (w, n) in enumerate(tok) if n == 1 and len(w) == 1])
        q = random.randrange(6)
        pos0 = sum(len(w) * n for w, n in tok[:h])
        s = Sim(M, [list(x) for x in tok], q, h)
        s.dir = 1
        s.run(random.randint(1, 400))
        cells = dict(enumerate(map(int, ''.join(w * n for w, n in tok))))
        p, st, k, halted = pos0, q, 0, False
        while k < s.steps:
            tr = T[(st, cells.get(p, 0))]
            k += 1
            if tr is None:
                halted = True
                break
            cells[p], mv, st = tr
            p += mv
        simcells = ''.join(w * n for w, n in s.tok)
        lo = min(cells)
        plain = ''.join(str(cells.get(i, 0)) for i in range(lo, lo + len(simcells)))
        assert halted == s.halted and plain == simcells and (halted or st == s.q)
    print('ok: %d random runs agree' % trials)


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'run'
    if cmd == 'run':
        main_run(10 ** int(sys.argv[2].split('e')[1]) if len(sys.argv) > 2 else 10 ** 300)
    elif cmd == 'check':
        main_check(int(float(sys.argv[2])) if len(sys.argv) > 2 else 2 * 10 ** 6)
    elif cmd == 'fuzz':
        main_fuzz()
