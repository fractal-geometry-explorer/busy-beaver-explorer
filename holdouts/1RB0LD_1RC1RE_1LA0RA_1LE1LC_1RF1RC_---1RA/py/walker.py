"""Item model of 1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA, checked against cell-by-cell sweeps.

At a sweep start the head is in state C on the blank cell right of the tape, and the tape is groups 1^m 0, then 1^t.
Items [(x, m)]: x groups 110 then one group 1^m 0 (m != 2); the tail: q groups 110 then 1^t.  See ../README.md.

    python3 walker.py check     random walker sweeps, shallow carries and pushes against cell-by-cell sweeps; the
                                model (no phase jumps) against the direct run from blank tape; the halting example
"""
import random, sys

M = '1RB0LD_1RC1RE_1LA0RA_1LE1LC_1RF1RC_---1RA'
TAB = {}
for i, g in enumerate(M.split('_')):
    for s in (0, 1):
        t = g[3 * s:3 * s + 3]
        TAB[(i, s)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)


def cells_of(items, q, t=2):
    c = []
    for x, m in items:
        c += [1, 1, 0] * x + [1] * m + [0]
    return c + [1, 1, 0] * q + [1] * t


def parse(cells):
    gs, m = [], 0
    for v in cells:
        if v == 1:
            m += 1
        else:
            gs.append(m); m = 0
    items, x = [], 0
    for g in gs:
        if g == 2:
            x += 1
        else:
            items.append((x, g)); x = 0
    return items, x, m


def cell_sweep(items, q, t=2, maxn=10 ** 9):
    """Run from the sweep start to the next one (state C on a fresh blank cell right of all visited cells)."""
    c = cells_of(items, q, t)
    pad = 64
    tape = bytearray(pad) + bytearray(c) + bytearray(pad)
    pos = pad + len(c); st = 2; hi = pos; n = 0
    while n < maxn:
        tr = TAB[(st, tape[pos])]
        if tr is None:
            return 'HALT', n
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; n += 1
        if pos < 1:
            return 'LEFT', n
        if pos > hi:
            hi = pos
            if pos >= len(tape) - 2:
                tape.extend(bytes(64))
            if st == 2 and tape[pos] == 0:
                lo = 0
                while tape[lo] == 0:
                    lo += 1
                return parse(list(tape[lo:pos])), n
    return 'MAX', n


def model(items, q, t=2):
    """One sweep by the rules of c/walker.c, or None when the sweep is an event (run cell by cell there)."""
    items = list(items)
    if t == 2 and items and items[-1][1] != 1:
        x, m = items[-1]; n = 10 * q + 23
        if m == 3 and x >= 1:
            items[-1] = (x - 1, 6); q += 1
        elif m == 3:
            if len(items) < 2:
                return None
            y, mm = items[-2]; items[-2:] = [(y, mm + 4)]; q += 1
        elif m == 5:
            items.pop(); q += x + 3
        else:
            items[-1] = (x, m - 3); q += 2
        return (items, q, 2), n
    if t == 2 and items and items[-1][1] == 1 and items[-1][0] >= q // 4 + 1:
        k, r = divmod(q, 4); x = items[-1][0]
        n = 50 * k * k + (88 * k + 28 if r < 2 else 138 * k + 82) + (7 if r % 2 else 0)
        items[-1] = (x - k - 1, 6 if r < 2 else 3)
        return (items, 5 * k + (3 if r >= 2 else 0), 6 if r % 2 else 2), n
    if t == 6 and items:
        return (items + [(q, 3)], 1, 2), 13
    return None


def rnd_items(rng):
    k = rng.randint(0, 4)
    items = [(0, 1)] + [(rng.randint(0, 12), rng.choice([1, 3, 4, 5, 6, 7, 8, 9, 10])) for _ in range(k)]
    return items


def check_random(n=3000, seed=1):
    rng = random.Random(seed); kinds = {}
    for _ in range(n):
        items = rnd_items(rng); q = rng.randint(0, 60); t = 2
        r = rng.random()
        if r < 0.35:     # force a shallow carry
            items[-1] = (q // 4 + 1 + rng.randint(0, 10), 1)
        elif r < 0.5:
            t = 6
        mo = model(items, q, t)
        if mo is None:
            continue
        cs = cell_sweep(items, q, t)
        if cs[0] in ('HALT', 'LEFT', 'MAX') or (tuple(cs[0]), cs[1]) != (tuple(mo[0]), mo[1]):
            print('MISMATCH', items, q, t, 'model', mo, 'cells', cs); return False
        kind = 'carry' if t == 2 and items[-1][1] == 1 else 'push' if t == 6 else 'walker'
        kinds[kind] = kinds.get(kind, 0) + 1
    print('random sweeps agree:', kinds)
    return True


def check_blank(max_steps=10 ** 7):
    """The model with events run cell by cell, against the direct run from blank tape (sweep starts and steps)."""
    # direct run: record every sweep start (state C on a fresh blank cell right of all visited cells)
    tape = {}; pos = 0; st = 0; n = 0; hi = 0; starts = {}
    while n < max_steps:
        tr = TAB[(st, tape.get(pos, 0))]
        if tr is None:
            print('direct run halted?'); return False
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; n += 1
        if pos > hi:
            hi = pos
            if st == 2 and n >= 49:
                lo = min(k for k, v in tape.items() if v)
                starts[n] = parse([tape.get(i, 0) for i in range(lo, pos)])
    T = 49; cfg = ([(0, 1)], 2, 2); ok = 0; ev = 0
    assert starts[49] == ([(0, 1)], 2, 2)
    while True:
        mo = model(*cfg)
        if mo is None:
            mo = cell_sweep(*cfg); ev += 1
        cfg, dn = mo
        T += dn
        if T >= max_steps:
            break
        if starts.get(T) != (list(cfg[0]), cfg[1], cfg[2]):
            print('BLANK MISMATCH at step', T, cfg, starts.get(T)); return False
        ok += 1
    if ok != len(starts) - 1:
        print('missed sweep starts', ok, len(starts)); return False
    print(f'blank run: all {ok} sweep starts after step 49 agree up to step {max_steps} ({ev} events cell by cell)')
    return True


def check_halt_example():
    r = cell_sweep([(0, 1), (3, 3), (1, 1)], 10, 2)
    print('items (0,1) (3,3) (1,1), q = 10:', r[0], 'after', r[1], 'steps')
    return r[0] == 'HALT'


if __name__ == '__main__':
    if sys.argv[1:] == ['check']:
        good = check_random() and check_blank() and check_halt_example()
        print('OK' if good else 'FAILED'); sys.exit(0 if good else 1)
    print(__doc__)
