"""The stages of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE--- after about 10^128 events, followed with the law proved in
Lean (`chain_event` in holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---/lean/Stage.lean) instead of fitted gifts.

The turning points of a stage (state C on a 0 at one cell, see stages.py) come two per event: the stages are events
of the chain law with the word Z empty, and with a chain of base-3 words on the left instead of the single counter N.
At an event the head is in state A on a 0 (the event cell e), and

    left of e:   0, then the left units (lenc): digits 100/110/010, separators 1010, the top 10 and blank tape;
    right of e:  Z (digits 0010/1010) then (11 [Q] 01 [P] 10)* 11 [Q] 01 [R], then any tape.

`chain_event` gives the next event for every such tape: the left units get one increment (`linc`) and the right
side moves by `evNext` (Z + 1; with Z empty one unit into the chain, `dU`).  This script ports those functions
from Stage.lean and Layers.lean, and

- at each stage, finds the event cell (the cell right of the turning cell of stages.py), reads every event run cell by
  cell in this layout, and checks it against the event before it by the ported functions;
- jumps over many events at once by adding to the words (the left words: +1 per event, a wrap sends 2; the right:
  Z + 1 per event, a wrap sends 3), as far as no carry leaves the right chain and the top left word does not grow;
  this is the ported law iterated;
- checks itself: random points of each jump are rebuilt and run cell by cell for 3 events, against the ported law;
- at a wrap of a half-digit item `11 [Q] 0011 [Q2] 01 [P2]` (Junction.lean, `chain_event_junction`), runs the event
  cell by cell and checks it against the ported `evNextJ` (`lawJ`);
- runs every change of stage (a carry leaving R, where `evNext` is none) cell by cell.

So the step from one event to the next is proved; what is trusted is that the run's tapes have this layout (each one
read off the tape), the port of the Lean functions, and the jump arithmetic (the law iterated).

usage (from the repository root):
  python3 .../py/stage_law.py run STAGES [SPOT]       from blank tape, follows STAGES stages after 10^128 events
"""
import random
import sys

from latestage import C, M, copy_sim, longest, reach_stage
from stages import find_visit_cells
from wordchain import ptab

A = 0
TEST_START = None
MAX_RETURNS = 500

# ---- the Lean functions (Layers.lean: incB, pInc, pUnit, qInc, qUnit, dU, evNext; Stage.lean: linc) ----


def incB(w):
    if not w:
        return [], True
    if w[0] == 0:
        return [1] + w[1:], False
    r, c = incB(w[1:])
    return [0] + r, c


def pInc(k, p, s):
    r, c = incB(p)
    if not c:
        return r, s
    s2 = k(s)
    return None if s2 is None else (r, s2)


def pUnit(k, p, s):
    for _ in range(3):
        x = pInc(k, p, s)
        if x is None:
            return None
        p, s = x
    return p, s


def qInc(k, q, p, s):
    r, c = incB(q)
    if not c:
        return r, p, s
    x = pUnit(k, p, s)
    return None if x is None else (r, x[0], x[1])


def qUnit(k, q, p, s):
    for _ in range(3):
        x = qInc(k, q, p, s)
        if x is None:
            return None
        q, p, s = x
    return q, p, s


def qAdd3(q):
    """Stage.lean `qAdd3`: three increments of a non-empty word, None if one of them wraps."""
    if not q:
        return None
    for _ in range(3):
        q, c = incB(q)
        if c:
            return None
    return q


def dU(its, l):
    """Layers.lean `dU`; with an open last item l = (Q, None) (Q followed by any tape), Stage.lean `dUo`."""
    if not its and l[1] is None:
        q = qAdd3(l[0])
        return None if q is None else ([], (q, None))
    if not its:
        x = qUnit(lambda s: None, l[0], l[1], ())
        return None if x is None else ([], (x[0], x[1]))
    i = its[0]
    x = qUnit(lambda s: dU(s[0], s[1]), i[0], i[1], (its[1:], l))
    return None if x is None else ([(x[0], x[1])] + x[2][0], x[2][1])


def evNext(z, its, l):
    r, c = incB(z)
    if not c:
        return r, its, l
    u = dU(its, l)
    return None if u is None else (r, u[0], u[1])


def linc(us):
    """One increment of the left units (Stage.lean `linc`): units 0, 1, 2 (digits), 'sep', 'top', 'rest' (any
    tape); None when a carry reaches 'rest'."""
    u = us[0]
    if u == 0 or u == 1:
        return [u + 1] + us[1:]
    if u == 2:
        r = linc(us[1:])
        return None if r is None else [0] + r
    if u == 'sep':
        r = linc(us[1:])
        r = None if r is None else linc(r)
        return None if r is None else ['sep'] + r
    if u == 'top':
        return [0, 'top']
    return None


def law(ev):
    us, z, its, l = ev
    r = evNext(z, its, l)
    u = linc(us)
    return None if r is None or u is None else (u, r[0], r[1], r[2])


# ---- reading and writing an event ----

ZD = {(0, 0, 1, 0): 0, (1, 0, 1, 0): 1}
QD = {(0, 0, 0, 1): 0, (0, 1, 0, 1): 1}
PD = {(1, 0, 0, 0): 0, (1, 0, 1, 0): 1}
ZW = {v: k for k, v in ZD.items()}
QW = {v: k for k, v in QD.items()}
PW = {v: k for k, v in PD.items()}
LW = {0: (0, 1), 1: (1, 1), 2: (1, 0)}   # a digit's cells left of its 0 cell, leftwards


def read(s, e):
    """(units, Z, items, last item) of the event at cell e, or None if the tape is not in the layout."""
    t = s.t
    if t[e] != 0 or t[e - 1] != 0:
        return None
    lo = t.find(1)
    us = []
    q = e - 1
    while True:
        if t[q] != 0:       # the last unit is not followed by a 0 cell: the tape from its own 0 cell on is 'rest'
            if not us:
                return None
            us[-1] = 'rest'
            break
        if q - 1 == lo and t[q - 1] == 1:
            us.append('top')
            break
        if q - 3 < lo:
            us.append('rest')
            break
        x = (t[q - 1], t[q - 2])
        if x == (1, 0) and t[q - 3] == 1:
            us.append('sep')
            q -= 4
        elif x == (0, 1):
            us.append(0)
            q -= 3
        elif x == (1, 1):
            us.append(1)
            q -= 3
        elif x == (1, 0):
            us.append(2)
            q -= 3
        else:
            us.append('rest')
            break
    j = e + 1
    z = []
    while tuple(t[j:j + 4]) in ZD:
        z.append(ZD[tuple(t[j:j + 4])])
        j += 4
    items = []
    while True:
        if tuple(t[j:j + 2]) != (1, 1):
            return None if not items else (us, z, items[:-1], items[-1])
        j += 2
        qw = []
        while tuple(t[j:j + 4]) in QD:
            qw.append(QD[tuple(t[j:j + 4])])
            j += 4
        if tuple(t[j:j + 2]) != (0, 1):
            if qw:      # an open last item: 11 [Q] and then any tape (Stage.lean `encO`)
                return us, z, items, (qw, None)
            return None if not items else (us, z, items[:-1], items[-1])
        j += 2
        pw = []
        while tuple(t[j:j + 4]) in PD:
            pw.append(PD[tuple(t[j:j + 4])])
            j += 4
        items.append((qw, pw))
        if tuple(t[j:j + 4]) == (1, 0, 1, 1):
            j += 2
            continue
        return us, z, items[:-1], items[-1]


def chain_at(t, j):
    """(items, last) of a chain of the grammar starting with `11` at cell j and ending in a closed R, or None."""
    items = []
    while True:
        if tuple(t[j:j + 2]) != (1, 1):
            return None
        j += 2
        qw = []
        while tuple(t[j:j + 4]) in QD:
            qw.append(QD[tuple(t[j:j + 4])])
            j += 4
        if tuple(t[j:j + 2]) != (0, 1):
            return None
        j += 2
        pw = []
        while tuple(t[j:j + 4]) in PD:
            pw.append(PD[tuple(t[j:j + 4])])
            j += 4
        items.append((qw, pw))
        if tuple(t[j:j + 4]) == (1, 0, 1, 1):
            j += 2
            continue
        return items[:-1], items[-1]


def read_j(s, e):
    """The event at cell e with a half-digit item (Junction.lean `encJ`): (units, Z, items, w) with
    w = ('unh', Q, b, Q2, P2, (rest, last)), the junction `0011` (b = 0) or `0111` (b = 1) after Q and the item
    (Q2, P2) followed by `10` and the rest of the chain; None if the tape does not read so."""
    r = read(s, e)
    if r is None:
        return None
    us, z, its, l = r
    t = s.t
    j = e + 1 + 4 * len(z) + sum(6 + 4 * len(q) + 4 * len(p) for q, p in its) + 2 + 4 * len(l[0])
    if l[1] is None and tuple(t[j:j + 4]) == (0, 0, 1, 1):
        b = 0
    elif l[1] == [] and tuple(t[j:j + 4]) == (0, 1, 1, 1):
        b = 1
    else:
        return None
    c = chain_at(t, j + 2)
    if c is None or not c[0]:
        return None
    (q2, p2), rest = c[0][0], c[0][1:]
    return us, z, its, ('unh', l[0], b, q2, p2, (rest, c[1]))


# ---- the law with a half-digit item (Junction.lean: jInc, jUnit, dUJ, evNextJ) ----


def kC(s):
    return dU(s[0], s[1])


def jInc(w):
    if w[0] == 'hld':
        _, q, p, s = w
        if not q:
            return None
        x = qInc(kC, q, p, s)
        return None if x is None else ('hld', x[0], x[1], x[2])
    _, q, b, q2, p2, s = w
    q1, c = incB(q)
    if not c:
        return ('unh', q1, b, q2, p2, s)
    if not b:
        return ('unh', q1, 1, q2, p2, s)
    if not q2:
        return None
    x = qInc(kC, q2, p2, s)
    if x is None:
        return None
    y = qInc(kC, x[0], x[1], x[2])
    return None if y is None else ('hld', q1 + [0] + y[0], y[1], y[2])


def jUnit(w):
    for _ in range(3):
        w = jInc(w)
        if w is None:
            return None
    return w


def dUJ(its, w):
    if not its:
        x = jUnit(w)
        return None if x is None else ([], x)
    x = qUnit(lambda s: dUJ(s[0], s[1]), its[0][0], its[0][1], (its[1:], w))
    return None if x is None else ([(x[0], x[1])] + x[2][0], x[2][1])


def lawJ(ev):
    us, z, its, w = ev
    u = linc(us)
    zz, c = incB(z)
    if c:
        x = dUJ(its, w)
        if x is None:
            return None
        its, w = x
    return None if u is None else (u, zz, its, w)


def norm(ev):
    """A healed half-digit item read as the chain of the grammar it is (Junction.lean `encJ_hld`)."""
    us, z, its, w = ev
    if len(w) == 4 and w[0] == 'hld':
        _, q, p, (rest, l) = w
        return us, z, its + [(q, p)] + rest, l
    return ev


def write(s, e, ev):
    """Writes the event ev at cell e, over a tape of the same widths."""
    us, z, its, l = ev
    t = s.t
    q = e - 1
    for u in us:
        if u in ('top', 'rest'):
            break
        if u == 'sep':
            t[q - 3:q + 1] = bytes([1, 0, 1, 0])
            q -= 4
        else:
            a, b = LW[u]
            t[q], t[q - 1], t[q - 2] = 0, a, b
            q -= 3
    j = e + 1
    for d in z:
        t[j:j + 4] = bytes(ZW[d])
        j += 4
    for k, (qw, pw) in enumerate(its + [l]):
        j += 2
        for d in qw:
            t[j:j + 4] = bytes(QW[d])
            j += 4
        if pw is None:
            break
        j += 2
        for d in pw:
            t[j:j + 4] = bytes(PW[d])
            j += 4
        if k < len(its):
            j += 2


# ---- jumps: the law iterated ----


def words_of(us):
    ws, cur = [], []
    for u in us:
        if u in ('sep', 'top', 'rest'):
            ws.append(cur)
            cur = []
        else:
            cur.append(u)
    return ws


def units_of(ws, end):
    us = []
    for i, w in enumerate(ws):
        us += w
        us.append('sep' if i < len(ws) - 1 else end)
    return us


def add_left(us, n):
    """n increments of the left units (each wrap of a word sends 2), None if a carry would leave the last word."""
    ws = [list(w) for w in words_of(us)]
    carry = n
    for i, w in enumerate(ws):
        k = len(w)
        v = sum(d * 3 ** j for j, d in enumerate(w)) + carry
        out = v // 3 ** k
        v %= 3 ** k
        ws[i] = [(v // 3 ** j) % 3 for j in range(k)]
        carry = 2 * out
    return None if carry else units_of(ws, us[-1])


def add_right(z, its, l, n):
    """n events on the right: Z + n, every wrap sends 3 to the next word; None if a carry leaves R."""
    ws = [z] + [w for it in its + [l] for w in it if w is not None]
    out = [list(w) for w in ws]
    carry = n
    for i, w in enumerate(out):
        k = len(w)
        v = sum(d << j for j, d in enumerate(w)) + carry
        c = v >> k
        v &= (1 << k) - 1
        out[i] = [(v >> j) & 1 for j in range(k)]
        carry = 3 * c
    if carry:
        return None
    pairs = [(out[1 + 2 * i], out[2 + 2 * i]) for i in range(len(its))]
    last = (out[-1], None) if l[1] is None else (out[-2], out[-1])
    return out[0], pairs, last


def jump(ev, n):
    us, z, its, l = ev
    a = add_left(us, n)
    b = add_right(z, its, l, n)
    return None if a is None or b is None else (a, b[0], b[1], b[2])


# ---- running ----


def run_to_event(s, e, maxsteps):
    """Runs until the head is in state A on a 0 at cell e: 'event' | 'HALT' | None."""
    t, tr = s.t, s.tr
    p, st = s.p, s.st
    k = 0
    while k < maxsteps:
        x = tr.get((st, t[p]))
        if x is None:
            s.p, s.st = p, st
            return 'HALT', k
        t[p] = x[0]
        p += x[1]
        st = x[2]
        k += 1
        if p == e and st == A and t[p] == 0:
            s.p, s.st = p, st
            return 'event', k
    s.p, s.st = p, st
    return None, k


def next_event(s, e, budget=10 ** 7):
    """The next event at cell e that reads in the layout: (kind, reading)."""
    while True:
        ev, k = run_to_event(s, e, budget)
        if ev != 'event':
            return ev, None
        budget -= k
        r = read(s, e)
        if r is not None:
            return 'event', r


def after_chain(s, e, ev, n=120):
    """The first tokens (z = 00, a = 10, c = 01, d = 11) after the last word of the chain read at the event ev."""
    if ev is None:
        return '?'
    us, z, its, l = ev
    j = e + 1 + 4 * len(z)
    for k, (q, p) in enumerate(its + [l]):
        j += 2 + 4 * len(q) if p is None else 4 + 4 * len(q) + 4 * len(p) + (2 if k < len(its) else 0)
    names = {(0, 0): 'z', (1, 0): 'a', (0, 1): 'c', (1, 1): 'd'}
    return ''.join(names[(s.t[i], s.t[i + 1])] for i in range(j, j + 2 * n, 2))


def good_cell(s, e):
    """Whether two consecutive events at cell e soon read in the layout and follow the law (tried on a copy)."""
    c = copy_sim(s)
    prev = None
    for _ in range(200):
        ev, r = next_event(c, e, 10 ** 6)
        if ev != 'event':
            return False
        if prev is not None and law(prev) == r:
            return True
        prev = r
    return False


def find_event_cell(s, prefer=None, tries=30):
    """The cell right of a turning cell where two consecutive events read in the layout and follow the law: PREFER
    (the last event cell) if it still is one, else the run goes on cell by cell (3·10^6 steps a try) until one is
    found; None after TRIES tries."""
    if prefer is not None and good_cell(s, prefer):
        return prefer
    for _ in range(tries):
        for v in find_visit_cells(s)[:6]:
            if good_cell(s, v + 1):
                return v + 1
    return None


def run(stages, nspot):
    tr = ptab(M)
    rng = random.Random(1)
    s, cell, events, e0 = (TEST_START or reach_stage)(tr)
    print('%s: about 10^%d events from blank tape (defects.py), then no full event' % (M, len(str(events)) - 1))
    total = 0           # events covered after the stage starts
    by_cell = 0         # consecutive pairs of events run cell by cell and checked against the law
    checks = [0, 0]     # spot-check events, mismatches
    mism = 0
    jpairs = jmism = 0  # events at a wrap of a half-digit item, checked against Junction.lean
    unread = 0
    stage = 0
    resumes = 0
    in_stage = 0
    shown = None
    e = None
    end = 'no halt'
    while stage < stages:
        e_prev = e
        e = find_event_cell(s, e)
        if e is None:
            end = 'no event cell found where the tape reads in the layout'
            break
        if e == e_prev:
            resumes += 1        # a carry reached the end of a chain, and the run came back to the same cell
            in_stage += 1
            if in_stage > MAX_RETURNS:
                end = ('stopped: %d carries in a row left the chain at the same cell (each crossing run cell by cell); '
                       'the tape after the chain: %s' % (in_stage - 1, after_chain(s, e, prev)))
                break
        else:
            stage += 1
            in_stage = 0
        prev = None
        n_stage = 0
        while True:
            ev, r = next_event(s, e)
            if ev != 'event':
                if ev == 'HALT':
                    end = 'HALT'
                break
            total += 1
            n_stage += 1
            if prev is not None:
                want = law(prev)
                if want is None:
                    unread += 1     # the carry left R at the event before: the change of stage, run cell by cell
                elif want != r:
                    mism += 1
                    print('  mismatch at stage %d' % stage)
                else:
                    by_cell += 1
            prev = r
            stop = False
            while law(r) is None:
                # a wrap at a half-digit item: one event by the law of Junction.lean, run cell by cell and checked
                rj = read_j(s, e)
                want = lawJ(rj) if rj is not None else None
                if want is None:
                    stop = True     # a carry leaves R at this event: the stage ends, and the run goes on cell by cell
                    break
                ev, r = next_event(s, e)
                if ev != 'event':
                    if ev == 'HALT':
                        end = 'HALT'
                    stop = True
                    break
                total += 1
                n_stage += 1
                got = read_j(s, e)
                if norm(want) == (got if got is not None else r):
                    jpairs += 1
                else:
                    jmism += 1
                    print('  mismatch at a half-digit item, stage %d' % stage)
                prev = r
            if stop:
                break
            j = longest(lambda x: jump(r, x))
            if j <= 1:
                continue
            j -= 1
            for _ in range(nspot):
                k0 = rng.randrange(0, j)
                c = copy_sim(s)
                a = jump(r, k0)
                write(c, e, a)
                for q in range(1, 4):
                    if k0 + q > j:
                        break
                    ee, rr = next_event(c, e)
                    checks[0] += 1
                    if ee != 'event' or rr != jump(r, k0 + q):
                        checks[1] += 1
                        break
            write(s, e, jump(r, j))
            total += j
            prev = jump(r, j)
        if end != 'no halt':
            break
        if stage == shown and resumes % 100:
            continue
        shown = stage
        print('stage %d (%d returns): event cell %d, %d events run cell by cell, about 10^%d events in all so far; '
              'left words %s, right words %s; pairs by the law %d, off it %d; self-checks %d, mismatches %d'
              % (stage, resumes, e, n_stage, len(str(total)) - 1,
                                                  [len(w) for w in words_of(prev[0])][:6] if prev else None,
                                                  [len(w) for it in prev[2] + [prev[3]] for w in it if w is not None][:8] if prev else None,
                 by_cell, mism, checks[0], checks[1]))
        if jpairs or jmism:
            print('  events at wraps of a half-digit item, by Junction.lean: %d, off it %d' % (jpairs, jmism))
        sys.stdout.flush()
    print('%s after 10^128 events: %d stages (event cells), %d returns to the same cell after a carry left a chain, '
          'about 10^%d events (so at least that many more steps), %s; %d pairs of events run cell by cell follow '
          'the law, %d do not; %d events at wraps of a half-digit item follow Junction.lean, %d do not; '
          'self-checks %d events, %d mismatches'
          % (M, stage, resumes, len(str(total)) - 1, end, by_cell, mism, jpairs, jmism, checks[0], checks[1]))


if __name__ == '__main__':
    sys.setrecursionlimit(100000)   # linc recurses once per left unit (a top word of about 1000 digits)
    run(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 2)
