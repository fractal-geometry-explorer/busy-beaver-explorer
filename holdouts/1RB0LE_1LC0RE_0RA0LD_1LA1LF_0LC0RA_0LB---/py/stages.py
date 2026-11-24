"""The stages of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE--- after about 10^128 events, followed with a law fitted per stage.

latestage.py decodes the first stage after 10^128 events: the head turns back at a cell inside the chain (a visit:
state C on a 0 there), the left side is a chain of base-3 words parted by 1010 (each wrap sends 2), and the right
side is the binary chain (each wrap sends 3), with one cell b in front of it.  When a carry leaves the right chain
the turning cell moves further right, and the next stage has the same two chains, with more short words on the
left and with other gifts: what each visit adds to the first words.

This script follows the stages with one form of law and fits its numbers per stage.  At a visit:

    left:   base-3 words L0, L1, ... (digits 100/110/010, lowest next to the head), parted by 1010, then
            101010101010101 next to the head; the last word ends at the old top 0^inf 1 0;
    right:  0 b 1 then the tokens of the chain (W1 c U1 a d W2 ...); the first word w0 is b followed by the first
            word of the chain that is not empty (b its lowest bit), then the words after it.

A visit with b = 0 adds GL0 to L0 and gives GR0[i] to the i-th right word; a visit with b = 1 adds GL1 and GR1[i];
in both chains a word that wraps sends its factor (2 left, 3 right) to the next.  The numbers GL0, GL1, GR0, GR1 of
a stage are found from 40 consecutive visits run cell by cell (the smallest that fit every one of them), then every
visit run cell by cell is checked against them (a mismatch drops the law and the next 40 visits fit a new one).
Jumps go by pairs of visits from b = 0, as far as no carry leaves either chain; SPOT random points of each jump are
rebuilt and run cell by cell for 3 pairs and compared with the law.  So a fitted law is only used with checks:
the 40 visits it was fitted on, every later visit run cell by cell, and the spot checks.

usage (from the repository root):
  python3 .../py/stages.py run STAGES [SPOT]      from blank tape, follows STAGES stages after 10^128 events
"""
import itertools
import random
import sys

import defects as D
from latestage import C, D3, D3w, M, copy_sim, longest, reach_stage
from wordchain import T2, ptab, val

DUMP = None         # a file to write the tape to at each move of the turning cell
VERBOSE = False
TEST_START = None   # a test can set this to skip the 4-minute run to the stage


def run_to_visit(s, maxsteps):
    """Runs to the next visit at cell s.v (any cell if s.v is None): ('visit' | 'HALT' | None, steps)."""
    t, tr, v = s.t, s.tr, s.v
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
        if (p == v or v is None) and st == C and t[p] == 0 and t[p + 1] == 0 and t[p + 3] == 1:
            s.p, s.st = p, st
            return 'visit', k
    s.p, s.st = p, st
    return None, k


def find_visit_cells(s, steps=3 * 10 ** 6):
    """The cells with at least 100 visit-shaped passes in the next STEPS steps, most passes first."""
    v0, s.v = getattr(s, 'v', None), None
    hits = {}
    budget = steps
    while budget > 0:
        e, k = run_to_visit(s, budget)
        budget -= k
        if e != 'visit':
            break
        hits[s.p] = hits.get(s.p, 0) + 1
    s.v = v0
    return [c for c in sorted(hits, key=hits.get, reverse=True) if hits[c] >= 100]


def choose(s, prevB):
    """At the current turning cell s.v: the block length B (-1: the lowest digit of L0 ends at the turning cell
    itself; else the cells 1010...1 of length B) with which the left side reads down to the old top 0^inf 1 0, or
    failing that one with which it reads at all; None if none does within 20 visits."""
    loose = None
    for _ in range(20):
        if run_to_visit(s, 10 ** 7)[0] != 'visit':
            break
        for B in sorted([-1] + list(range(1, 41, 2)), key=lambda x: abs(x - prevB)):
            s.B = B
            r = read(s)
            if r is not None and r[1]:
                return B
            if r is not None and loose is None:
                loose = B
    return loose


def read(s, cells=1 << 14):
    """(left words, top, right words, rest) at a visit, or None."""
    t, p, B = s.t, s.p, s.B
    if B > 0 and t[p - B:p] != bytes([1, 0] * (B // 2) + [1]):
        return None
    left = []
    cur = []
    q = p - B - 1
    while q > 4:
        if (t[q - 3], t[q - 2], t[q - 1], t[q]) == (1, 0, 1, 0):
            left.append(cur)
            cur = []
            q -= 4
            continue
        d = D3.get((t[q - 2], t[q - 1], t[q]))
        if d is None:
            break
        cur.append(d)
        q -= 3
    top = bool(cur) and cur[-1] == 2 and not any(t[max(0, q - 40):q + 1])
    if top:
        cur = cur[:-1]
    left.append(cur)
    end = min(len(t), p + cells)
    last = p + 2
    for j in range(p + 2, end):
        if t[j]:
            last = j
    R = ''.join('1' if t[j] else '0' for j in range(p + 2, last + 1))
    if len(R) % 2:
        R += '0'
    tok = ''.join(T2[R[j:j + 2]] for j in range(0, len(R), 2))
    if len(tok) < 3 or tok[0] not in 'cd':
        return None
    r = D.parse('zad' + tok[1:])
    if r is None:
        return None
    words, seps = r
    f = D.first_defect(seps)
    pre = words[1:f + 1] if f is not None else words[1:]
    k = next((i for i, w in enumerate(pre) if w), None)
    if k is None:
        return None
    chain = [[1 if tok[0] == 'd' else 0] + pre[k]] + [list(x) for x in pre[k + 1:]]
    return left, top, chain, (words, seps, len(pre), k)


def write(s, left, chain, rest):
    words, seps, npre, k = rest
    t, p = s.t, s.p
    q = p - s.B - 1
    for w in left:
        for d in w:
            t[q - 2], t[q - 1], t[q] = D3w[d]
            q -= 3
        q -= 4
    pre = [[] for _ in range(k)] + [chain[0][1:]] + chain[1:]
    w = [[0]] + pre + [list(x) for x in words[1 + npre:]]
    full = D.tape(w, seps)
    cells = '00' + ('11' if chain[0][0] else '01') + full[7:]
    for i, ch in enumerate(cells):
        t[p + i] = 1 if ch == '1' else 0


def give_right(chain, gifts):
    w = [list(x) for x in chain]
    carry = 0
    for i in range(len(w)):
        k = len(w[i])
        v = val(w[i]) + gifts.get(i, 0) + carry
        out = v >> k
        v &= (1 << k) - 1
        w[i] = [(v >> j) & 1 for j in range(k)]
        carry = 3 * out
    return None if carry else w


def give_left(left, g):
    w = [list(x) for x in left]
    carry = g
    for i in range(len(w)):
        k = len(w[i])
        v = sum(d * 3 ** j for j, d in enumerate(w[i])) + carry
        out = v // 3 ** k
        v %= 3 ** k
        w[i] = [(v // 3 ** j) % 3 for j in range(k)]
        carry = 2 * out
    return None if carry else w


def lw_of(r):
    return r[0] if r[1] else r[0][:-1]


def predict(law, r):
    """(left words, right words) one visit after r by the law, or None."""
    b = r[2][0][0]
    gl, gr = law[b]
    el = give_left(lw_of(r), gl)
    er = give_right(r[2], gr)
    return None if el is None or er is None else (el, er)


def same(pred, r):
    lw = lw_of(r)
    return pred is not None and pred[0] == lw[:len(pred[0])] and len(pred[0]) <= len(lw) and pred[1] == r[2]


def fit(window):
    """The smallest gifts (GL, GR) for b = 0 and b = 1 that fit every transition of the window, or None."""
    law = {}
    for b in (0, 1):
        tr_ = [(x, y) for x, y in zip(window, window[1:]) if x[2][0][0] == b]
        if len(tr_) < 5:
            return None
        gl = next((g for g in range(0, 200) if all(give_left(lw_of(x), g) is not None
                                                   and give_left(lw_of(x), g) == lw_of(y)[:len(lw_of(x))]
                                                   for x, y in tr_)), None)
        if gl is None:
            return None
        gr = None
        for g in itertools.product(range(0, 65), range(0, 13), range(0, 13)):
            gd = {i: v for i, v in enumerate(g) if v}
            if all(give_right(x[2], gd) == y[2] for x, y in tr_):
                gr = gd
                break
        if gr is None:
            return None
        law[b] = (gl, gr)
    return law


def fits_soon(c, visits=400):
    """Whether 41 consecutive readable visits of the same widths, all fitting one law, come within VISITS visits."""
    window = []
    for _ in range(visits):
        if run_to_visit(c, 10 ** 6)[0] != 'visit':
            return False
        r = read(c)
        if r is None or (window and ([len(x) for x in lw_of(window[-1])] != [len(x) for x in lw_of(r)]
                                     or [len(x) for x in window[-1][2]] != [len(x) for x in r[2]])):
            window = [] if r is None else [r]
            continue
        window.append(r)
        if len(window) >= 41:
            if fit(window) is not None:
                return True
            window = []
    return False


def jump_to(law, r, e):
    """(left words, right words) e pairs of visits after r (b = 0), or None."""
    g0, g1 = law[0], law[1]
    el = give_left(lw_of(r), (g0[0] + g1[0]) * e)
    gifts = {}
    for d in (g0[1], g1[1]):
        for i, v in d.items():
            gifts[i] = gifts.get(i, 0) + v * e
    er = give_right(r[2], gifts)
    return None if el is None or er is None else (el, er)


def run(stages, nspot):
    tr = ptab(M)
    rng = random.Random(1)
    s, cell, events, e = (TEST_START or reach_stage)(tr)
    print('%s: about 10^%d events from blank tape (defects.py), then no full event' % (M, len(str(events)) - 1))
    visits = 0
    checks = [0, 0]
    stage = 0
    end = 'no halt'
    log = []
    while stage < stages:
        if DUMP:
            nz = [i for i in range(len(s.t)) if s.t[i]]
            with open(DUMP, 'w') as fh:
                fh.write('%d %d\n%s\n' % (s.p - nz[0] + 10, s.st, ''.join('1' if x else '0' for x in s.t[nz[0] - 10:nz[-1] + 10])))
        prevB = getattr(s, 'B', None) or 15
        v0 = getattr(s, 'v', None)
        found = None
        cands = []
        for v in find_visit_cells(s)[:6]:
            c = copy_sim(s)
            c.v = v
            B = choose(c, prevB)
            if B is not None:
                c.B = B
                cands.append((v, B, fits_soon(c)))
        # a cell whose tape fits a law of the form soon, else the first that reads
        good = [x for x in cands if x[2]] or cands
        if good:
            found, s.B = good[0][0], good[0][1]
            s.v = found
        if found is None:
            end = 'no turning cell found where the tape reads as two chains'
            break
        stage += 1
        moved = found - (v0 if v0 is not None else cell)
        st = {'block': s.B, 'jumps': 0, 'visits run cell by cell': 0, 'laws fitted': 0, 'visits off the law': 0}
        law = None
        window = []
        prev = None
        v_start = visits
        unread = 0
        while True:
            ev, _ = run_to_visit(s, 10 ** 7)
            if ev != 'visit':
                if ev == 'HALT':
                    end = 'HALT'
                break
            visits += 1
            st['visits run cell by cell'] += 1
            if law is None and st['visits run cell by cell'] > 5000:
                end = 'no law of the given form fits this stage'
                break
            r = read(s)
            if VERBOSE and st['visits run cell by cell'] % 200 == 0:
                print('  %d visits run cell by cell, law %s, read %s' % (st['visits run cell by cell'], law, r is not None))
                sys.stdout.flush()
            if r is None:
                prev, window = None, []
                unread += 1
                if unread > 2000:   # the tape around the cell no longer reads: look for the turning cell again
                    break
                continue
            unread = 0
            if law is not None and prev is not None and not same(predict(law, prev), r):
                st['visits off the law'] += 1
                law, window = None, []
            prev = r
            if law is None:
                if window and ([len(x) for x in lw_of(window[-1])] != [len(x) for x in lw_of(r)]
                               or [len(x) for x in window[-1][2]] != [len(x) for x in r[2]]):
                    window = []
                window.append(r)
                if len(window) >= 41:
                    law = fit(window)
                    window = []
                    if law is not None:
                        st['laws fitted'] += 1
                        st['law'] = law
                continue
            if r[2][0][0] != 0:
                continue
            j = longest(lambda x: jump_to(law, r, x))
            if j <= 0:
                continue
            for _ in range(nspot):
                e0 = rng.randrange(0, j)
                c = copy_sim(s)
                c.B = s.B
                a = jump_to(law, r, e0)
                write(c, a[0] + r[0][len(lw_of(r)):], a[1], r[3])
                for q in range(1, 4):
                    if e0 + q > j:
                        break
                    ok = True
                    for _v in range(2):
                        ee, _ = run_to_visit(c, 10 ** 7)
                        if ee != 'visit':
                            ok = False
                            break
                    if not ok:
                        break
                    rr = read(c)
                    checks[0] += 1
                    want = jump_to(law, r, e0 + q)
                    if rr is None or not same(want, rr):
                        checks[1] += 1
                        break
            if VERBOSE:
                print('  jump of 10^%d pairs, left widths %s, right widths %s, checks %s'
                      % (len(str(j)) - 1, [len(x) for x in lw_of(r)][:6], [len(x) for x in r[2]][:6], checks))
                sys.stdout.flush()
            a = jump_to(law, r, j)
            write(s, a[0] + r[0][len(lw_of(r)):], a[1], r[3])
            visits += 2 * j
            st['jumps'] += 1
            prev = None
        log.append((stage, moved, len(str(visits - v_start)) - 1, st, [len(x) for x in prev[0]] if prev else None))
        print('stage %d: the turning cell moved %d cells; about 10^%d visits in it; %s' % log[-1][:4])
        sys.stdout.flush()
        if end != 'no halt':
            break
    print('%s after 10^128 events: %d stages, about 10^%d visits (so at least that many more steps), %s; '
          'self-checks %d pairs, %d mismatches' % (M, stage, len(str(visits)) - 1, end, checks[0], checks[1]))


if __name__ == '__main__':
    run(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 2)
