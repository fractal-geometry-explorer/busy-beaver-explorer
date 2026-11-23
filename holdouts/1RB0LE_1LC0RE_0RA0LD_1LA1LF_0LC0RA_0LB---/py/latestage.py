"""The stage of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE--- after about 10^128 events: two chains around a new event cell.

At about 10^128 events (see defects.py) no full event comes any more: the cell where the head turns back in the
events has moved 17 cells to the right, into the chain.  The events of this stage ("visits") are the moments the
head is at that cell in state C on a 0.  Around it, at a visit:

    left of the head:   ... [L2] 1010 [L1] 1010 [L0] 101010101010101       (15 fixed cells next to the head)
    right of the head:  0 b 1  W1 c U1 a d W2 c U2 a d ...                  (tokens as in wordchain.py)

- left: base-3 words in the digits 100 = 0, 110 = 1, 010 = 2 of N (lowest digit next to the head), parted by the
  four cells 1010, so each word is shifted by one cell against the next.  L2 is what is left of the N of the earlier
  stages, still ending in 0^inf 1 0.  At the start of the stage the carries of N rebuild its lowest digits into
  L0 (10 digits) and L1 (4 digits); after that the widths stay fixed.
- right: the bit b (cell 2 after the head) and the words of the chain of wordchain.py from W1 on (W1 empty in this
  stage).

**The law of the stage (checked, see below).**  Visits come in pairs; over each pair, from a visit with b = 0:
  left:   L0 gets 16, and each word that wraps sends 2 to the next (base-3 words, so the left side is one counter
          that gains 16 * 2^k per pair, k + 1 words in all);
  right:  the word w0 = (b, U1) (b its lowest bit) gets 2, W2 gets 6, and each word that wraps sends 3 to the next,
          as in the chain law of wordchain.py.
So the whole stage is two counters run at once, and this script jumps over it like wordchain.py: at a visit with
b = 0 it takes the largest number of pairs such that no carry leaves either chain, writes that tape and runs cell
by cell to the next visit with b = 0.  It checks itself: SPOT random points of each jump are rebuilt and run cell
by cell for 3 pairs, each compared with the law.  It stops when a carry leaves the right chain and the visit cell
moves again (it says where to).

usage (from the repository root):
  python3 .../py/latestage.py check STEPS        reaches the stage, then checks the law on every pair of
                                                  visits of STEPS steps run cell by cell
  python3 .../py/latestage.py run [SPOT]         reaches the stage, then jumps until the visit cell moves
"""
import random
import sys

import defects as D
from prefixjump import parse_prefix
from wordchain import Sim, T2, add_n, jump, ptab, tape_left, tape_right, val

M = '1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---'
BLOCK = bytes([1, 0] * 7 + [1])
D3 = {(1, 0, 0): 0, (1, 1, 0): 1, (0, 1, 0): 2}
D3w = {0: (1, 0, 0), 1: (1, 1, 0), 2: (0, 1, 0)}
C = 2
TEST_START = None   # a test can set this to skip the 4-minute run to the stage


def reach_stage(tr):
    """Runs the defect simulator of defects.py (without its self-checks) until no full event comes within 10^8
    steps; returns the simulator there, the cell of the last full event and the number of events (about)."""
    s = Sim(tr)
    e, _ = s.run_to_event(10 ** 9)
    events = 1
    while True:
        n, nw, tok = e
        r = D.parse(tok)
        if r is not None:
            words, seps = r
            while True:
                j = D.longest(words, seps)
                if j > 0:
                    words = D.advance(words, seps, j)
                    n, nw = add_n(n, nw, j)
                    events += j
                st = D.step(words, seps)
                if st is None:
                    break
                words, seps = st
                n, nw = add_n(n, nw, 1)
                events += 1
            s.load(tape_left(n, nw), D.tape(words, seps))
        else:
            p = parse_prefix(tok)
            if p:
                j, w2 = jump(p[0])
                if j > 0:
                    n, nw = add_n(n, nw, j)
                    events += j
                    s.load(tape_left(n, nw), tape_right(w2) + p[1])
        cell = s.p
        e, _ = s.run_to_event(10 ** 8)
        events += 1
        if e in (None, 'HALT'):
            return s, cell, events, e


def run_to_visit(s, maxsteps):
    """Runs to the next visit (state C on a 0 at cell s.v, or at any cell if s.v is None, with BLOCK on its left
    and 0 ? 1 0 1 on its right): ('visit' | 'HALT' | None, steps)."""
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
        if (p == v or v is None) and st == C and t[p] == 0 and t[p - 15:p] == BLOCK and t[p + 1] == 0 \
                and t[p + 3] == 1 and t[p + 4] == 0 and t[p + 5] == 1:
            s.p, s.st = p, st
            return 'visit', k
    s.p, s.st = p, st
    return None, k


def find_visit_cell(s, steps=3 * 10 ** 6):
    """The cell with the most visit-shaped passes in the next STEPS steps (at least 100), or None."""
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
    best = max(hits, key=hits.get) if hits else None
    return best if best is not None and hits[best] >= 100 else None


def read_visit(s, cells=1 << 14):
    """(left words, whether the last one ends at the old top 0^inf 1 0, right words (w0, W2, U2, ...) up to the
    first defect, and the parse of the right side) at a visit, or None if it is not in the shape of the stage."""
    t, p = s.t, s.p
    left = []
    cur = []
    q = p - 16
    lo = max(4, p - cells)
    while q > lo:
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
    top = bool(cur) and cur[-1] == 2 and not any(t[max(0, q - 40):q + 1])   # its 0 1 0 reads as one more 2
    if top:
        cur = cur[:-1]
    left.append(cur)
    if len(left) < 2:
        return None
    end = min(len(t), p + cells)
    last = p + 2
    for j in range(p + 2, end):
        if t[j]:
            last = j
    R = ''.join('1' if t[j] else '0' for j in range(p + 2, last + 1))
    if len(R) % 2:
        R += '0'
    tok = ''.join(T2[R[j:j + 2]] for j in range(0, len(R), 2))
    if len(tok) < 3 or tok[0] not in 'cd' or tok[1] != 'c':
        return None
    r = D.parse('zad' + tok[1:])        # a dummy Z d, then W1 (empty here) c U1 a d W2 ...
    if r is None:
        return None
    words, seps = r
    if words[1]:
        return None
    f = D.first_defect(seps)
    if f is not None and f <= 2:
        return None
    pre = words[:f + 1] if f is not None else words
    chain = [[1 if tok[0] == 'd' else 0] + words[2]] + [list(x) for x in pre[3:]]
    return left, top, chain, (words, seps, f)


def write_visit(s, left, chain, rest):
    words, seps, f = rest
    t, p = s.t, s.p
    q = p - 16
    for w in left:
        for d in w:
            t[q - 2], t[q - 1], t[q] = D3w[d]
            q -= 3
        q -= 4
    w = [[0], []] + [chain[0][1:]] + chain[1:] + ([list(x) for x in words[f + 1:]] if f is not None else [])
    full = D.tape(w, seps)
    cells = '00' + ('11' if chain[0][0] else '01') + full[7:]
    for i, ch in enumerate(cells):
        t[p + i] = 1 if ch == '1' else 0


def give_right(chain, gifts):
    """The right words after adding gifts[i] to word i, each word that wraps sending 3 to the next; None if a
    carry leaves them."""
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


def add_right(chain, e):
    """The right words e pairs of visits on (from b = 0), or None if a carry leaves them."""
    return give_right(chain, {0: 2 * e, 1: 6 * e})


def add_left(left, e):
    """The left words e pairs of visits on, or None if a carry leaves them."""
    w = [list(x) for x in left]
    carry = 16 * e
    for i in range(len(w)):
        k = len(w[i])
        v = sum(d * 3 ** j for j, d in enumerate(w[i])) + carry
        out = v // 3 ** k
        v %= 3 ** k
        w[i] = [(v // 3 ** j) % 3 for j in range(k)]
        carry = 2 * out
    return None if carry else w


def longest(f):
    """The largest e with f(e) not None (f monotone), 0 if none."""
    if f(1) is None:
        return 0
    lo, hi = 1, 2
    while f(hi) is not None:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f(mid) is not None:
            lo = mid
        else:
            hi = mid
    return lo


def copy_sim(s):
    c = Sim(s.tr, 1)
    c.t = bytearray(s.t)
    c.p, c.st, c.lo, c.hi, c.v = s.p, s.st, s.lo, s.hi, s.v
    return c


def start(tr):
    s, cell, events, e = TEST_START(tr) if TEST_START else reach_stage(tr)
    if e == 'HALT':
        print('HALT before the stage')
        sys.exit()
    v = find_visit_cell(s)
    if v is None:
        print('no visit cell found')
        sys.exit()
    s.v = v
    print('%s: about 10^%d events from blank tape, then no full event; the visit cell is %d cells right of the '
          'last event cell' % (M, len(str(events)) - 1, v - cell))
    return s


def check(steps):
    """Every pair of consecutive visits against the law: from b = 0 the next visit has w0 + 1 and L0 + 16, from
    b = 1 it has w0 + 1 and W2 + 6."""
    tr = ptab(M)
    s = start(tr)
    tally = {}
    prev = None
    done = 0
    while done < steps:
        e, k = run_to_visit(s, min(10 ** 7, steps - done))
        done += k
        if e == 'HALT' or (e is None and done < steps):
            print('stopped:', e)
            break
        if e is None:
            break
        r = read_visit(s)
        cur = None if r is None else (r[0] if r[1] else r[0][:-1], r[2])
        if r is None:
            key = 'not in the shape of the stage'
        elif prev is None:
            key = None
        else:
            pl, pc = prev
            if pc[0][0] == 0:
                el, er = add_left(pl, 1), give_right(pc, {0: 1})
            else:
                el, er = [list(x) for x in pl], give_right(pc, {0: 1, 1: 6})
            if el is None or er is None:
                key = 'a carry leaves a chain'
            elif el == cur[0][:len(el)] and len(el) <= len(cur[0]) and er == cur[1]:
                key = 'by the law'
            else:
                key = 'MISMATCH'
        if key:
            tally[key] = tally.get(key, 0) + 1
        prev = cur
    print('%d steps of the stage: %s' % (done, tally))


def run(nspot):
    tr = ptab(M)
    rng = random.Random(1)
    s = start(tr)
    visits = 0
    stats = {'jumps': 0, 'visits run cell by cell': 0}
    checks = [0, 0]
    end = 'no halt'
    while True:
        e, _ = run_to_visit(s, 10 ** 7)
        if e != 'visit':
            if e == 'HALT':
                end = 'HALT'
            else:
                v = find_visit_cell(s)
                end = 'a carry left the right chain and the visit cell moved by %s cells' % (
                    'an unknown number of' if v is None else v - s.v)
            break
        visits += 1
        stats['visits run cell by cell'] += 1
        r = read_visit(s)
        if r is None:
            continue
        left, top, chain, rest = r
        if chain[0][0] != 0 or len(chain) < 2:
            continue
        lw = left if top else left[:-1]
        j = min(longest(lambda x: add_right(chain, x)), longest(lambda x: add_left(lw, x)))
        if j <= 0:
            continue
        for _ in range(nspot):
            e0 = rng.randrange(0, j)
            c = copy_sim(s)
            write_visit(c, add_left(lw, e0) + left[len(lw):], add_right(chain, e0), rest)
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
                rr = read_visit(c)
                checks[0] += 1
                if rr is None or rr[0][:len(lw)] != add_left(lw, e0 + q) or rr[2] != add_right(chain, e0 + q):
                    checks[1] += 1
                    break
        write_visit(s, add_left(lw, j) + left[len(lw):], add_right(chain, j), rest)
        visits += 2 * j
        stats['jumps'] += 1
    print('%s, the stage: about 10^%d visits (so at least that many more steps), %s; %s; left words %s; '
          'self-checks: %d pairs, %d mismatches' % (M, len(str(visits)) - 1, end, stats,
                                                     [len(x) for x in left], checks[0], checks[1]))


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check(int(sys.argv[2]))
    else:
        run(int(sys.argv[2]) if len(sys.argv) > 2 else 2)
