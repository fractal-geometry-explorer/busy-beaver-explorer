"""What a change of stage hands on, for 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE--- after about 10^128 events.

Inside a stage every event follows the chain law of Stage.lean (`chain_event`): with Z empty the event sends one unit
into the first item, a unit is three increments of Q, a wrap of Q is three increments of P, and a wrap of P sends a
unit into the next item.  A stage ends at the event where a carry leaves R, the last word.  This script follows those
events (the changes of stage) cell by cell and checks them against the rule below.

**What happens.**  The change of stage is a single event (about 8,000 to 12,000 steps here).  The unit cascade reaches
the blank tape after R in state B or E and comes back in state C: R is all ones, so the a/z stream of R and the blank
is in the even case (`vb_even` in Stream.lean).  That return in C (the *C-wave*) runs back left through every item to
the event cell.

**The rule (trusted, checked here).**  At the moment the carry leaves R, every item k is in the middle of one unit:
the unit's a-th increment of Q (a = 1, 2, 3) wrapped and sent three increments into P, and the b-th of those (b = 1, 2,
3) wrapped P and sent the unit on (for the last item: the carry out of R).  `phases` computes (a, b) for every item by
running the chain law.  After the event:

- the cells `11` that start item k have moved by one token: 2 cells right if a = 1, 2 cells left if a >= 2;
- the cells `01` between Q and P of item k have moved 2 cells right if b = 1, 2 cells left if b >= 2;
- so the widths change by at most one digit, and every word is rewritten: Q gets 2 if a >= 2 and 0 if a = 1, P gets
  2 if b >= 2 and 0 if b = 1, with the carries of the chain law (a word that wraps sends 3 to the next word); R keeps
  its width and only its top digit is 1.

The grammar reads the same tape at a one-cell shift (a Q word is a P word one cell to the left, and the other way
round), so when the event cell moves by an odd number of cells the same tape is read with Q and P swapped; the rule
is checked on the cells, not on a reading.

The rule covers item 0 (the first item after the event cell) too: its `11` and `01` move the same way and its carry
goes into item 1, but its cells are not compared here, because what is left of it belongs to the new event cell.  A
word may become empty (width 0) after the change; the rule still holds there.

Not covered yet, and counted apart: a word that is empty before the change (there widths can become negative and two
items merge, as the half-digit item of Junction.lean does), item 0 with a word that becomes empty, the changes where
the head goes past the end of R before it comes back, those where the new event cell lies in item 1, the left side and
the new event cell, and changes of stage with Z not empty.

Result (`check 150`): 186 changes of stage with Z empty; the rule covers 116 and all 116 match it cell by cell; set
apart 65 at an empty word, 4 where the head goes past R, 1 where the new event cell lies in item 1.

**After the C-wave (`transient`).**  When the C-wave has left item 1 for the last time, what is left of the change is
local: the head works on item 0 and on the left words next to the event cell, and never more than 77 cells left of
it, until the first event at the new event cell.  There Z is empty and the first item starts on the next cell (`11`),
in all 186 changes of stage with Z empty.  The head crosses into the event cell from the right in a few patterns of
states (D C D C D, A, E C E C, A A, ...).  The halting state F is entered 1,381 times in these changes and always on a 0.

**The new first item (`transient`, `rules`).**  Which rule applies depends on the state in which the head first
crosses into the event cell from the right after the C-wave:

- E (36 changes): the event ends as an ordinary one.  The event cell stays, the left words get exactly one
  increment (`linc`), and item 0 keeps its widths with Q = 3 - a and P = 3 - b, as if the unit had gone on in item 0
  alone and its carry into item 1 had been dropped.  26 of 26 where the P of item 0 and the Q of item 1 are not
  empty (10 at such an empty word are set apart).
- D (a >= 2) with the event cell 2 cells left, and A (a = 1) with it 2 cells right: item 0 is rewritten as an item
  of the C-wave (its `11` moved 2 cells, Q = 2 or 0, P = 2 if b >= 2 and 0 if b = 1).  37 of 37 and 21 of 21.
- Open: D with the event cell 6 cells left (29: item 0 takes in the two nearest left digits) or farther (25), A with
  the event cell elsewhere (37, from 61 cells left to 20 right), and the left words in the D and A cases.

Result (`transient 150`): 186 changes of stage with Z empty (with or without empty words); farthest left -77; Z
empty and `11` right of the new event cell in 186 of 186; F on a 1: 0 of 1,381; rules: E 26 of 26, D 37 of 37,
A 21 of 21 (84 changes), the other 102 not covered yet.

usage (from the repository root):
  python3 .../py/stage_change.py check STAGES     follows STAGES stages from about 10^128 events and checks every
                                                  change of stage with Z empty against the rule, cell by cell
  python3 .../py/stage_change.py transient STAGES what the head does after the C-wave, at every change of stage
                                                  with Z empty
"""
import sys

from latestage import copy_sim, longest, reach_stage
from stage_law import A, M, QW, PW, evNext, find_event_cell, incB, jump, law, linc, next_event, read, read_j, write
from wordchain import ptab


def val(w):
    return sum(d << i for i, d in enumerate(w))


class _Over(Exception):
    pass


def phases(items):
    """(a, b) for every item at the event where the carry leaves R, by the chain law; None if no carry leaves R."""
    items = [(list(q), list(p)) for q, p in items]
    st = [None] * len(items)

    def unit(k):
        for a in range(1, 4):
            q, p = items[k]
            q, c = incB(q)
            items[k] = (q, p)
            if c:
                for b in range(1, 4):
                    q, p = items[k]
                    p, c2 = incB(p)
                    items[k] = (q, p)
                    if c2:
                        st[k] = (a, b)
                        if k + 1 == len(items):
                            raise _Over()
                        unit(k + 1)
    try:
        unit(0)
    except _Over:
        return st
    return None


def separators(e, ev):
    """For every item: the cell of its `11`, the cell of its `01`, and its words."""
    us, z, its, l = ev
    j = e + 1 + 4 * len(z)
    out = []
    for q, p in its + [l]:
        out.append((j, j + 2 + 4 * len(q), q, p))
        j += 6 + 4 * len(q) + 4 * len(p)
    return out


def predict(e, ev):
    """The cells of items 1, 2, ... and R after the change of stage, by the rule; (None, why) where it does not apply."""
    its = ev[2] + [ev[3]]
    st = phases(its)
    if st is None:
        return None, 'no carry leaves R'
    if any(not q or not p for q, p in its[:-1]):
        return None, 'an empty word'
    sep = separators(e, ev)
    m = len(its)
    s = [(2 if st[k][0] == 1 else -2) for k in range(m)]
    c = [(2 if st[k][1] == 1 else -2) for k in range(m)]
    words = []
    for k in range(m):
        s0, c0 = sep[k][0] + s[k], sep[k][1] + c[k]
        qw = (c0 - s0 - 2) // 4
        pw = (sep[k + 1][0] + s[k + 1] - c0 - 4) // 4 if k + 1 < m else len(its[k][1])
        if min(qw, pw) < (1 if k == 0 else 0):
            return None, 'an empty word'
        words.append((s0, qw, 2 if st[k][0] >= 2 else 0, c0, pw, 2 if st[k][1] >= 2 else 0))
    flat = []
    for w in words:
        flat += [(w[1], w[2]), (w[4], w[5])]
    vals, carry = [], 0
    for width, add in flat:
        v = add + carry
        carry = 3 * (v >> width)
        vals.append(v & ((1 << width) - 1))
    if flat[-1][0]:
        vals[-1] |= 1 << (flat[-1][0] - 1)
    cells = {}
    for k, (s0, qw, _, c0, pw, _) in enumerate(words):
        if k == 0:
            continue
        qv, pv = vals[2 * k], vals[2 * k + 1]
        cells[s0] = cells[s0 + 1] = 1
        for i in range(qw):
            for j, b in enumerate(QW[(qv >> i) & 1]):
                cells[s0 + 2 + 4 * i + j] = b
        cells[c0], cells[c0 + 1] = 0, 1
        for i in range(pw):
            for j, b in enumerate(PW[(pv >> i) & 1]):
                cells[c0 + 2 + 4 * i + j] = b
        if k + 1 < m:
            cells[c0 + 2 + 4 * pw], cells[c0 + 3 + 4 * pw] = 1, 0
    return cells, None


def check(stages):
    tr = ptab(M)
    s, cell, events, e0 = reach_stage(tr)
    print('%s: about 10^%d events from blank tape (defects.py)' % (M, len(str(events)) - 1))
    e, stage = None, 0
    tally = {'match': 0, 'differ': 0}
    while stage < stages:
        ep = e
        e = find_event_cell(s, e)
        if e is None:
            print('no event cell found')
            break
        if e != ep:
            stage += 1
        while True:
            ev, r = next_event(s, e)
            if ev != 'event':
                print(ev)
                return
            if law(r) is None:
                if evNext(r[1], r[2], r[3]) is None and not r[1] and read_j(s, e) is None:
                    cells, why = predict(e, r)
                    if cells is None:
                        tally[why] = tally.get(why, 0) + 1
                    else:
                        c = copy_sim(s)
                        v = find_event_cell(copy_sim(c), e)
                        t, steps, out, end = c.t, 0, False, max(cells)
                        while steps < 200000:     # the change of stage, cell by cell, to the first event at the new cell
                            y = c.tr[(c.st, t[c.p])]
                            t[c.p] = y[0]
                            c.p += y[1]
                            c.st = y[2]
                            steps += 1
                            out = out or c.p > end
                            if c.st == A and t[c.p] == 0 and c.p == v and read(c, v) is not None:
                                break
                        if out:      # the head went past the end of R: not covered by the rule
                            tally['the head goes past R'] = tally.get('the head goes past R', 0) + 1
                        elif v > separators(e, r)[1][0]:      # the new event cell lies in item 1
                            tally['the new event cell lies in item 1'] = tally.get('the new event cell lies in item 1', 0) + 1
                        else:
                            ok = all(t[p] == b for p, b in cells.items())
                            tally['match' if ok else 'differ'] += 1
                break
            j = longest(lambda x: jump(r, x))
            if j > 1:
                write(s, e, jump(r, j - 1))
        sys.stdout.flush()
    print('%d stages; changes of stage with Z empty: %s' % (stage, ', '.join('%s %d' % kv for kv in tally.items())))


def rules(r, rv, shift, first):
    """Checks the new stage's reading rv (at the new event cell, `shift` cells from the old one) against the rules
    for the state of the first crossing into the event cell after the C-wave.  E: the event ends as usual (same event
    cell, one left increment `linc`, item 0 keeps its widths with Q = 3 - a and P = 3 - b, as if the unit went on in
    item 0 alone); checked where the P of item 0 and the Q of item 1 are not empty.  D (a >= 2) with the event cell
    moved 2 cells left, and A (a = 1) with it moved 2 cells right: item 0 is rewritten as an item of the C-wave,
    its `11` moved 2 cells, Q = 2 (a >= 2) or 0 (a = 1), P = 2 if b >= 2 and 0 if b = 1.  Returns a label."""
    its = r[2] + [r[3]]
    st = phases(its)
    if st is None or first not in ('A', 'D', 'E'):
        return '%s other' % first
    a, b = st[0]
    q0 = its[0][0]
    n0 = (rv[2] + [rv[3]])[0]
    q1, p1 = n0[0], n0[1]
    v = lambda w: sum(d << i for i, d in enumerate(w))
    if first == 'E':
        if not its[0][1]:
            return 'E, P of item 0 empty'
        if len(its) > 1 and not its[1][0]:
            return 'E, Q of item 1 empty'
        li = linc(r[0])
        lu = [u for u in rv[0] if u not in ('top', 'rest')]
        why = [w for w, ok in (('cell', shift == 0), ('left', li is not None and li[:len(lu)] == lu),
                               ('Q', len(q1) == len(q0) and v(q1) == (3 - a) % (1 << len(q1))),
                               ('P', p1 is not None and v(p1) == (3 - b) % (1 << len(p1)))) if not ok]
        return 'E ' + ('match' if not why else 'differ (%s)' % '+'.join(why))
    want = -2 if first == 'D' else 2      # the C-wave moves the `11` of item 0 two cells left (a >= 2) or right (a = 1)
    if shift != want:
        return '%s, cell moved %s' % (first, '-6' if shift == -6 else 'otherwise')
    ok = (v(q1) == (0 if a == 1 else 2) % (1 << len(q1)) and p1 is not None
          and v(p1) == (2 if b >= 2 else 0) % (1 << len(p1)))
    return '%s, cell moved %d, ' % (first, shift) + ('match' if ok else 'differ')


def transient(stages):
    """Follows STAGES stages and, at every change of stage with Z empty (any widths), runs the change cell by cell on
    a copy up to the first event at the new event cell and records what the head does after the C-wave has left
    item 1 for the last time: how far left of the event cell it goes, the states
    in which it crosses into the event cell from the right, every visit in state F (the halting state) and the cell
    it reads there, and the reading at the new event cell (Z, and where its first item starts)."""
    tr = ptab(M)
    s, cell, events, e0 = reach_stage(tr)
    print('%s: about 10^%d events from blank tape (defects.py)' % (M, len(str(events)) - 1))
    S = 'ABCDEF'
    e, stage = None, 0
    n, far, zne, first, f_one, f_all = 0, 0, 0, 0, 0, 0
    sigs, tally = {}, {}
    while stage < stages:
        ep = e
        e = find_event_cell(s, e)
        if e is None:
            print('no event cell found')
            break
        if e != ep:
            stage += 1
        while True:
            ev, r = next_event(s, e)
            if ev != 'event':
                print(ev)
                return
            if law(r) is None:
                if evNext(r[1], r[2], r[3]) is None and not r[1] and read_j(s, e) is None:
                    c = copy_sim(s)
                    v = find_event_cell(copy_sim(c), e)
                    s1 = separators(e, r)[1][0] if len(r[2]) else None
                    t, steps, left, after, sig, prev = c.t, 0, 0, False, [], c.p
                    while steps < 200000:
                        if c.st == S.index('F'):
                            f_all += 1
                            f_one += t[c.p]
                        y = c.tr[(c.st, t[c.p])]
                        t[c.p] = y[0]
                        c.p += y[1]
                        c.st = y[2]
                        steps += 1
                        if s1 is not None and c.p >= s1:
                            left, sig, after = 0, [], False
                        elif s1 is not None and prev >= s1:
                            after = True
                        if after:
                            left = min(left, c.p - e)
                            if prev > e >= c.p:
                                sig.append(S[c.st])
                        prev = c.p
                        if c.st == A and t[c.p] == 0 and c.p == v and read(c, v) is not None:
                            break
                    if s1 is None or v is None:
                        continue
                    n += 1
                    far = min(far, left)
                    rv = read(c, v)
                    zne += bool(rv[1])
                    first += tuple(t[v + 1:v + 3]) == (1, 1)
                    k = ''.join(sig)
                    sigs[k] = sigs.get(k, 0) + 1
                    cls = rules(r, rv, v - e, sig[0] if sig else None)
                    tally[cls] = tally.get(cls, 0) + 1
                    if 'differ' in cls and '-v' in sys.argv:
                        its0 = r[2] + [r[3]]
                        print('  %s: phases %s, items before %s, first items after %s' % (
                            cls, phases(its0)[:2], its0[:2], (rv[2] + [rv[3]])[:2]))
                break
            j = longest(lambda x: jump(r, x))
            if j > 1:
                write(s, e, jump(r, j - 1))
        sys.stdout.flush()
    print('%d stages; %d changes of stage with Z empty and at least two items' % (stage, n))
    print('after the C-wave has left item 1 for the last time: farthest left of the event cell %d cells' % far)
    print('at the new event cell: Z not empty %d; first item starting right of it (11): %d of %d' % (zne, first, n))
    print('visits in state F during the changes: %d, on a 1: %d' % (f_all, f_one))
    print('states crossing into the event cell from the right, after the C-wave: %s' %
          ', '.join('%s %d' % kv for kv in sorted(sigs.items(), key=lambda kv: -kv[1])))
    print('the first item and the left words, by the state of the first crossing: %s' %
          ', '.join('%s %d' % kv for kv in sorted(tally.items())))


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    {'check': check, 'transient': transient}[sys.argv[1]](int(sys.argv[2]))
