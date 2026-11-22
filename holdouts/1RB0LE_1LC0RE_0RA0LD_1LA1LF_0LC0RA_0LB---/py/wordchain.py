"""The right side of the two-word sweepers as a chain of binary counters, and a simulator that jumps over eras.

At a full event (state A on a 0, the tape left of the head exactly 0^inf 1 0 [N], N base 3 in 3-cell digits
100 = 0, 110 = 1, 010 = 2), cut the cells right of the head into tokens of two cells (z = 00, a = 10, c = 01,
d = 11).  In every layout met so far they read

    Z d  W1 c U1  a d  W2 c U2  a d ...  a d  Wm c Um        (blank tape after Um)

- Z: digits za = 0, aa = 1 (4-cell 0010 / 1010), lowest digit first, at least one digit;
- W_i: digits zc = 0, cc = 1 (0001 / 0101), any width, possibly empty;
- U_i: digits az = 0, aa = 1 (1000 / 1010), any width, possibly empty.

(The README's plain layout Z | 11 | C | 01 | R is Z d [C] c [R]; the X layout Z | 11 01 10 | X | 11 | C | 01 | R is
Z d [] c [X] a d [C] c [R]; X's za/aa digits are the same cells as az/aa digits read one token later.)

**The carry law (checked on runs, not yet in Lean beyond the cases of Cascade.lean and Xlayer*.lean).**  Every
word is a binary counter.  At each event Z gets 1.  A word w of width k that gets c adds c and passes
3·floor((w + c) / 2^k) to the next word (so an empty word passes 3c on).  In one number: with the words
w_0 = Z, w_1 = W1, w_2 = U1, ... and p_i the total width of the words before w_i,

    S = sum_i  w_i · 2^(p_i) · 3^(m - i)        (m + 1 words in all)

gains exactly 3^m at every event, and the words are the unique digits of S with every w_i < 2^(width) (each
lower word is fixed by S modulo a power of 2, because 3 is invertible mod 2).  So inside a layout the whole right
side is one counter, and the only events not covered are those in which the last word would overflow: the
changes of era, where the layout changes.

The simulator runs the machine cell by cell from blank tape; at each full event in such a layout it computes, from
S, the last event before the last word overflows, writes that tape and goes on cell by cell through the era
change to the next full event in a layout.  Before each jump it spot-checks the law: SPOT random events of the
era, each built from S and run cell by cell for up to 40 events (at most 10^6 steps), every one compared with
the law.

usage (from the repository root):
  python3 .../py/wordchain.py MACHINE check STEPS          the law on every pair of consecutive full events of a run
  python3 .../py/wordchain.py MACHINE jump ERAS [SPOT [OUT.json]]
                                                          follow ERAS changes of era (SPOT spot checks per era)
"""
import json
import random
import re
import sys

D3 = {0: '100', 1: '110', 2: '010'}
D3r = {v: k for k, v in D3.items()}
T2 = {'00': 'z', '10': 'a', '01': 'c', '11': 'd'}
GL = re.compile(r'^((?:za|aa)+)d((?:(?:zc|cc)*c(?:az|aa)*ad)*)((?:zc|cc)*)c((?:az|aa)*)$')
PR = re.compile(r'((?:zc|cc)*)c((?:az|aa)*)ad')


def ptab(m):
    t = {}
    for i, s in enumerate(m.split('_')):
        for r in range(2):
            x = s[3 * r:3 * r + 3]
            if x[2] != '-':
                t[(i, r)] = (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t


def bits(s, one):
    return [1 if s[i:i + 2] == one else 0 for i in range(0, len(s), 2)]


def val(b):
    return sum(x << i for i, x in enumerate(b))


def parse_words(tok):
    """The words [Z, W1, U1, W2, U2, ...] (bit lists, lowest first) of a token string, or None."""
    m = GL.match(tok)
    if not m:
        return None
    z, mid, wl, ul = m.groups()
    words = [bits(z, 'aa')]
    for w, u in PR.findall(mid):
        words += [bits(w, 'cc'), bits(u, 'aa')]
    words += [bits(wl, 'cc'), bits(ul, 'aa')]
    return words


def tape_right(words):
    """The cells from the head on (the head cell 0 first) of a layout."""
    D = (('0010', '1010'), ('0001', '0101'), ('1000', '1010'))
    s = '0' + ''.join(D[0][b] for b in words[0]) + '11'
    rest = words[1:]
    for i in range(0, len(rest), 2):
        if i:
            s += '1011'
        s += ''.join(D[1][b] for b in rest[i]) + '01' + ''.join(D[2][b] for b in rest[i + 1])
    return s


def tape_left(n, nw):
    return '10' + ''.join(D3[(n // 3 ** i) % 3] for i in range(nw - 1, -1, -1))


def S_of(words):
    m = len(words) - 1
    S = 0
    p = 0
    for i, w in enumerate(words):
        S += val(w) * (1 << p) * 3 ** (m - i)
        p += len(w)
    return S


def decode(S, widths):
    """The words with these widths whose S is S, or None if the last word would not fit."""
    m = len(widths) - 1
    out = []
    for i, w in enumerate(widths):
        if i == m:
            if S < 0 or S >= (1 << w):
                return None
            out.append([(S >> j) & 1 for j in range(w)])
            break
        t = 3 ** (m - i)
        mod = 1 << w
        v = (S * pow(t, -1, mod)) % mod if w else 0
        out.append([(v >> j) & 1 for j in range(w)])
        S -= v * t
        S //= mod
    return out


def add_n(n, nw, e):
    """N after e events: base 3; 2...2 wraps to 0...0 with one digit more."""
    n += e
    while n >= 3 ** nw:
        n -= 3 ** nw
        nw += 1
    return n, nw


def show(n, nw, words):
    names = ['Z'] + ['W' if i % 2 else 'U' for i in range(1, len(words))]
    return 'N=%d(%d) ' % (n, nw) + ' '.join('%s%d(%d)' % (a, val(w), len(w)) for a, w in zip(names, words))


class Sim:
    def __init__(self, tr, size=1 << 22):
        self.tr = tr
        self.size = size
        self.t = bytearray(size)
        self.p = size // 2
        self.st = 0
        self.lo = self.hi = self.p

    def load(self, left, right):
        self.t = bytearray(self.size)
        self.p = self.size // 2
        self.st = 0
        for i, ch in enumerate(left):
            self.t[self.p - len(left) + i] = ch == '1'
        for i, ch in enumerate(right):
            self.t[self.p + i] = ch == '1'
        self.lo = self.p - len(left)
        self.hi = self.p + len(right)

    def full_event(self):
        """(N, width of N, tokens right of the head) if the head is at a full event, else None."""
        t, p = self.t, self.p
        f = self.lo
        while f < p and t[f] == 0:
            f += 1
        if f >= p - 2 or t[f + 1] != 0 or (p - f - 2) % 3:
            return None
        n = nw = 0
        for j in range(f + 2, p, 3):
            key = '%d%d%d' % (t[j], t[j + 1], t[j + 2])
            if key not in D3r:
                return None
            n = n * 3 + D3r[key]
            nw += 1
        if nw == 0:
            return None
        R = ''.join('1' if t[j] else '0' for j in range(p + 1, self.hi + 2)) + '0000'
        if len(R) % 2:
            R += '0'
        if R[:4] not in ('0010', '1010'):
            return None
        return n, nw, ''.join(T2[R[j:j + 2]] for j in range(0, len(R), 2)).rstrip('z')

    def run_to_event(self, maxsteps):
        """Runs to the next full event: ((N, nw, tokens), steps), ('HALT', steps) or (None, steps)."""
        t, tr = self.t, self.tr
        k = 0
        p, st, lo, hi = self.p, self.st, self.lo, self.hi
        while k < maxsteps:
            x = tr.get((st, t[p]))
            if x is None:
                self.p, self.st, self.lo, self.hi = p, st, lo, hi
                return 'HALT', k
            t[p] = x[0]
            p += x[1]
            st = x[2]
            k += 1
            if p < lo:
                lo = p
            elif p > hi:
                hi = p
            if st == 0 and t[p] == 0 and t[p + 1:p + 5] in (b'\x00\x00\x01\x00', b'\x01\x00\x01\x00'):
                self.p, self.st, self.lo, self.hi = p, st, lo, hi
                e = self.full_event()
                if e:
                    return e, k
        self.p, self.st, self.lo, self.hi = p, st, lo, hi
        return None, k


def jump(words):
    """The largest e such that the layout still holds e events later (the last word does not overflow)."""
    m = len(words) - 1
    S = S_of(words)
    W = [len(w) for w in words]
    inc = 3 ** m
    if decode(S + inc, W) is None:
        return 0, None
    lo, hi = 1, 2
    while decode(S + hi * inc, W) is not None:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if decode(S + mid * inc, W) is not None:
            lo = mid
        else:
            hi = mid
    return lo, decode(S + lo * inc, W)


def spot_check(tr, n, nw, words, j, count, rng):
    """count random events of the era, each built from S and run for up to 40 events against the law."""
    W = [len(w) for w in words]
    m = len(words) - 1
    S = S_of(words)
    done = bad = 0
    for _ in range(count):
        e0 = rng.randrange(0, j + 1)
        s = Sim(tr, 1 << 16)
        nn, nnw = add_n(n, nw, e0)
        s.load(tape_left(nn, nnw), tape_right(decode(S + e0 * 3 ** m, W)))
        budget = 10 ** 6  # steps per sample: a sample stops early when its events are long
        for q in range(1, 41):
            if e0 + q > j:
                break
            e, k = s.run_to_event(budget)
            budget -= k
            if e is None and budget <= 0:
                break
            if e == 'HALT' or e is None or parse_words(e[2]) != decode(S + (e0 + q) * 3 ** m, W) \
                    or (e[0], e[1]) != add_n(n, nw, e0 + q):
                bad += 1
                break
            done += 1
    return done, bad


def check(M, maxsteps):
    tr = ptab(M)
    s = Sim(tr)
    stats = {'by the law': 0, 'MISMATCH': 0, 'change of layout': 0, 'full event in no layout': 0}
    prev = None
    steps = 0
    while steps < maxsteps:
        e, k = s.run_to_event(maxsteps - steps)
        steps += k
        if e == 'HALT':
            print('HALT at step', steps)
            break
        if e is None:
            break
        n, nw, tok = e
        w = parse_words(tok)
        if w is None:
            stats['full event in no layout'] += 1
            prev = None
            continue
        if prev:
            pn, pnw, pw = prev
            if [len(x) for x in pw] == [len(x) for x in w]:
                if S_of(w) == S_of(pw) + 3 ** (len(w) - 1) and (n, nw) == add_n(pn, pnw, 1):
                    stats['by the law'] += 1
                else:
                    stats['MISMATCH'] += 1
                    if stats['MISMATCH'] <= 5:
                        print('mismatch at step', steps, show(*prev), '->', show(n, nw, w))
            else:
                stats['change of layout'] += 1
        prev = (n, nw, w)
    print('%d steps of %s: %s' % (steps, M, stats))


def save(out, M, rows, events, steps, checked):
    if out:
        json.dump(dict(machine=M, eras=rows, events=events, cell_steps=steps, spot_checked=checked[0],
                       spot_bad=checked[1]), open(out, 'w'), indent=1)


def follow(M, eras, spot, out=None):
    tr = ptab(M)
    s = Sim(tr)
    rng = random.Random(1)
    steps = 0   # steps simulated cell by cell
    events = 0  # full events since the start (each is at least one step of the machine)
    rows = []
    checked = [0, 0]
    e, k = s.run_to_event(10 ** 9)
    steps += k
    events += 1
    while len(rows) < eras:
        if e == 'HALT':
            print('HALT after %d events, %d steps simulated cell by cell' % (events, steps))
            break
        if e is None:
            print('no full event within 10^9 steps')
            break
        n, nw, tok = e
        w = parse_words(tok)
        if w is not None:
            j, w2 = jump(w)
            if j > 0:
                if spot:
                    d, b = spot_check(tr, n, nw, w, j, spot, rng)
                    checked[0] += d
                    checked[1] += b
                n2, nw2 = add_n(n, nw, j)
                row = dict(event=events, start=show(n, nw, w), events=j, last=show(n2, nw2, w2),
                           widths=[len(x) for x in w])
                if rows:
                    rows[-1]['next'] = row['start']
                    rows[-1]['steps_to_next'] = steps - rows[-1]['steps_at_last']
                events += j
                row['steps_at_last'] = steps
                rows.append(row)
                print('event %d: %s, +%d events to %s (spot checks %d events, %d bad)'
                      % (row['event'], row['start'], j, row['last'], checked[0], checked[1]))
                sys.stdout.flush()
                s.load(tape_left(n2, nw2), tape_right(w2))
                if len(rows) % 10 == 0:
                    save(out, M, rows, events, steps, checked)
        e, k = s.run_to_event(10 ** 9)
        steps += k
        events += 1
    save(out, M, rows, events, steps, checked)
    print('%d events (so at least %d steps), %d steps simulated cell by cell, spot checks: %d events, %d bad'
          % (events, events, steps, checked[0], checked[1]))


if __name__ == '__main__':
    M, mode = sys.argv[1], sys.argv[2]
    if mode == 'check':
        check(M, int(sys.argv[3]))
    else:
        follow(M, int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 0,
               sys.argv[5] if len(sys.argv) > 5 else None)
