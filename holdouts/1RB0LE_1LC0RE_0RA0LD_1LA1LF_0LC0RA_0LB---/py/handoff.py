"""What a change of era hands on: checks three rules at every change of era of a jump run (see wordchain.py).

At the last full event of an era (state A on a 0, left of the head 0^inf 1 0 [N], N base 3 with nw digits; right of
the head the chain Z d W1 c U1 a d ... Wm c Um with the last word about to overflow) the next event is the change of
era.  Its carry runs through every word and off the right end of the chain, and the head then sweeps back to the
left end.  Let d be the number of base-3 digits N loses at the change (nw - nw' at the next full event in a layout).

  R1  N' = floor(N / 3^d) + 1, with nw' = nw - d digits.
  R2  d = 0, or d = a + b + 2 where, reading N from its lowest digit (the one next to the head), N starts with a
      zeros, then one digit x in {1, 2}, then b twos, then one more digit: the change eats exactly that block.
      (So whenever d > 0 it is fixed by N alone.)
  R3  d = 0 exactly when the sweep back reaches the left end (cell 0, the head cell of the last event) in state C;
      otherwise it arrives in state A and d > 0.  The state is fixed by the chain, word by word, during the sweep.

usage (from the repository root):
  python3 .../py/handoff.py MACHINE ERAS        follow ERAS changes of era and check R1-R3 at each
"""
import re
import sys

from wordchain import Sim, add_n, jump, parse_words, ptab, show, tape_left, tape_right


def low_digits(n, nw):
    out = []
    for _ in range(nw):
        out.append(n % 3)
        n //= 3
    return out


def r2_predict(dig):
    s = ''.join(map(str, dig))
    m = re.match(r'(0*)([12])(2*)', s)
    return len(m.group(0)) + 1 if m else None


def sweep_back_state(s, width):
    """Runs from the last event of an era until the head, having been past the right end of the chain, is back at
    cell 0 or left of it; returns the state there (A..F) and the steps taken."""
    t, tr = s.t, s.tr
    p, st = s.p, s.st
    p0 = p
    far = False
    k = 0
    while True:
        x = tr[(st, t[p])]
        t[p] = x[0]
        p += x[1]
        st = x[2]
        k += 1
        if p - p0 >= width - 2:
            far = True
        if p < s.lo:
            s.lo = p
        elif p > s.hi:
            s.hi = p
        if far and p <= p0:
            s.p, s.st = p, st
            return 'ABCDEF'[st], k


def run(M, eras):
    tr = ptab(M)
    s = Sim(tr)
    e, _ = s.run_to_event(10 ** 9)
    changes = []
    while len(changes) < eras:
        if e in ('HALT', None):
            print('stopped:', e)
            break
        n, nw, tok = e
        w = parse_words(tok)
        if w is None:
            e, _ = s.run_to_event(10 ** 9)
            continue
        j, w2 = jump(w)
        if j == 0:  # this event is already the last of its era
            w2 = w
        n2, nw2 = add_n(n, nw, j)
        right = tape_right(w2)
        s.load(tape_left(n2, nw2), right)
        state, _ = sweep_back_state(s, len(right))
        e, _ = s.run_to_event(10 ** 9)
        while e not in ('HALT', None) and parse_words(e[2]) is None:
            e, _ = s.run_to_event(10 ** 9)
        if e in ('HALT', None):
            print('stopped after a change:', e)
            break
        n3, nw3 = e[0], e[1]
        changes.append((n2, nw2, show(n2, nw2, w2), state, n3, nw3))
    return changes


def main():
    M, eras = sys.argv[1], int(sys.argv[2])
    changes = run(M, eras)
    tally = {}
    bad = []
    for i, (n, nw, last, state, n3, nw3) in enumerate(changes):
        d = nw - nw3
        r1 = d >= 0 and n // 3 ** d + 1 == n3
        r2 = d == 0 or r2_predict(low_digits(n, nw)) == d
        r3 = (d == 0) == (state == 'C') and state in 'AC'
        key = 'd=0' if d == 0 else ('d>=2' if d >= 2 else 'd=%d' % d)
        tally[key] = tally.get(key, 0) + 1
        if not (r1 and r2 and r3):
            bad.append((i, d, ''.join(map(str, low_digits(n, nw)))[:12], state, r1, r2, r3))
    print('%s: %d changes of era, %s' % (M, len(changes), tally))
    print('changes breaking R1, R2 or R3 (index, d, lowest digits of N first, state, R1, R2, R3):')
    for b in bad:
        print('  ', b)
    print('all others follow R1, R2 and R3')


if __name__ == '__main__':
    main()
