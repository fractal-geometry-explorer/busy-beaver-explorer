"""Exact rounds of the counter model on very long lists (the A phase of round 16,952,683,091).

`model.jump` computes the prefix values L[i] = sum d_j 3^j of the whole list, so one jump costs O(m^2) bit
operations and O(m) big integers of size 3^m in memory. With 135,700 groups that is several GB per jump, and the
cycle.py run was killed for lack of memory at the A phase of round 16,952,683,091. `jump_fast` gives the same
result (checked by `test`) but only looks at the low k digits, where 3^k is the first power above the jump length:
  - for i >= k a group can only stop the jump if its digit and every digit between k and i are 0 and it has
    n <= 1 (then its event is L[k] + 1), or it is the first nonzero digit p above k, equal to 1, with n = 0 (its
    digit reaches 0 at L[k] + 1); every other group's event is above 3^k > D;
  - subtracting D < 3^k changes the digits above k only by one borrow, which runs through the zero digits from k
    up to the first nonzero digit p (or wraps round the top when every digit from k up is 0); exactly the groups
    k-1 .. p-1 are passed once more by that borrow.

usage: python3 aphase.py test [N]                  jump_fast == model.jump on N random states (default 20000)
       python3 aphase.py run STATE.pkl OUT.pkl      exact rounds from a cycle.py checkpoint (n0, G, R) until the
                                                    next normal round start, as cycle.py's slow() does; writes
                                                    (n0, G, R) and prints the events
"""
import pickle
import random
import sys
import time

sys.set_int_max_str_digits(0)

from model import jump, bounce_lean, split_trailing, INF
from rightpart import normal


def jump_fast(n0, G):
    H, t = split_trailing(G)
    if t > 3:
        return 0, n0, G
    m = len(H)
    best = INF
    Li = 0          # L[i]
    p3 = 1          # 3^i
    k = m
    for i in range(m):
        if p3 > best:
            k = i
            break
        d, n = H[i]
        Li1 = Li + d * p3
        q = p3 * 3
        if n >= 1:
            if n >= 2 and best != INF and (n - 1).bit_length() + q.bit_length() - 2 > best.bit_length():
                Li, p3 = Li1, q         # (n-1)*q >= 2^(a-1) 2^(b-1) > best: no need to multiply
                continue
            ev = Li1 + 1 + (n - 1) * q
        else:
            ev = Li1 + 1
            if d >= 1:
                ev = min(ev, Li + 1 + (d - 1) * p3)
        if ev - 1 < best:
            best = ev - 1
        Li, p3 = Li1, q
    # Li = L[k], p3 = 3^k
    # first nonzero digit at or above k; groups k..p-1 with n <= 1 stop the jump at L[k]
    p = k
    while p < m and H[p][0] == 0:
        if H[p][1] <= 1 and Li < best:
            best = Li
        p += 1
    if p < m and H[p] == (1, 0) and Li < best:
        best = Li                       # an empty group whose digit 1 reaches 0 at L[p] + 1 = L[k] + 1
    if t != 2 and p == m and Li < best:
        best = Li                       # best starts at L[m] when the borrow supply is finite
    if best == INF:
        return 0, n0, G
    D = int(best)
    if D <= 0:
        return 0, n0, G
    if t != 2 and p == m:
        assert D <= Li
    newLk = Li - D
    borrow = newLk < 0
    low = newLk % p3
    newH = list(H)
    cur, a, b = low, Li, newLk      # low // 3^i, L[k] // 3^(i+1), (L[k] - D) // 3^(i+1); divisions by 3 only
    for i in range(k):
        d, n = H[i]
        cur, e = divmod(cur, 3)
        a //= 3
        b //= 3
        newH[i] = (e, n - (a - b))
    if borrow:
        for j in range(k, p):
            newH[j] = (2, H[j][1] - 1)
        if p < m:
            d, n = H[p]
            newH[p] = (d - 1, n)
        else:
            assert t == 2
    return D, n0 + D, newH + [(0, 0)] * t


def test(N):
    rnd = random.Random(1)
    bad = 0
    for it in range(N):
        m = rnd.randint(1, 12)
        H = []
        for i in range(m):
            d = rnd.choice([0, 0, 1, 2, 2, 2])
            n = rnd.choice([0, 1, 1, 2, 3, rnd.randint(0, 50), rnd.randint(0, 10 ** 6)])
            H.append((d, n))
        t = rnd.choice([0, 1, 2, 2, 3])
        n0 = rnd.randint(0, 100)
        G = H + [(0, 0)] * t
        try:
            a = jump(n0, G)
        except OverflowError:
            continue                    # model.jump is undefined here (no group left); never used so
        b = jump_fast(n0, G)
        if a[0] == 0 and b[0] == 0:
            continue
        if a != b:
            bad += 1
            if bad < 5:
                print('MISMATCH', n0, G, a, b)
    print('%d random states, %d mismatches' % (N, bad))
    return bad == 0


def run(src, out):
    st = pickle.load(open(src, 'rb'))
    n0, G, R = st if len(st) == 3 else (st[0], st[1], 0)
    print('start round %d, %d groups, last %s' % (R, len(G), [n for _, n in G[-3:]]), flush=True)
    t0 = time.time()
    events, bounces, jumps = {}, 0, 0
    while True:
        D, n0, G = jump_fast(n0, G)
        bounces += D
        jumps += 1
        r = bounce_lean(n0, G)
        bounces += 1
        if r[0] != 'next':
            print('HALT in round %d after %d bounces: %s' % (R, bounces, r), flush=True)
            pickle.dump((n0, G, R, 'HALT'), open(out, 'wb'))
            return 'HALT'
        n0, G, ev = r[1], r[2], r[3]
        if ev is not None:
            events[ev] = events.get(ev, 0) + 1
            if ev == 'E':
                R += 1
            if sum(events.values()) <= 50 or ev not in ('E',):
                print('%.0f s event %s, round %d, %d groups, %d jumps' % (time.time() - t0, ev, R, len(G), jumps), flush=True)
        if jumps % 100000 == 0:
            print('%.0f s %d jumps, round %d, events %s' % (time.time() - t0, jumps, R, events), flush=True)
        if ev in ('D', 'A') and normal(G):
            break
    print('normal round start: round %d, %d groups, last %s, events %s, %d jumps, %.0f s' % (
        R, len(G), [n for _, n in G[-3:]], events, jumps, time.time() - t0), flush=True)
    pickle.dump((n0, G, R), open(out, 'wb'))
    return 'next'


if __name__ == '__main__':
    if sys.argv[1] == 'test':
        sys.exit(0 if test(int(sys.argv[2]) if len(sys.argv) > 2 else 20000) else 1)
    run(sys.argv[2], sys.argv[3])
