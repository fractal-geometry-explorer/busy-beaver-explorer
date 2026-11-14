"""A simulator of the counter model (model.py) that does not touch the old groups.

Between events a round is a countdown of the ternary counter from all digits 2 to all digits 0, and a group with
p - 1 groups to its right is passed 3^(p-1) times in it (the last one twice), whatever happens to its left: a group
is passed exactly when the number formed by the digits to its right is decremented.  So the groups are kept as
(length at round R0, R0) and only the *prefix* is simulated bounce by bounce: the groups that can run out in this
round and the one after them.  The rest of the list is one counter W that absorbs the borrows leaving the prefix.
At the end of the countdown the round ends in closed form:

    (x; (0,a1), ..., (0,am))  ->  (2; (2,x), (2,a1-1), ..., (2,a(m-1)-1), (2,am-2))       (events E, decrement, D)

Whenever the prefix would reach the last two groups, the last group is below 3, a group next to W is empty, or an
event other than a decrement or a merge occurs, the whole round is done with the exact model instead (`slow`),
until all digits are 2 again.  A halt found in the prefix is confirmed by the exact model.

    python3 py/skip.py test ROUNDS            # against the exact model at the start of every round
    python3 py/skip.py run ROUNDS [SECONDS]   # run, reporting slow rounds, charged pairs and the right end
"""
import heapq
import os
import pickle
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import START, bounce_lean, jump
from charge import charges

BIG = 1 << 62
P3 = [1]


def pow3(k):
    while len(P3) <= k:
        P3.append(P3[-1] * 3)
    return P3[k]


def rate(q):
    return pow3(q) if q else 2


def normal(G):
    return len(G) >= 2 and all(d == 2 for d, _ in G) and G[-1] != (2, 0)


class Sim:
    """Round-start states only: all digits 2.  A[q] = [base, R0] for the group with q groups to its right."""

    def __init__(self, n0, G, rounds):
        self.rounds, self.slow_rounds, self.halted = rounds, 0, False
        self.load(n0, G)

    def load(self, n0, G):
        assert normal(G)
        self.n0 = n0
        self.A = [[n, self.rounds, 0] for _, n in reversed(G)]
        self.heap = []
        for q in range(len(self.A)):
            self.push(q)

    def val(self, q):
        b, r0, _ = self.A[q]
        return b - (self.rounds - r0) * rate(q)

    def push(self, q):
        """The first round at whose start this group is below rate + 2 (it may run out in that round)."""
        g = self.A[q]
        g[2] += 1
        lim = rate(q) + 2
        k = 0 if g[0] < lim else (g[0] - lim) // rate(q) + 1
        heapq.heappush(self.heap, (g[1] + k, id(g), g[2], g))

    def state(self):
        return self.n0, [(2, self.val(q)) for q in range(len(self.A) - 1, -1, -1)]

    def due(self):
        """Depth q of the deepest group that may run out in this round, or None."""
        out = None
        h = self.heap
        while h and h[0][0] <= self.rounds:
            _, _, stamp, g = h[0]
            if g[2] != stamp or g[1] > self.rounds:
                heapq.heappop(h)
                continue
            q = self.where(g)
            if q is None:
                heapq.heappop(h)
                continue
            out = q if out is None else min(out, q)
            heapq.heappop(h)
            self.pending.append(g)
        return out

    def where(self, g):
        A = self.A                      # groups near the front: search from the top
        for q in range(len(A) - 1, -1, -1):
            if A[q] is g:
                return q
        return None

    def slow(self):
        """One or more rounds with the exact model, until all digits are 2 again."""
        n0, G = self.state()
        self.slow_rounds += 1
        while True:
            _, n0, G = jump(n0, G)
            r = bounce_lean(n0, G)
            if r[0] != 'next':
                self.halted = True
                self.halt_state = (n0, G)
                return
            n0, G = r[1], r[2]
            if r[3] == 'E':
                self.rounds += 1
            if r[3] in ('D', 'A') and normal(G):
                break
        self.load(n0, G)

    def step(self):
        """One round."""
        A, m = self.A, len(self.A)
        self.pending = []
        qd = self.due()
        if m < 8 or self.val(0) < 3:
            return self.slow()
        cut = m - 2 if qd is None else min(m - 2, qd - 1)       # the prefix is A[cut:]
        if cut < 2:
            return self.slow()
        c = m - cut
        P = [(2, self.val(q)) for q in range(m - 1, cut - 1, -1)]
        n0, W = self.n0, pow3(cut) - 1
        while True:
            # ---- jump: plain decrements up to the next event of the prefix
            L = [0] * (c + 1)
            for i, (d, n) in enumerate(P):
                L[i + 1] = L[i] + d * pow3(i)
            tot = L[c] + W * pow3(c)
            if tot == 0:
                break
            best = tot
            for i, (d, n) in enumerate(P):
                q3 = pow3(i + 1)
                if n >= 1:
                    ev = L[i + 1] + 1 + (n - 1) * q3
                else:
                    ev = L[i + 1] + 1
                    if d >= 1:
                        ev = min(ev, L[i] + 1 + (d - 1) * pow3(i))
                best = min(best, ev - 1)
            if best > 0:
                new = tot - best
                P = [((new // pow3(i)) % 3, n - (tot // pow3(i + 1) - new // pow3(i + 1))) for i, (d, n) in enumerate(P)]
                W, n0 = new // pow3(c), n0 + best
                if new == 0:
                    break
            # ---- one bounce of the exact model on the prefix followed by the counter W
            if not P or P[-1][1] == 0:
                return self.slow()
            r = bounce_lean(n0, P + [(W, BIG)])
            if r[0] != 'next' or r[3] is not None or not r[2] or r[2][-1][1] != BIG:
                return self.slow()
            n0, P, W = r[1], r[2][:-1], r[2][-1][0]
            c = len(P)
            if c == 0:
                return self.slow()
        if any(n < 2 for _, n in P):
            return self.slow()
        # ---- the end of the round, in closed form
        self.rounds += 1
        del A[cut:]
        for d, n in reversed(P):
            A.append([n - 1, self.rounds, 0])
        A.append([n0, self.rounds, 0])
        self.n0 = 2
        for q in range(cut, len(A)):
            self.push(q)
        for g in self.pending:                                   # still due, if it was not in the prefix
            q = self.where(g) if g[2] else None
            if q is not None and q < cut:
                self.push(q)


def exact_rounds(n0, G, rounds, upto):
    """Round-start states of the exact model: yields (rounds, n0, G) at every normal state."""
    while rounds < upto:
        _, n0, G = jump(n0, G)
        r = bounce_lean(n0, G)
        assert r[0] == 'next'
        n0, G = r[1], r[2]
        if r[3] == 'E':
            rounds += 1
        if r[3] in ('D', 'A') and normal(G):
            yield rounds, n0, G


def first_normal(n0, G, rounds):
    for x in exact_rounds(n0, G, rounds, 10 ** 18):
        return x


def test(upto, start=None):
    if start:
        n0, G = pickle.load(open(start, 'rb'))
        rounds = int(''.join(ch for ch in os.path.basename(start) if ch.isdigit()))
    else:
        rounds, n0, G = first_normal(START[0], START[1], 0)
    s = Sim(n0, G, rounds)
    ref = {}
    last = rounds
    for r, a, b in exact_rounds(n0, G, rounds, rounds + upto):
        ref.setdefault(r, []).append((a, b))
        last = r
    checked = 0
    while s.rounds < last and not s.halted:
        s.step()
        if s.state() not in ref.get(s.rounds, []):
            print('MISMATCH at round', s.rounds)
            return False
        checked += 1
    print('%d round starts agree with the exact model (rounds %d to %d, %d done by the exact model)' % (
        checked, rounds, s.rounds, s.slow_rounds))
    return True


def run(upto, seconds, start=None, save=None):
    if start:
        n0, G = pickle.load(open(start, 'rb'))
        rounds = int(''.join(ch for ch in os.path.basename(start) if ch.isdigit()))
    else:
        rounds, n0, G = first_normal(START[0], START[1], 0)
    s = Sim(n0, G, rounds)
    t0, nxt, slow, ch = time.time(), 1, 0, None
    while s.rounds < upto and time.time() - t0 < seconds and not s.halted:
        s.step()
        if s.slow_rounds != slow or s.rounds >= nxt or s.halted:
            n0, G = s.state()
            c = [(len(G) - i, o) for i, o in charges(G)]
            if s.slow_rounds != slow or c != ch:
                print('round %d: %d groups, last groups %s, charged pairs (position from the right, residue) %s%s' % (
                    s.rounds, len(G), [n for _, n in G[-3:]], c, ', exact rounds so far %d' % s.slow_rounds), flush=True)
            slow, ch = s.slow_rounds, c
            while nxt <= s.rounds:
                nxt *= 2
    if s.halted:
        print('HALT in round', s.rounds)
    print('stopped at round %d after %.0f s, %d groups' % (s.rounds, time.time() - t0, len(s.A)))
    if save:
        pickle.dump(s.state(), open(save, 'wb'))
    return s


if __name__ == '__main__':
    a = sys.argv[2:]
    if sys.argv[1] == 'test':
        sys.exit(0 if test(int(a[0]), a[1] if len(a) > 1 else None) else 1)
    run(int(a[0]), float(a[1]) if len(a) > 1 else 1e18, a[2] if len(a) > 2 and a[2] != '-' else None, a[3] if len(a) > 3 else None)
