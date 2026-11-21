"""The right part of the counter model on its own (21 November 2026).

A group with q groups to its right is passed exactly 3^q - 1 times in every round (the last group twice), whatever
happens to its left (skip.py).  So the groups from some block X to the right end evolve on their own, round by round,
and the only effect of the groups left of X is what they merge into X (merges only ever add to X).  This script runs
X and everything right of it with *nothing* fed into X: two sentinel groups left of X (neutral pairs, lifetimes a
million times X's, so they never run out) stand for a front that survives, and after every round everything left of
the sentinels (the new front block) is deleted.  Between events whole runs of rounds are done in closed form
(every group loses K * 3^q); a round in which some group may run out is done by the exact model (model.py).

With X the charged block of round 49,669, this gives the next events at the right end exactly, the A phases among
them, and a lower bound for the charged block at every round (the real block holds at least as much, as long as
some group survives to its left).

    python3 py/rightpart.py test [ROUNDS]       # against skip.py from blank tape: the groups right of the split
    python3 py/rightpart.py run STATE.pkl [N]    # STATE = (n0, G, rounds) at a round start; N events (default all)
    python3 py/rightpart.py probe STATE.pkl FRONT.pkl OUT.pkl
        # forecast (heuristic): the front of FRONT.pkl (a later cycle.py state) put in front of the right part as it
        # is just before the first A phase after STATE, and that A round run by the exact model; OUT gets (n0, G)
"""
import os
import pickle
import sys

sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import START, bounce_lean, jump  # noqa: E402
from charge import charges  # noqa: E402

SENT = 10 ** 40


def rate(q):
    return 3 ** q if q else 2


def lim(q):
    return rate(q) + 2


def normal(G):
    return len(G) >= 2 and all(d == 2 for d, _ in G) and G[-1] != (2, 0)


def exact_round(n0, G):
    """From a round start, the exact model up to the next round start: (n0', G', E events, events) or None."""
    ev, E = [], 0
    while True:
        _, n0, G = jump(n0, G)
        r = bounce_lean(n0, G)
        if r[0] != 'next':
            return None, (n0, G), E, ev + ['HALT']
        n0, G = r[1], r[2]
        if r[3] is not None:
            ev.append(r[3])
        if r[3] == 'E':
            E += 1
        if r[3] in ('D', 'A') and normal(G):
            return n0, G, E, ev


def with_sentinels(H):
    """H = X and the groups right of it; two neutral sentinels in front (n = 1 mod 3 before a digit 2)."""
    sl = SENT + 10 ** 6 * (H[0][1] // rate(len(H) - 1))
    return [(2, sl * rate(len(H) + 1) + 1), (2, sl * rate(len(H)) + 1)] + H


def advance(G, R, K):
    m = len(G)
    return [(2, n - K * rate(m - 1 - i)) for i, (d, n) in enumerate(G)], R + K


def run(H, R, maxR=None, maxev=None, log=print):
    """H: X and the groups right of it at a round start (round R); X is re-found after every event as the left
    block of the rightmost charged pair."""
    G = with_sentinels(H)
    n0, events = 2, 0
    while True:
        m = len(G)
        K = min((0 if n < lim(m - 1 - i) else (n - lim(m - 1 - i)) // rate(m - 1 - i) + 1)
                for i, (d, n) in enumerate(G) if i >= 2)
        if maxR is not None and R + K >= maxR:
            G, R = advance(G, R, maxR - R)
            return 'maxR', R, G[2:]
        if K > 0:
            G, R = advance(G, R, K)
            continue
        old = len(G)
        n0b, G2, E, ev = exact_round(n0, G)
        if n0b is None:
            log('HALT in round %d, events %s' % (R, ev))
            return 'halt', R, G
        R += E
        events += 1
        ch = charges(G2)
        if not ch:
            log('round %d: no charged pair left (events %s)' % (R, ev))
            return 'nocharge', R, G2
        j = ch[-1][0]
        H = G2[j:]
        log('round %d: events %s, %d -> %d groups, X has %d groups to its right, lifetimes X %.4g, next %.4g' % (
            R, [e for e in ev if e != 'E'], old - 2, len(H), len(H) - 1,
            H[0][1] / rate(len(H) - 1), H[1][1] / rate(len(H) - 2) if len(H) > 1 else 0))
        G = with_sentinels(H)
        if len(H) < 3 or (maxev is not None and events >= maxev):
            return 'stop', R, H


def test(upto=60000, depth=30):
    """skip.py from blank tape; at round 2000 split off the last `depth` groups; compare every group strictly right
    of X at every round start up to `upto` (the real X gets merges from the left, the model's does not)."""
    from skip import Sim, first_normal
    r0, n0, G = first_normal(START[0], START[1], 0)
    s = Sim(n0, G, r0)
    while s.rounds < 2000:
        s.step()
    n0, G = s.state()
    R = s.rounds
    H = G[-depth:]
    ok = bad = 0
    while s.rounds < upto and not s.halted:
        s.step()
        st, R2, H2 = run_plain(H, R, s.rounds)
        n0r, Gr = s.state()
        if H2[1:] == Gr[len(Gr) - len(H2) + 1:]:
            ok += 1
        else:
            bad += 1
            print('MISMATCH at round', s.rounds, len(H2), H2[-3:], Gr[-3:])
            return False
        H, R = H2, R2
    print('%d round starts: the %d..%d groups right of X agree with skip.py (rounds 2000 to %d, %d mismatches)' % (
        ok, len(H) - 1, depth - 1, s.rounds, bad))
    return bad == 0


def run_plain(H, R, target):
    """X = H[0] kept as the leftmost tracked group: run to round `target` exactly (no sentinel bookkeeping besides
    the two sentinels); X is re-found as the group that still has the same number of groups right of it plus
    the change at the right end."""
    G = with_sentinels(H)
    n0 = 2
    while R < target:
        m = len(G)
        K = min((0 if n < lim(m - 1 - i) else (n - lim(m - 1 - i)) // rate(m - 1 - i) + 1)
                for i, (d, n) in enumerate(G) if i >= 2)
        K = min(K, target - R)
        if K > 0:
            G, R = advance(G, R, K)
            continue
        n0b, G2, E, ev = exact_round(n0, G)
        assert n0b is not None and E == 1, ev
        R += 1
        # drop the new front block and the sentinels (the last group of sentinel size) and put new sentinels
        m2 = len(G2)
        k = max(i for i, (d, n) in enumerate(G2) if n >= SENT * rate(m2 - 1 - i))
        G = with_sentinels(G2[k + 1:])
    return 'ok', R, G[2:]


def probe(state, front, out):
    n0, G, R = pickle.load(open(state, 'rb'))
    H = G[charges(G)[0][0]:]
    while True:                      # right-end events up to the start of the round that holds the A phase
        Hf, Rf = fast_forward(H, R)
        if 'A' in exact_round(2, with_sentinels(Hf))[3]:
            H, R = Hf, Rf
            break
        st, R, H = run(H, R, maxev=1, log=lambda *a: None)
    n0f, Gf, Rf2 = pickle.load(open(front, 'rb'))
    j = charges(Gf)[0][0]
    G = Gf[:j] + H
    print('round %d: front of round %d (%d groups) + right part (%d groups)' % (R, Rf2, j, len(H)), flush=True)
    n0, G2, E, ev = exact_round(2, G)
    if n0 is None:
        print('HALT in the A round', ev)
        return
    from charge import n0rel
    print('after the A round: events %s, %d groups, n0 %d digits, n0 + d1 = 1 mod 3: %s, charged pairs %s' % (
        ev, len(G2), len(str(n0)), n0rel(n0, G2), [(len(G2) - a, o) for a, o in charges(G2)]))
    pickle.dump((n0, G2), open(out, 'wb'))


def fast_forward(H, R):
    """H at the start of the next round in which some group may run out"""
    m = len(H)
    K = min((0 if n < lim(m - 1 - i) else (n - lim(m - 1 - i)) // rate(m - 1 - i) + 1) for i, (d, n) in enumerate(H))
    return advance(H, R, K)


if __name__ == '__main__':
    if sys.argv[1] == 'probe':
        probe(*sys.argv[2:5])
        sys.exit(0)
    if sys.argv[1] == 'test':
        sys.exit(0 if test(int(sys.argv[2]) if len(sys.argv) > 2 else 60000) else 1)
    n0, G, R = pickle.load(open(sys.argv[2], 'rb'))
    i = charges(G)[0][0]
    res = run(G[i:], R, maxev=int(sys.argv[3]) if len(sys.argv) > 3 else None)
    print(res[0], 'at round', res[1])
