"""The front of the counter model in closed form: the lifetime model (23 November 2026).

A group (d, n) with q groups to its right loses 3^q per round (skip.py), so its lifetime is l = n / 3^q rounds.
Take the round as time t in [0, 1): the borrow passes a group at depth q every 3^(m-q) bounces, evenly, so every
lifetime falls by 1 per unit of t and the front block n0 grows by 1 (bounces / 3^(depth it will have)). When a group
j runs out at time t, the empty group and its right neighbour (digit 1) merge into the left neighbour: the two groups
right of j-1 are gone, so every group left of j has two fewer groups to its right and its lifetime is multiplied by 9:

    l_(j-1) <- 9 l_(j-1) + l_(j+1),     l_i <- 9 l_i (i < j-1, and the front block),    j and j+1 removed.

At t = 1 the front block becomes the newborn group. E.g. one death at time t gives a newborn 9t + (1-t) = 1 + 8t,
and the two-round cycle of cycle.py is [1, 0, X, Y] -> [1, X+8, Y-1] -> [1, 0, X+7, Y-2]. All this drops terms of
relative size 3^-q, and one of them matters: in the cycle the aged newborn has exact size c and the next newborn
has excess 8c + 8 over 3^q (synthetic rounds: a single group j of size s gives newborn 3^(m-2) + 8 3^(j-1) s +
7 3^(j-1) + 1), so its lifetime c / 3^q grows 8-fold per cycle from about 3^-m and after about 0.53 m cycles the
cycle breaks ("chain blow-up"); that is what makes the list grow like sqrt(rounds). The chain is kept exactly:
c = (c0 + 8/7) 8^k - 8/7. c/front.c is the fast implementation (256-bit fixed point 2^-128, frozen runs, cycle skips,
right-end events as global x9 events); this file writes its input, reads its dumps, and tests it
(FRONT_EXE = path of the compiled front, default ./front).

The model is exact in its decisions only as long as its precision lasts: the exact model reads about one to two
more bits of the lifetimes per chain blow-up (`chaos`; a 2^-128 perturbation of every young lifetime reaches O(1)
after ~21,000 rounds at round 2e4 and ~100,000 rounds at round 1e6). front.c therefore follows the exact run for
a few dozen blow-ups and then only produces a typical front, not the real one (README, 23 November, closed form).

    python3 py/front.py lmtest R0 N P        # the lifetime model in Python (fixed point 2^-P with the 3^-m seeds)
                                             #   against skip.py, every round from round R0 for N rounds
    python3 py/front.py test R0 N [EVERY [TAIL]]   # c/front.c against skip.py: every EVERY-th round start, R0 .. R0+N
                                             #   (the last TAIL groups, default 80, are left out: frozen run)
    python3 py/front.py chaos R0 N [BITS]    # the exact model's sensitivity: perturb all lifetimes by < 2^-BITS
    python3 py/front.py input STATE.pkl EVENTS.pkl HORIZON OUT.txt [DUMPS]   # input for c/front.c from a state
"""
import os
import pickle
import subprocess
import sys
import time

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from skip import Sim, first_normal, pow3  # noqa: E402
from model import START  # noqa: E402

FRAC = 128
ONE = 1 << FRAC
FREEZE = 1 << (59 + FRAC)
EXE = os.environ.get('FRONT_EXE', os.path.abspath('front'))   # gcc -O2 -o front c/front.c -lquadmath


# ------------------------------------------------------------------ the model in Python (reference)
def to_fixed(G, P):
    m = len(G)
    return [(n << P) // (pow3(m - 1 - i) if i < m - 1 else 2) for i, (d, n) in enumerate(G)]


def round_lm(L, P, seeds=True):
    """One round of the lifetime model on L (fixed point 2^-P, front first); the newborn gets its exact seed
    (1 + 7 3^(j-1) for a single death at j) when P is large enough to hold it."""
    S = 1 << P
    t = F = 0
    nd, jd, ev = 0, None, []
    while True:
        j = min(range(len(L)), key=L.__getitem__)
        tj = L[j]
        if tj >= S:
            break
        tj = max(tj, t)
        F += tj - t
        t = tj
        ev.append((j, t))
        right = L[j + 1] - t
        if j >= 1:
            L[j - 1] = 9 * (L[j - 1] - t) + right + t
            for i in range(j - 1):
                L[i] = 9 * (L[i] - t) + t
            F = 9 * F
        else:
            F = 9 * F + right
        del L[j:j + 2]
        nd += 1
        jd = j
    F += S - t
    if seeds:
        c = 1 + (7 * 3 ** (jd - 1) if nd == 1 and jd >= 1 else 0)
        F += (c << P) // pow3(len(L))
    return [F] + [x - S for x in L], ev


def lmtest(R0, N, P, tail=40):
    r, n0, G = first_normal(START[0], START[1], 0)
    s = Sim(n0, G, r)
    while s.rounds < R0:
        s.step()
    L = to_fixed(s.state()[1], P)
    S = 1 << P
    worst, bad, k, slow0, nd = 0, 0, 0, s.slow_rounds, 0
    for k in range(N):
        L, ev = round_lm(L, P)
        nd += len(ev)
        if any(j >= len(L) - tail for j, _ in ev):
            print('a death near the right end in round', s.rounds + 1, ': stop')
            break
        s.step()
        if s.slow_rounds != slow0:
            print('an exact-model round at', s.rounds, ': stop')
            break
        E = to_fixed(s.state()[1], P)
        if len(E) != len(L):
            print('MISMATCH (length) at round', s.rounds)
            bad += 1
            break
        for a, b in zip(L[:-tail], E[:-tail]):
            worst = max(worst, abs(a - b) / max(S, abs(b)))
        if worst > 1e-6:
            print('MISMATCH (value) at round', s.rounds, worst)
            bad += 1
            break
    print('lifetime model vs skip.py: %d round starts from round %d, %d deaths, %d mismatches, worst relative error %.3g' % (
        k + 1, R0, nd, bad, worst))
    return bad == 0


# ------------------------------------------------------------------ input for c/front.c
def chain_of(c):
    """(c0, k) with c = (c0 + 8/7) 8^k - 8/7, k as large as possible."""
    v, k = 7 * c + 8, 0
    while v % 8 == 0 and (v // 8 - 8) % 7 == 0 and v // 8 >= 15:
        v //= 8
        k += 1
    c0 = (v - 8) // 7
    assert (7 * c0 + 8) * 8 ** k == 7 * c + 8
    return c0, k


def nodes_from_state(G, tail, charged_idx=()):
    """Nodes for front.c from exact groups G (round start, n0 = 2): the last `tail` groups become one frozen run
    (the right part, whose events are global events), groups with lifetime > 2^59 are frozen, the aged newborn
    (index 1) carries its exact chain when it is tiny."""
    m = len(G)
    out = []
    for i, (d, n) in enumerate(G[:m - tail]):
        q = m - 1 - i
        p = pow3(q)
        l = (n << FRAC) // p
        ch = 1 if i in charged_idx else 0
        if l > FREEZE:
            if out and out[-1][0] == 'F':
                out[-1] = ('F', out[-1][1] + 1, out[-1][2] | ch)
            else:
                out.append(('F', 1, ch))
            continue
        hc, c0, k = 0, 0, 0
        if i == 1 and n < p >> (FRAC + 2):
            c0, k = chain_of(n)
            hc = 1
        if i == 0 and 0 < n - p < p >> (FRAC + 2):
            c0, k = chain_of(n - p)
            hc = 1
            l = ONE
        out.append(('A', l, ch, hc, c0, k))
    out.append(('F', tail, 0))
    return out


def words(x):
    assert 0 <= x < 1 << 254
    return ' '.join(str((x >> (64 * i)) & ((1 << 64) - 1)) for i in (3, 2, 1, 0))


def unwords(ws):
    x = 0
    for w in ws:
        x = (x << 64) | int(w)
    if x >> 255:
        x -= 1 << 256
    return x


def write_input(path, tau0, horizon, nodes, globs, dumps):
    with open(path, 'w') as f:
        f.write('%d %d 0\n%d\n' % (tau0, horizon, len(nodes)))
        for x in nodes:
            if x[0] == 'F':
                f.write('F %d %d\n' % (x[1], x[2]))
            else:
                l = x[1]
                f.write('A %s %d %d %d %d\n' % (words(l), x[2], x[3], x[4], x[5]))
        f.write('%d\n' % len(globs))
        for tg, t in globs:
            f.write('%d %s\n' % (tg, words(t)))
        f.write('%d\n' % len(dumps))
        f.write(' '.join(str(x) for x in dumps) + '\n')


def read_dumps(text):
    """{tau: (m_total, [('A', l_fixed, charged, haschain, c0, k) | ('F', cnt, charged)])}, stats line, other lines"""
    dumps, stats, other = {}, None, []
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.startswith('DUMP'):
            p = ln.split()
            tau, mt = int(p[3]), int(p[5])
            nodes = []
            i += 1
            while lines[i] != 'END':
                q = lines[i].split()
                if q[0] == 'F':
                    nodes.append(('F', int(q[1]), int(q[2])))
                else:
                    nodes.append(('A', unwords(q[1:5]), int(q[5]), int(q[6]), int(q[7]), int(q[8])))
                i += 1
            dumps.setdefault(tau, (mt, nodes))
        elif ln.startswith('STATS'):
            stats = ln
        elif ln:
            other.append(ln)
        i += 1
    return dumps, stats, other


def expand(nodes):
    """lifetimes (float, None for frozen) per group"""
    out = []
    for x in nodes:
        if x[0] == 'F':
            out += [None] * x[1]
        else:
            out.append(x[1] / ONE)
    return out


def test(R0, N, every=1, tail=40):
    """c/front.c against skip.py: the lifetimes of all groups but the last `tail` at every `every`-th round start."""
    r, n0, G = first_normal(START[0], START[1], 0)
    s = Sim(n0, G, r)
    while s.rounds < R0:
        s.step()
    n0, G = s.state()
    R0 = s.rounds
    nodes = nodes_from_state(G, tail)
    dumps = list(range(R0 + every, R0 + N + 1, every))
    path = '/tmp/front_test_%d.txt' % os.getpid()
    write_input(path, R0, R0 + N, nodes, [], dumps)
    t0 = time.time()
    res = subprocess.run([EXE], stdin=open(path), capture_output=True, text=True)
    os.unlink(path)
    D, stats, other = read_dumps(res.stdout)
    tc = time.time() - t0
    tail0 = [n for _, n in G[-tail:]]
    checked = bad = 0
    worst = 0.0
    slow0 = s.slow_rounds
    for R in dumps:
        while s.rounds < R:
            s.step()
        if s.slow_rounds != slow0:
            print('skip.py used the exact model at round %d: stop' % s.rounds)
            break
        n0, E = s.state()
        k = R - R0
        exp_tail = [n - k * (pow3(tail - 1 - i) if i < tail - 1 else 2) for i, n in enumerate(tail0)]
        if [n for _, n in E[-tail:]] != exp_tail:
            print('an event at the right end before round %d: stop' % R)
            break
        if R not in D:
            print('MISMATCH: no dump at round', R, other[-3:])
            bad += 1
            break
        mt, nodes = D[R]
        L = expand(nodes)
        if mt != len(E) or len(L) != len(E):
            print('MISMATCH (groups) at round %d: front.c %d, exact %d' % (R, mt, len(E)))
            bad += 1
            break
        m = len(E)
        for i, ((d, n), l) in enumerate(zip(E[:-tail], L[:-tail])):
            q = m - 1 - i
            p = pow3(q)
            if l is None:
                if (n << FRAC) // p <= FREEZE // 2:
                    print('MISMATCH (frozen) at round %d index %d' % (R, i))
                    bad += 1
                break
            x = (n << 64) // p / 2.0 ** 64
            err = abs(x - l) / max(1.0, abs(x))
            worst = max(worst, err)
        if worst > 1e-6:
            print('MISMATCH (lifetime) at round %d: worst %.3g' % (R, worst))
            bad += 1
            break
        checked += 1
    print('front.c vs skip.py: %d round starts from round %d (every %d), %d mismatches, worst relative error %.3g, '
          'front.c %.1f s; %s' % (checked, R0, every, bad, worst, tc, stats))
    return bad == 0


def chaos(R0, N, bits=128, tail=80, seed=5):
    """Sensitivity of the exact model (skip.py): add to every group but the two chain carriers (index 0, 1) and
    the last `tail` a random multiple of 3 below 2^-bits of 3^q (its lifetime moves by < 2^-bits rounds) and
    follow both runs; prints the largest lifetime difference."""
    import math
    import random
    r, n0, G = first_normal(START[0], START[1], 0)
    s = Sim(n0, G, r)
    while s.rounds < R0:
        s.step()
    n0, G = s.state()
    m = len(G)
    rnd = random.Random(seed)
    G2 = list(G)
    for i in range(2, m - tail):
        q = m - 1 - i
        k = max(0, int(q - bits / math.log2(3)))
        G2[i] = (G2[i][0], G2[i][1] + 3 * rnd.randrange(3 ** k))
    a, b = Sim(n0, G, s.rounds), Sim(n0, G2, s.rounds)
    nxt = R0 + 1
    while a.rounds < R0 + N:
        a.step()
        while b.rounds < a.rounds:
            b.step()
        if a.rounds >= nxt:
            A, B = a.state()[1], b.state()[1]
            if len(A) != len(B):
                print('round %d: the two runs have different numbers of groups' % a.rounds)
                return
            mm = len(A)
            worst = max((abs(x - y).bit_length() - (mm - 1 - i) * math.log2(3), i)
                        for i, ((_, x), (_, y)) in enumerate(zip(A[:-tail], B[:-tail])))
            print('round %d, %d groups: largest lifetime difference 2^%.1f (index %d)' % (a.rounds, mm, worst[0], worst[1]),
                  flush=True)
            nxt = R0 + int((nxt - R0) * 1.4) + 1


def far_input(state, events, horizon_round, out, dumps=()):
    """Input for the far run: STATE = (n0, G, R) at a round start (n0 = 2), EVENTS = the right-end rounds (as
    listed by the run in the README: (R, E, events, groups before, after, due)), the right part = the block of
    the rightmost charged pair and everything right of it. Times are relative to R."""
    from charge import charges
    n0, G, R = pickle.load(open(state, 'rb'))
    ch = charges(G)
    jx = ch[-1][0]
    tail = len(G) - jx
    nodes = nodes_from_state(G, tail, charged_idx=[i for i, _ in ch[:-1]])
    globs = []
    for (Re, E, ev, before, after, due) in pickle.load(open(events, 'rb')):
        if after == before - 1 and 'A' not in ev:          # two groups gone at the right end (plus the newborn)
            q, n, _ = due[0]
            globs.append((Re - R, (n << FRAC) // pow3(q)))
    write_input(out, 0, horizon_round - R, nodes, globs, [d - R for d in dumps])
    print('far input: %d groups, %d nodes (%d active), right part %d groups, %d global events, horizon %d rounds' % (
        len(G), len(nodes), sum(1 for x in nodes if x[0] == 'A'), tail, len(globs), horizon_round - R))
    return nodes, globs


if __name__ == '__main__':
    a = sys.argv[2:]
    if sys.argv[1] == 'chaos':
        chaos(int(a[0]), int(a[1]), int(a[2]) if len(a) > 2 else 128)
    elif sys.argv[1] == 'input':
        far_input(a[0], a[1], int(a[2]), a[3], [int(x) for x in a[4:]])
    elif sys.argv[1] == 'lmtest':
        sys.exit(0 if lmtest(int(a[0]), int(a[1]), int(a[2])) else 1)
    elif sys.argv[1] == 'test':
        sys.exit(0 if test(int(a[0]), int(a[1]), int(a[2]) if len(a) > 2 else 1, int(a[3]) if len(a) > 3 else 80) else 1)
