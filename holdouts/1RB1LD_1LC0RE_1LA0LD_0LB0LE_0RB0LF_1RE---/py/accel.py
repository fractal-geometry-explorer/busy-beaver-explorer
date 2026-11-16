"""Many ticks of the macro map (macro.py) at once (16 November 2026).

Between events a tick is a decrement of a base-3 counter.  With separators 0..k-1 standard digits (c = 2, r = 1,
z = 0, the block before separator i being xs[i]) and separator k a wall (`1`, `01101`, `00101`) or the far end:

  * the borrow of tick t (t = 0, 1, ...) reaches separator i iff 3^i divides V - t, where V = sum digit_i 3^i
    (i < k); it is a c -> r (no block change) iff V - t = 2*3^i mod 3^(i+1), otherwise xs[i] loses one;
  * borrows reaching the wall cycle `1` (D: xs[k] - 1, xs[k+1] - 1, +6 steps) -> `01101` (A: xs[k] - 1) ->
    `00101` (C: +12 steps) -> `1`;
  * the steps of a tick are 30y + 5 pos/2 + 210 + 13 nb + e (macro.tick), so the sum over T ticks needs the sums of
    the block lengths seen by the borrows; they are sums of arithmetic progressions (`seen`).

T is chosen so that every block that a borrow reaches stays >= MARGIN (3, so that macro.retok never re-cuts the tokens) and,
without a wall, the borrow never reaches the far end.  `py/accel.py test` compares the skips with tick-by-tick
moves of macro.py (state and step count); `run` follows the map with skips and with macro.move for everything else
(every event is computed by macro.event, exactly as before).

    python3 py/accel.py test SECONDS [CAP [START.pkl]]   # skips against macro.tick
    python3 py/accel.py run SECONDS [verify] [coracle|ocheck] [START.pkl] [CKPT.pkl]
                                     # coracle: events by c/oracle.c (ORACLE=path of the binary);
                                     # ocheck: the same, every call also made in Python and compared
"""
import os
import pickle
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import macro as M  # noqa: E402

DIG = {'010101': 2, '01': 1, '00': 0}
SEP = {2: '010101', 1: '01', 0: '00'}
WALL = ['1', '01101', '00101']            # D, A, C in this order
MARGIN = 3


def fcount(lo, hi, m, r):
    """#{x in [lo, hi) : x = r mod m}."""
    if hi <= lo:
        return 0
    return (hi - 1 - r) // m - (lo - 1 - r) // m


def seen(x0, digit, beta):
    """Sum of the block lengths seen by beta borrows into a separator whose digit starts at `digit`, the block
    being x0 at the first one; the borrow lowers the block unless the digit is 2 (c -> r)."""
    # dec(u) = number of decrementing borrows among the first u; sum_{u < beta} dec(u)
    # a borrow number u is c -> r iff (digit - u) mod 3 == 2, i.e. u = (digit + 1) mod 3 (mod 3)
    r = (digit + 1) % 3
    tot = beta * (beta - 1) // 2
    # sum_{u<beta} #{v < u : v = r mod 3} = sum over such v <= beta-2 of (beta - 1 - v)
    if beta - 2 >= r:
        n = (beta - 2 - r) // 3 + 1
        tot -= n * (beta - 1 - r) - 3 * n * (n - 1) // 2
    return beta * x0 - tot


def plan(st):
    """The counter part: (k, digits, wall index or None) or None if the word does not have the standard shape."""
    y, xs, ss, tail = st
    digits = []
    k = 0
    while k < len(ss) and ss[k] in DIG:
        digits.append(DIG[ss[k]])
        k += 1
    if k < len(ss) and ss[k] in WALL:
        return k, digits, WALL.index(ss[k])
    return k, digits, None          # the far end, or a separator of another kind: the borrow must not reach it


def effect(st, k, digits, w, T):
    """(new xs prefix, steps) for T ticks, or None if not allowed."""
    y, xs, ss, tail = st
    V = sum(d * 3 ** i for i, d in enumerate(digits))
    if w is None and T > V:
        return None
    if w is not None and k + 1 >= len(xs):
        return None
    steps = 30 * (T * y + 2 * T * (T - 1)) + 210 * T
    new = list(xs[:k + 2]) if w is not None else list(xs[:k + 1])
    touched = set()
    for i in range(k + 1):
        p = 3 ** i
        beta = V // p - (V - T) // p                    # borrows reaching separator i
        if beta > 0:
            touched.add(i)
        if i < k:
            dig = digits[i]
            gam = fcount(V - T + 1, V + 1, 3 * p, 2 * p)  # those that find digit 2: t with V - t = 2p mod 3p
            new[i] = xs[i] - (beta - gam)
            s = seen(xs[i], dig, beta)
            steps += 10 * s if i == 0 else 5 * beta + 10 * s + 13 * beta
        else:
            # the wall (or nothing, if w is None: beta = 0 then)
            if w is None:
                assert beta == 0
                break
            # wall borrows b = 0..beta-1 have type (w + b) mod 3: 0 = D, 1 = A, 2 = C
            nD = fcount(0, beta, 3, (0 - w) % 3)
            nA = fcount(0, beta, 3, (1 - w) % 3)
            nC = beta - nD - nA
            # the blocks seen: pos adds 4*xs[i] for borrows reaching i >= 1 (the B before it); xs[k] drops at D, A
            s = seen_wall(xs[i], w, beta)
            steps += 10 * s if i == 0 else 5 * beta + 10 * s + 13 * beta
            steps += 6 * nD + 12 * nC
            new[i] = xs[i] - nD - nA
            new[i + 1] = xs[i + 1] - nD
            if beta > 0:
                touched.add(i + 1)
    if any(new[i] < MARGIN for i in touched):
        return None
    return new, steps


def seen_wall(x0, w, beta):
    """Sum of xs[k] seen by beta borrows into the wall; it drops after D and A, i.e. unless the type is C."""
    # same as seen() with 'C' playing the part of digit 2: type (w + u) mod 3 == 2 iff u = (2 - w) mod 3
    r = (2 - w) % 3
    tot = beta * (beta - 1) // 2
    if beta - 2 >= r:
        n = (beta - 2 - r) // 3 + 1
        tot -= n * (beta - 1 - r) - 3 * n * (n - 1) // 2
    return beta * x0 - tot


def apply(st, k, digits, w, T, new):
    y, xs, ss, tail = st
    V = sum(d * 3 ** i for i, d in enumerate(digits))
    Vn = (V - T) % (3 ** k) if k else 0
    for i in range(k):
        ss[i] = SEP[(Vn // 3 ** i) % 3]
    if w is not None:
        beta = V // 3 ** k - (V - T) // 3 ** k
        ss[k] = WALL[(w + beta) % 3]
    xs[:len(new)] = new
    st[0] = y + 4 * T


def maxskip(st):
    """(T, plan, new, steps) for the largest allowed T >= 2, or None."""
    p = plan(st)
    if p is None:
        return None
    k, digits, w = p
    if effect(st, k, digits, w, 2) is None:
        return None
    lo, hi = 2, 2
    while effect(st, k, digits, w, hi * 2) is not None:
        hi *= 2
        if hi > 1 << 20000:
            break
    hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if effect(st, k, digits, w, mid) is not None:
            lo = mid
        else:
            hi = mid
    new, steps = effect(st, k, digits, w, lo)
    return lo, p, new, steps


def skip(st):
    """Apply the largest skip; returns (ticks, steps) or None."""
    r = maxskip(st)
    if r is None:
        return None
    T, (k, digits, w), new, steps = r
    apply(st, k, digits, w, T, new)
    return T, steps


# ------------------------------------------------------------------ the event oracle in C (c/oracle.c)
class COracle:
    """macro.oracle, computed by c/oracle.c (same rules; NONE from C, e.g. out of tape room, falls back to the
    Python oracle).  With check=True every call is also made in Python and compared."""

    def __init__(self, exe, check=False):
        import subprocess
        self.p = subprocess.Popen([exe], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.check = check
        self.py = M.oracle
        self.calls = 0

    def __call__(self, y, u, maxsteps=10 ** 8):
        self.p.stdin.write('%d %s %d\n' % (y, u if u else '-', maxsteps))
        self.p.stdin.flush()
        a = self.p.stdout.readline().split()
        self.calls += 1
        if a[0] == 'NONE':
            r = self.py(y, u, maxsteps)
        elif a[0] == 'HALT':
            r = ('HALT', int(a[1]))
        else:
            r = (int(a[0]), '' if a[1] == '-' else a[1], int(a[2]))
        if self.check:
            q = self.py(y, u, maxsteps)
            assert q == r, ('C oracle differs', y, u, q, r)
        return r


def use_coracle(check=False):
    exe = os.environ.get('ORACLE', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'c', 'oracle'))
    M.oracle = COracle(exe, check)


def copy(st):
    return [st[0], st[1][:], st[2][:], st[3]]


def test(seconds, cap=None, start=None):
    """From the first tick (or a checkpoint): at every skip, also do the same ticks one by one with macro.tick and
    compare (with `cap`, the skips are cut to at most cap ticks, so that the comparison stays cheap)."""
    if start:
        t, _, _, st = pickle.load(open(start, 'rb'))
    else:
        t, n, w = M.START
        st = M.state(n, w)
    t0 = time.time()
    nskip = nt = 0
    import random
    random.seed(5)
    while time.time() - t0 < seconds:
        r = maxskip(st)
        if r is not None:
            T, (k, digits, wl), new, steps = r
            T = random.choice([T, random.randint(2, T)])
            if cap:
                T = min(T, random.randint(2, cap))
            new, steps = effect(st, k, digits, wl, T)
            ref = copy(st)
            rs = 0
            for _ in range(T):
                d = M.tick(ref)
                assert d is not None, 'a tick of the skip is not a plain tick'
                rs += d
            apply(st, k, digits, wl, T, new)
            if ref != st or rs != steps:
                print('MISMATCH', T, ref[:2], st[:2], rs, steps)
                return False
            nskip += 1
            nt += T
            t += steps
        d, e = M.move(st)
        if isinstance(d, tuple):
            print('HALT', d)
            return False
        t += d
    print('OK: %d skips (%d ticks) agree with tick-by-tick moves, state and steps; reached step %d' % (nskip, nt, t))
    return True


def summ(st):
    return 'y=%d K=%d xs=%s ss=%s tail=%s' % (st[0], len(st[1]), st[1], st[2], st[3])


def run(seconds, verify=False, start=None, ckpt=None):
    if verify:
        M.VERIFY = True
    if start:
        t, moves, nev, st = pickle.load(open(start, 'rb'))
    else:
        t, n, w = M.START
        st = M.state(n, w)
        moves = nev = 0
    t0 = time.time()
    last = t0
    ticks = 0
    while time.time() - t0 < seconds:
        r = skip(st)
        if r is not None:
            ticks += r[0]
            t += r[1]
        before = summ(st)
        d, e = M.move(st)
        moves += 1
        ticks += 1
        if isinstance(d, tuple):
            print('HALT-EVENT', t, before, d, flush=True)
            break
        t += d
        if e:
            nev += 1
            print('EV %d step %d (%.3e) ticks %d FROM %s TO %s' % (nev, t, float(t), ticks, before[:2000], summ(st)[:2000]), flush=True)
        if time.time() - last > 600:
            last = time.time()
            print('AT step %d ticks %d events %d %s' % (t, ticks, nev, summ(st)[:3000]), flush=True)
            if ckpt:
                pickle.dump((t, moves, nev, st), open(ckpt + '.tmp', 'wb'))
                os.replace(ckpt + '.tmp', ckpt)
    print('END step %d ticks %d events %d %s' % (t, ticks, nev, summ(st)[:5000]), flush=True)
    if ckpt:
        pickle.dump((t, moves, nev, st), open(ckpt + '.tmp', 'wb'))
        os.replace(ckpt + '.tmp', ckpt)


if __name__ == '__main__':
    a = sys.argv[2:]
    if sys.argv[1] == 'test':
        sys.exit(0 if test(float(a[0]), int(a[1]) if len(a) > 1 else None, a[2] if len(a) > 2 else None) else 1)
    if 'coracle' in a or 'ocheck' in a:
        use_coracle('ocheck' in a)
    pk = [x for x in a[1:] if x.endswith('.pkl')]
    run(float(a[0]), 'verify' in a, pk[0] if pk and os.path.exists(pk[0]) and len(pk) > 1 else None, pk[-1] if pk else None)
