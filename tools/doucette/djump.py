#!/usr/bin/env python3
"""Fast orbits of the five Doucette-family maps (the halting questions of five BB(6) holdouts).

Each map is  D -> D + alpha * floor(D / b^(v+1)) + beta(v, rho)  where  D = b^v * (b*a + rho),  rho != 0,
except at a few exceptional values (odd part 1 or 3 in base 2, a pure power of 3 in base 3), which are the only
places the machine can halt.  See tools/doucette/README.md.

The algorithm uses the shift identity (proved in Lean, holdouts/.../lean/Shift.lean):

    if D = b^m * X + L with X >= 1 and v = v_b(L) <= m - 2, then
    F(D) = b^(m-v-1) * (b^(v+1) + alpha) * X + F(L)

so the next v (and rho) depend only on L, and k steps can be taken on the low part alone.  A recursive
divide-and-conquer on the low digits (as for fast Collatz trajectories) takes N steps in about O(M(n) log n)
time, n the size of the final term.  Inside a jump D cannot be exceptional (its odd part is at least b^2), so
halting values can only occur at the exact top-level steps, which follow the Lean definition `G` literally.

usage: djump.py MACHINE STEPS [--check N] [--out FILE] [--base B]
"""
import sys, time, hashlib, json, argparse, resource
import gmpy2
from gmpy2 import mpz

MACHINES = {
    # name: (b, alpha, beta(v, rho), start state (D, r))
    'SN':  ('1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD', 2, 3, lambda v, r: v,         (6, 1)),
    'M31': ('1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE', 2, 1, lambda v, r: v,         (5, 1)),
    'M53': ('1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC', 2, 1, lambda v, r: v + 1,     (5, 2)),
    'M14': ('1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB', 2, 1, lambda v, r: v + 2,     (6, 1)),
    'M86': ('1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB', 3, 1, lambda v, r: v + r + 2, (4, 1)),
}


def val_part(b, D):
    """(v, part) with D = b^v * part, b does not divide part."""
    if b == 2:
        v = gmpy2.bit_scan1(D)
        return v, D >> v
    p, v = gmpy2.remove(D, b)
    return v, p


def exact_step(name, D, r):
    """One step of the Lean map `G` of the machine (Doucette.lean / Collatz.lean), on (D, r).
    Returns None for a halt, else (D', r')."""
    if name == 'SN':
        v, E = val_part(2, D)
        if E == 1:
            return None
        return D + v + 3 * (E // 2), 1
    if name == 'M31':
        v, E = val_part(2, D)
        if E == 1:
            return None
        if E == 3:
            return D + v + 3, 1
        return D + E // 2 + v, 1
    if name == 'M53':
        v, E = val_part(2, D)
        if E == 1:
            return None
        if E == 3:
            t = D + v + r
            return t + 1, (2 if t % 2 == 0 else 1)
        return D + E // 2 + v + r, 1
    if name == 'M14':
        v, E = val_part(2, D)
        if E == 1:
            return None
        if E == 3 and v % 2 == 0 and v != 0:
            return (3 * D + 3 * v + 10) // 2, 1
        return D + E // 2 + v + 2, 1
    if name == 'M86':
        v, E = val_part(3, D)
        if E == 1:
            t = (v + r) % 3
            if t == 1:
                return None
            if t == 2:
                return D + v + r + 2, 1
            return D + v + r, 2
        return D + E // 3 + v + r + E % 3 + 1, 1
    raise ValueError(name)


class Run:
    def __init__(self, name, base=600):
        self.name = name
        _, self.b, self.alpha, self.beta, _ = MACHINES[name]
        self.base = base
        self.k = 0                     # steps taken
        self.hist = {}                 # (v, rho) -> count
        self.vmax = -1
        self.vrec = []                 # (step index, v) at each new record of v
        self.pw = {}
        self.limit = None              # stop jumps at this step count
        self.pairs = None              # optional: counts of consecutive (v, v') pairs
        self.last = None

    def bpow(self, e):
        if self.b == 2:
            return mpz(1) << e
        p = self.pw.get(e)
        if p is None:
            p = mpz(3) ** e
            if len(self.pw) < 4096:
                self.pw[e] = p
        return p

    def note(self, v, rho):
        key = (v, rho)
        self.hist[key] = self.hist.get(key, 0) + 1
        if self.pairs is not None:
            if self.last is not None:
                kk = (min(self.last, 9), min(v, 9))
                self.pairs[kk] = self.pairs.get(kk, 0) + 1
            self.last = v
        if v > self.vmax:
            self.vmax = v
            self.vrec.append((self.k, v))

    def base_jump(self, L, m):
        """Steps on the low part L of D = b^m X + L (X >= 1 unknown) while they are certain.
        Returns (L', s, c): D' = b^(m-s) * c * X + L'."""
        b, alpha, beta = self.b, self.alpha, self.beta
        L = int(L)
        s = 0
        c = 1
        if b == 2:
            lim = self.limit
            while L and self.k < lim:
                v = (L & -L).bit_length() - 1
                if v + 2 > m - s:
                    break
                self.note(v, 1)
                L = L + alpha * (L >> (v + 1)) + beta(v, 1)
                c *= (1 << (v + 1)) + alpha
                s += v + 1
                self.k += 1
        else:
            lim = self.limit
            while L and self.k < lim:
                v = 0
                q = L
                while q % 3 == 0:
                    q //= 3
                    v += 1
                if v + 2 > m - s:
                    break
                rho = q % 3
                self.note(v, rho)
                L = L + alpha * (q // 3) + beta(v, rho)
                c *= 3 ** (v + 1) + alpha
                s += v + 1
                self.k += 1
        return mpz(L), s, mpz(c)

    def base_jump_one(self, L, m):
        """At most one certain step on a (large) low part L."""
        if L == 0:
            return L, 0, mpz(1)
        v, q = val_part(self.b, L)
        if v + 2 > m:
            return L, 0, mpz(1)
        rho = int(q % self.b)
        self.note(v, rho)
        self.k += 1
        L = L + self.alpha * (q // self.b) + self.beta(v, rho)
        return L, v + 1, self.bpow(v + 1) + self.alpha

    def split(self, L, m):
        if self.b == 2:
            return L >> m, L & ((mpz(1) << m) - 1)
        return gmpy2.f_divmod(L, self.bpow(m))

    def jump(self, L, m):
        if m <= self.base:
            return self.base_jump(L, m)
        m1 = m // 2
        H1, L1 = self.split(L, m1)
        L1p, s1, c1 = self.jump(L1, m1)
        if self.k >= self.limit:
            L2 = self.bpow(m1 - s1) * c1 * H1 + L1p if self.b != 2 else ((c1 * H1) << (m1 - s1)) + L1p
            return L2, s1, c1
        if s1 == 0:
            # the next valuation is at least m1 - 1: one direct step on L, then go on
            Lp, s, c = self.base_jump_one(L, m)
            if s == 0:
                return L, 0, mpz(1)
            L3, s3, c3 = self.jump(Lp, m - s)
            return L3, s + s3, c * c3
        L2 = self.bpow(m1 - s1) * c1 * H1 + L1p if self.b != 2 else ((c1 * H1) << (m1 - s1)) + L1p
        m2 = m - s1
        H2, L2lo = self.split(L2, m2)
        L2p, s2, c2 = self.jump(L2lo, m2)
        if self.b == 2:
            L3 = ((c2 * H2) << (m2 - s2)) + L2p
        else:
            L3 = self.bpow(m2 - s2) * c2 * H2 + L2p
        return L3, s1 + s2, c1 * c2


def sha(D):
    """SHA-256 of the big-endian bytes of D (portable)."""
    return hashlib.sha256(int(D).to_bytes((int(D.bit_length()) + 7) // 8, 'big')).hexdigest()


def digits(b, D):
    return D.bit_length() if b == 2 else gmpy2.num_digits(D, 3)


def run(name, steps, base=600, log=None, every=None, checkpoints=(), start=None, pairs=False, save_dir='', maxm=0):
    R = Run(name, base)
    if pairs:
        R.pairs = {}
    b = R.b
    D, r = MACHINES[name][4]
    D = mpz(D)
    if start is not None:
        D, r, R.k = start
    cps = sorted(checkpoints)
    out = {}
    t0 = time.time()
    next_report = (R.k + every) if every else None
    while R.k < steps:
        n = digits(b, D)
        if r != 1 or n < 64:
            # exact step (Lean's G), with the exceptions and the halt
            v, E = val_part(b, D)
            R.note(v, int(E % b))
            nxt = exact_step(name, D, r)
            R.k += 1
            if nxt is None:
                out['halt'] = R.k
                break
            D, r = mpz(nxt[0]), nxt[1]
        else:
            m = n - 3
            if maxm:
                m = min(m, maxm)
            R.limit = min([c for c in cps if c > R.k] + [steps])
            H, L = R.split(D, m)
            k0 = R.k
            Lp, s, c = R.jump(L, m)
            if R.k == k0:
                # no certain step: take one exact step
                v, E = val_part(b, D)
                R.note(v, int(E % b))
                nxt = exact_step(name, D, r)
                R.k += 1
                if nxt is None:
                    out['halt'] = R.k
                    break
                D, r = mpz(nxt[0]), nxt[1]
            else:
                D = (((c * H) << (m - s)) + Lp) if b == 2 else R.bpow(m - s) * c * H + Lp
        while cps and R.k >= cps[0]:
            c0 = cps.pop(0)
            if R.k == c0:
                out.setdefault('checkpoints', {})[c0] = {
                    'digits': int(digits(b, D)),
                    'sha256': sha(D),
                    'low64': int(D % (mpz(1) << 64)),
                }
                if save_dir:
                    open('%s/%s_%d.bin' % (save_dir, name, c0), 'wb').write(gmpy2.to_binary(D))
        if every and R.k >= next_report:
            if log:
                log.write('%s k=%d digits=%d vmax=%d t=%.1fs\n' % (name, R.k, digits(b, D), R.vmax,
                                                                    time.time() - t0))
                log.flush()
            next_report += every
    out.update({'machine': MACHINES[name][0], 'steps': R.k, 'digits': int(digits(b, D)), 'vmax': R.vmax,
                'vrecords': R.vrec, 'hist': {'%d,%d' % kk: cnt for kk, cnt in sorted(R.hist.items())},
                'seconds': round(time.time() - t0, 1),
                'final_sha256': sha(D), 'final_r': r,
                'pairs': ({'%d,%d' % kk: cnt for kk, cnt in sorted(R.pairs.items())} if R.pairs is not None else None),
                'peak_rss_mb': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024,
                'final_low64': int(D % (mpz(1) << 64))})
    return out, D


def naive(name, steps):
    D, r = MACHINES[name][4]
    D = mpz(D)
    seq = [D]
    for _ in range(steps):
        nxt = exact_step(name, D, r)
        if nxt is None:
            break
        D, r = mpz(nxt[0]), nxt[1]
        seq.append(D)
    return seq


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('machine', choices=sorted(MACHINES))
    ap.add_argument('steps', type=int)
    ap.add_argument('--check', type=int, default=0, help='compare with the naive map at every step up to N')
    ap.add_argument('--base', type=int, default=600)
    ap.add_argument('--every', type=int, default=0)
    ap.add_argument('--cp', type=str, default='', help='comma-separated checkpoint step counts')
    ap.add_argument('--out', type=str, default='')
    ap.add_argument('--save', type=str, default='', help='write the final term (gmpy2 binary) here')
    ap.add_argument('--save-dir', type=str, default='', help='also save the term at each checkpoint here (for --resume)')
    ap.add_argument('--maxm', type=int, default=0, help='cap the low window of a top-level jump (digits), to bound memory')
    ap.add_argument('--pairs', action='store_true', help='count consecutive valuation pairs (capped at 9)')
    ap.add_argument('--resume', type=str, default='', help='FILE,K,R: start from the term saved in FILE, at step K, with r = R')
    a = ap.parse_args()
    if a.check:
        seq = naive(a.machine, a.check)
        bad = 0
        for k in sorted(set([1, 2, 3, 10, 100, 1000] + list(range(0, a.check + 1, max(1, a.check // 50))))):
            if k > len(seq) - 1:
                continue
            o, D = run(a.machine, k, base=a.base)
            if D != seq[k]:
                print('MISMATCH at', k)
                bad += 1
        print('check', a.machine, 'ok' if not bad else 'FAILED', 'up to', len(seq) - 1)
        sys.exit(1 if bad else 0)
    cps = [int(x) for x in a.cp.split(',') if x]
    start = None
    if a.resume:
        f, k, r = a.resume.split(',')
        start = (gmpy2.from_binary(open(f, 'rb').read()), int(r), int(k))
    o, D = run(a.machine, a.steps, base=a.base, log=sys.stderr, every=a.every, checkpoints=cps, start=start, pairs=a.pairs, save_dir=a.save_dir, maxm=a.maxm)
    s = json.dumps(o, indent=1)
    if a.out:
        open(a.out, 'w').write(s)
    else:
        print(s)
    if a.save:
        open(a.save, 'wb').write(gmpy2.to_binary(D))
