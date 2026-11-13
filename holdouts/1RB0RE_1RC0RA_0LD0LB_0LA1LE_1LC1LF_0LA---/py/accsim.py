"""Accelerated simulator for 1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA--- built on the pass map of passes.py.

The tape at a left-end sample is held as items instead of pairs:

    c                     the counter (the word a^c next to the left end)
    L = [[m, k], ...]     finished blocks (2,1)(1,m), run-length coded, left of the frontier
    W                     the frontier: ('CNT', q) counter phase, ('P', p, q) block being built,
                          ('G', q) carry, ('T', p) tail, ('NONE',) no frontier (timer phase)
    R = [['F', m, k] | ['X', x] | ['Y', q], ...]   blocks right of the frontier (X = a bare (1,x), Y = a carry (2,q), both left by a rebuild)
    END                   the end marker (2,1)

Every pass rule of passes.py becomes an item rule here, and runs of identical passes are done at once, with the
exact step count (sums of affine terms).  `validate` compares the state and the step count with the samples of the
plain machine at every point where both exist; `run` goes on as far as asked.  A situation that no rule covers
raises NoRule (then nothing is claimed beyond that point).

usage: python3 accsim.py validate SAMPLES         SAMPLES from  lt1 MACHINE STEPS  (all left-end arrivals)
       python3 accsim.py window SAMPLES           SAMPLES from  lt2 MACHINE STEPS FROM N  (N arrivals after FROM)
       python3 accsim.py run MAXSTEPS SECONDS [LOG]
"""
import sys
import time

HERE = __file__.rsplit('/', 1)[0]
sys.path.insert(0, HERE)
from passes import merge, sample  # noqa: E402


class NoRule(Exception):
    pass


YK = 48  # fitted on the one sample at step 79,277,382,450


def tri(n):
    return n * (n - 1) // 2


class Sim:
    def __init__(self):
        # the sample at step 440:  c = -1, pairs (2,1)(1,4)(2,1)(1,2)(2,1)(1,1)(2,1)
        self.c = -1
        self.L = [[4, 1], [2, 1], [1, 1]]
        self.F, self.M = 3, 7
        self.W = ('NONE',)
        self.R = []
        self.steps = 440
        self.passes = 0
        self.rebuilds = 0
        self.log = []

    # ---------------------------------------------------------------- helpers
    def addL(self, m, k=1):
        if k <= 0:
            return
        if self.L and self.L[-1][0] == m:
            self.L[-1][1] += k
        else:
            self.L.append([m, k])
        self.F += k
        self.M += m * k

    def popR(self):
        """Remove and return the head item of R as ('F', m) or ('X', x) or ('END',)."""
        if not self.R:
            return ('END',)
        h = self.R[0]
        if h[0] in ('X', 'Y'):
            self.R.pop(0)
            return (h[0], h[1])
        h[2] -= 1
        if h[2] == 0:
            self.R.pop(0)
        return ('F', h[1])

    def headR(self):
        if not self.R:
            return ('END',)
        h = self.R[0]
        return (h[0], h[1]) if h[0] in ('X', 'Y') else ('F', h[1], h[2])

    def pairs(self):
        """The pair list of passes.py for the current state."""
        P = []
        W = self.W
        if W[0] == 'CNT':
            P.append((1, W[1]))
        for m, k in self.L:
            P += [(2, 1), (1, m)] * k
        if W[0] == 'P':
            P += [(2, 1), (1, W[1]), (1, W[2])]
        elif W[0] == 'G':
            P.append((2, W[1]))
        elif W[0] == 'T':
            P += [(2, 1), (1, W[1]), (1, 0)]
        for h in self.R:
            if h[0] == 'X':
                P.append((1, h[1]))
            elif h[0] == 'Y':
                P.append((2, h[1]))
            else:
                P += [(2, 1), (1, h[1])] * h[2]
        if W[0] != 'T':
            P.append((2, 1))
        return merge(P)

    # ---------------------------------------------------------------- one batch
    def batch(self):
        """Apply one rule (a run of identical passes where possible).  Returns the number of passes."""
        c, W = self.c, self.W
        if c == -1:
            return self.rebuild()
        kind = W[0]
        base = 6 * c + 20 * self.F + 6 * self.M
        if kind == 'CNT':
            q = W[1]
            if q >= 1:
                self.steps += 6 * c * q + 9 * q * (q - 1) + 36 * q
                self.c = c + 3 * q
                self.W = ('CNT', 0)
                return q
            h = self.popR()
            if h[0] == 'X':
                # (1,0)(1,x) = (2,x): the carry G(x) starts at once (no pass); seen at step 48,916,125,776
                self.W = ('G', h[1])
                return 0
            if h[0] != 'F':
                raise NoRule(f'counter phase ends on {h}')
            self.steps += 6 * c + 54
            self.c = c - 1
            self.W = ('P', 4, h[1] - 1)
            return 1
        if kind == 'P':
            p, q = W[1], W[2]
            if q >= 1:
                t = min(q, c + 1)
                self.steps += t * (base + 6 * p + 56) + 18 * tri(t)
                self.c = c - t
                self.W = ('P', p + 4 * t, q - t)
                return t
            h = self.headR()
            if h[0] == 'F':
                m, k = h[1], h[2]
                # whole items: each takes 1 d-pass + (m-1) c-passes, all at c >= 0
                kk = min(k, (c + 1) // m)
                if kk >= 1:
                    def item(i):
                        ci = c - i * m
                        Fi = self.F + i
                        Mi = self.M + (0 if i == 0 else p + (i - 1) * 4 * m)
                        pi = p if i == 0 else 4 * m
                        d = 6 * ci + 20 * Fi + 6 * Mi + 6 * pi + 74
                        rest = (m - 1) * (6 * (ci - 1) + 20 * (Fi + 1) + 6 * (Mi + pi) + 80) + 18 * tri(m - 1)
                        return d + rest
                    tot = item(0)
                    if kk >= 2:
                        n = kk - 1
                        a1, a2 = item(1), item(2)
                        tot += n * a1 + (a2 - a1) * tri(n)
                    self.steps += tot
                    self.R[0][2] -= kk
                    if self.R[0][2] == 0:
                        self.R.pop(0)
                    self.addL(p)
                    self.addL(4 * m, kk - 1)
                    self.c = c - kk * m
                    self.W = ('P', 4 * m, 0)
                    return kk * m
                # not enough counter for a whole item: one d-pass
                self.popR()
                self.steps += base + 6 * p + 74
                self.addL(p)
                self.c = c - 1
                self.W = ('P', 4, m - 1)
                return 1
            if h[0] == 'END':
                self.steps += base + 6 * p + 70
                self.addL(p)
                self.addL(2)
                self.c = c - 1
                self.W = ('NONE',)
                return 1
            if h[0] == 'X':
                # (1,p)(1,0)(1,x) = (1,p)(2,x): the block is finished and the carry G(x) starts (no pass)
                self.R.pop(0)
                self.addL(p)
                self.W = ('G', h[1])
                return 0
            raise NoRule(f'P({p},0) meets {h}')
        if kind == 'G':
            q = W[1]
            h = self.headR()
            if h[0] == 'F':
                m, k = h[1], h[2]
                t = min(k, c + 1)

                def cost(i):
                    Fi = self.F + i
                    Mi = self.M + (0 if i == 0 else q + 3 + (i - 1) * (m + 3))
                    qi = q if i == 0 else m
                    return 6 * (c - i) + 20 * Fi + 6 * Mi + 8 * qi + 48
                tot = cost(0)
                if t >= 2:
                    n = t - 1
                    a1, a2 = cost(1), cost(2)
                    tot += n * a1 + (a2 - a1) * tri(n)
                self.steps += tot
                self.R[0][2] -= t
                if self.R[0][2] == 0:
                    self.R.pop(0)
                self.addL(q + 3)
                self.addL(m + 3, t - 1)
                self.c = c - t
                self.W = ('G', m)
                return t
            if h[0] == 'X' and q != 1:
                x = h[1]
                self.R.pop(0)
                FR = sum(e[2] for e in self.R if e[0] == 'F')
                MR = sum(e[1] * e[2] for e in self.R if e[0] == 'F')
                if any(e[0] == 'X' for e in self.R):
                    raise NoRule('f2 with more X items to the right')
                self.steps += 6 * c + 20 * (self.F + 1 + FR) + 6 * (self.M + x + MR) + 68
                self.addL(x + 3)
                for e in self.R:
                    self.addL(e[1], e[2])
                self.R = []
                self.addL(1)
                self.c = c - 1
                self.W = ('NONE',)
                return 1
            if h[0] == 'Y' and h[1] == 1:
                # (2,q)(2,1)(2,1) -> (2,1)(1,q+3)(3,1): the frozen carry is used up and a block q+3 is being built
                # (seen at step 79,277,382,450)
                self.R.pop(0)
                self.steps += base + 8 * q + YK
                self.c = c - 1
                self.W = ('P', q + 3, 0)
                return 1
            if h[0] == 'END' and q == 1:
                self.steps += base + 56
                self.c = c - 1
                self.W = ('T', 4)
                return 1
            raise NoRule(f'G({q}) meets {h}')
        if kind == 'T':
            p = W[1]
            if self.R:
                raise NoRule('T with items to the right')
            self.steps += base + 6 * p + 58
            self.addL(p + 3)
            self.c = c - 1
            self.W = ('NONE',)
            return 1
        if kind == 'NONE':
            t = c + 1
            self.steps += t * (base + 44) + 20 * tri(t)
            self.addL(1, t)
            self.c = -1
            return t
        raise NoRule(f'frontier {W}')

    def rebuild(self):
        """c = -1: the frontier rule as at c = 0 (4 steps fewer), then the first block becomes the counter (70 steps)."""
        self.c = 0
        s0 = self.steps
        W0 = self.W
        n = self.single_at_zero()
        if n != 1:
            raise NoRule('rebuild pass')
        self.steps -= 4
        # second pass: first block -> counter
        if self.W[0] not in ('P', 'NONE', 'G'):
            raise NoRule(f'rebuild with frontier {self.W}')
        newR = []
        for m, k in self.L:
            if newR and newR[-1][0] == 'F' and newR[-1][1] == m:
                newR[-1][2] += k
            else:
                newR.append(['F', m, k])
        if self.W[0] == 'P':
            p, q = self.W[1], self.W[2]
            newR.append(['F', p, 1])
            newR.append(['X', q])
        if self.W[0] == 'G':
            # a carry frozen by the rebuild stays in the list as the pair (2,q) (seen at step 52,926,503,624)
            newR.append(['Y', self.W[1]])
        for e in self.R:
            if e[0] == 'F' and newR and newR[-1][0] == 'F' and newR[-1][1] == e[1]:
                newR[-1][2] += e[2]
            else:
                newR.append(list(e))
        first = newR[0]
        if first[0] != 'F':
            raise NoRule('rebuild: first item not a block')
        m1 = first[1]
        first[2] -= 1
        if first[2] == 0:
            newR.pop(0)
        self.L, self.F, self.M = [], 0, 0
        self.R = newR
        self.W = ('CNT', m1 - 2)
        self.c = 5
        self.steps += 70
        self.rebuilds += 1
        self.log.append((s0, self.steps, m1, W0))
        return 2

    def single_at_zero(self):
        """One pass at c = 0 (used by the rebuild): never a multi-pass batch."""
        W = self.W
        if W[0] == 'NONE':
            self.steps += 20 * self.F + 6 * self.M + 44
            self.addL(1)
            self.c = -1
            return 1
        if W[0] == 'P' and W[2] >= 1:
            p, q = W[1], W[2]
            self.steps += 20 * self.F + 6 * self.M + 6 * p + 56
            self.W = ('P', p + 4, q - 1)
            self.c = -1
            return 1
        if W[0] == 'P' and W[2] == 0 and self.headR()[0] == 'F':
            p = W[1]
            h = self.popR()
            self.steps += 20 * self.F + 6 * self.M + 6 * p + 74
            self.addL(p)
            self.W = ('P', 4, h[1] - 1)
            self.c = -1
            return 1
        if W[0] == 'G' and self.headR()[0] == 'F':
            q = W[1]
            h = self.popR()
            self.steps += 20 * self.F + 6 * self.M + 8 * q + 48
            self.addL(q + 3)
            self.W = ('G', h[1])
            self.c = -1
            return 1
        raise NoRule(f'rebuild pass with frontier {W}')

    def run(self, maxsteps, seconds, every=None):
        t0 = time.time()
        while self.steps < maxsteps and time.time() - t0 < seconds:
            self.passes += self.batch()
            if every:
                every(self)
        return self


def validate(path):
    data = {}
    for line in open(path):
        f = line.split()
        if f[1] == 'A' and int(f[0]) >= 440:
            data[int(f[0])] = sample(f[2:])
    last = max(data)
    s = Sim()
    checked = 0
    while s.steps < last:
        if s.steps in data:
            if data[s.steps] != (s.c, s.pairs()):
                raise SystemExit(f'state differs at step {s.steps}')
            checked += 1
        elif s.c != -1 or True:
            raise SystemExit(f'no sample of the plain machine at step {s.steps} (after {s.passes} passes)')
        s.passes += s.batch()
    print(f'{checked} batch ends from step 440 to {s.steps} agree with the plain machine (state and step); '
          f'{s.passes} passes, {s.rebuilds} rebuilds')


def validate_window(path):
    """Samples of the plain machine from some step on (lt2 MACHINE STEPS FROM N): every batch end of the
    accelerated run inside the sampled window must be one of them, with the same state."""
    data = {}
    for line in open(path):
        f = line.split()
        if len(f) > 1 and f[1] == 'A':
            data[int(f[0])] = sample(f[2:])
    first, last = min(data), max(data)
    s = Sim()
    checked = 0
    while s.steps <= last:
        if s.steps >= first:
            if s.steps not in data:
                raise SystemExit(f'no sample of the plain machine at step {s.steps}')
            if data[s.steps] != (s.c, s.pairs()):
                raise SystemExit(f'state differs at step {s.steps}')
            checked += 1
        s.passes += s.batch()
    print(f'{checked} batch ends in steps {first}..{last} agree with the plain machine (state and step)')


def describe(s, n=12):
    def runs(L):
        return ' '.join(f'{m + 2}' + (f'^{k}' if k > 1 else '') for m, k in L)
    R = ' '.join((f"{e[1] + 2}" + (f"^{e[2]}" if e[2] > 1 else '')) if e[0] == 'F' else f"X{e[1]}" for e in s.R)
    return f'c={s.c} L=[{runs(s.L[:n])}{" ..." if len(s.L) > n else ""}] W={s.W} R=[{R[:200]}]'


if __name__ == '__main__':
    if sys.argv[1] == 'validate':
        validate(sys.argv[2])
    elif sys.argv[1] == 'window':
        validate_window(sys.argv[2])
    elif sys.argv[1] == 'run':
        s = Sim()
        maxs = int(float(sys.argv[2]))
        secs = float(sys.argv[3])
        out = open(sys.argv[4], 'w') if len(sys.argv) > 4 else sys.stdout
        t0 = time.time()
        nrb = 0
        try:
            while s.steps < maxs and time.time() - t0 < secs:
                s.passes += s.batch()
                if s.rebuilds != nrb:
                    nrb = s.rebuilds
                    s0, s1, m1, W0 = s.log[-1]
                    nruns = len(s.R)
                    print(f'rebuild {nrb} at step {s0} (~10^{len(str(s0)) - 1}): first block {m1 + 2}, '
                          f'{nruns} runs, frontier before {W0}', file=out, flush=True)
        except NoRule as e:
            print(f'NoRule at step {s.steps}: {e}', file=out)
            print(describe(s), file=out)
        print(f'stopped at step {s.steps} (~10^{len(str(s.steps)) - 1}) after {s.passes} passes, {s.rebuilds} rebuilds, '
              f'{time.time() - t0:.1f} s', file=out)
        print(describe(s), file=out)
