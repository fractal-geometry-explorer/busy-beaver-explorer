"""Accelerated simulator (validated) for the 1RB1LA_1LC1RD_1LA0LC_1RE0RB family: two binary counters (E counts down in the
blocks left of the head, F counts up in the gaps right of it).  c/acc runs the machine directly and reports K
consecutive configurations of one even-config pattern; Python checks E-1/F+1 between them, fits the step count
dt = a + b*nu2(E) + g*nu2(F+1) exactly, jumps N cycles in closed form, rebuilds the tape and continues.
Before every jump the first min(N, 2^15) cycles are simulated directly by c/acc and the tape must equal the predicted
one token for token; otherwise the pattern is excluded and the run goes on directly.

Build:  gcc -O2 -o holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/c/acc holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/c/acc.c
Run:    python3 accel.py MACHINE ROUNDS          (1a, 1b: defaults; 1c, 1d: GB=4 GP=5 XEFF=0 in the environment)
Prints one line per jump: ('jump', step, pattern, bits of E, bits of N, bits of F, |S|, |Q|)."""
import subprocess, sys, re
from absm import stack_value, value_stack
import os
ACC = os.environ.get('ACC', os.path.join(os.path.dirname(os.path.abspath(__file__)), '../c/acc'))
GB = int(os.environ.get('GB', '2')); GP = int(os.environ.get('GP', '3')); XEFF = os.environ.get('XEFF', '1') == '1'
pop = lambda x: bin(x).count('1')
def nu2(x): return (x & -x).bit_length() - 1
def s_nu2(a, b):
    if b < a: return 0
    f = lambda n: n - pop(n)
    return f(b) - f(a - 1)

def toks(s):
    out = []; head = None
    for t in s.split():
        if '>' in t: head = len(out); out.append(('H', t)); continue
        m = re.match(r'^([01])(\^(\d+))?$', t); out.append((int(m.group(1)), int(m.group(3) or 1)))
    # strip blank ends
    while out and out[0][0] == 0: out.pop(0); head -= 1
    while out and out[-1][0] == 0: out.pop()
    return out, head

def merge(seq):
    out = []
    for x in seq:
        if x[0] != 'H' and out and out[-1][0] == x[0]: out[-1] = (x[0], out[-1][1] + x[1])
        elif x[0] == 'H' or x[1] > 0: out.append(x)
    return out

def parse_key(key):
    a = [int(x) for x in key.split('.')]
    return a[0], a[1], a[2], a[3], a[4:]

def parse_even(tape, key):
    o, p, c, m, W = parse_key(key)
    T, h = toks(tape)
    L = T[:h]; R = T[h+1:]
    assert R[0] == (1, m)
    i = 1
    for w in W:
        assert R[i] == (0, w) and R[i+1] == (1, 1); i += 2
    for _ in range(c+1):
        assert R[i] == (0, GB) and R[i+1] == (1, 1); i += 2
    Q = []
    while i+1 < len(R) and R[i][0] == 0 and R[i][1] % GP == GB % GP and R[i+1] == (1, 1):
        Q.append((R[i][1]-GB)//GP); i += 2
    Rrest = R[i:]
    xeff = 0
    if XEFF and len(Rrest) >= 2 and Rrest[0][0] == 0 and Rrest[1][0] == 1:
        g, sep = Rrest[0][1], Rrest[1][1]
        if sep == 1:
            if g % 3 == 0: xeff = (g - 3)//3
            elif g % 3 == 1: xeff = (g - 4)//3
        else:
            xeff = (g - 2)//3 - 1
        xeff = max(0, xeff)
    S = []; j = len(L) - 1
    while j >= 0 and L[j][0] == 1 and L[j][1] % 2 == 1:
        S.append((L[j][1]-1)//2); j -= 1
        if j >= 1 and L[j] == (0, 1) and L[j-1][0] == 1 and L[j-1][1] % 2 == 1: j -= 1; continue
        break
    Lrest = L[:j+1]
    S = S[::-1]; S[-1] -= o
    if S[-1] < 0: return None
    lblock = len(Lrest) >= 2 and Lrest[-1] == (0, 1) and Lrest[-2][0] == 1
    return dict(Lrest=Lrest, S=S, Q=Q, Rrest=Rrest, lblock=lblock, key=key, xeff=xeff,
                E=stack_value(S), F=stack_value(list(reversed(Q))))

def build(P, E, F):
    o, p, c, m, W = parse_key(P['key'])
    Lrest = P['Lrest']
    S = value_stack(E); S[-1] += o
    Q = list(reversed(value_stack(F))) if F else []
    body = []
    for a in S: body += [(0, 1), (1, 2*a+1)]
    if not Lrest or Lrest[-1] == (0, 1): body = body[1:]
    seq = list(Lrest) + body + [('H', 'A>0'), (1, m)]
    for w in W: seq += [(0, w), (1, 1)]
    for _ in range(c+1): seq += [(0, GB), (1, 1)]
    for q in Q: seq += [(0, GP*q+GB), (1, 1)]
    seq += P['Rrest']
    out = []
    for x in merge(seq):
        out.append(x[1] if x[0] == 'H' else (str(x[0]) if x[1] == 1 else '%d^%d' % x))
    return ' '.join(out)

def run_c(M, tape, maxsteps, skip, K, excl):
    r = subprocess.run([ACC, M, str(maxsteps), str(skip), str(K), ',' + ','.join(excl) + ','], input=tape,
                       capture_output=True, text=True).stdout.splitlines()
    if 'reset' in r:
        r = r[len(r) - 1 - r[::-1].index('reset') + 1:]
    return r

def fit(samples):
    import itertools
    from fractions import Fraction as Fr
    rows = sorted(set(samples))
    for r1, r2, r3 in itertools.combinations(rows, 3):
        A = [[1, r[1], r[2]] for r in (r1, r2, r3)]; y = [r[0] for r in (r1, r2, r3)]
        def det3(X): return (X[0][0]*(X[1][1]*X[2][2]-X[1][2]*X[2][1]) - X[0][1]*(X[1][0]*X[2][2]-X[1][2]*X[2][0])
                             + X[0][2]*(X[1][0]*X[2][1]-X[1][1]*X[2][0]))
        d = det3(A)
        if d == 0: continue
        sol = []
        for col in range(3):
            X = [row[:] for row in A]
            for i in range(3): X[i][col] = y[i]
            sol.append(Fr(det3(X), d))
        a, b, g = sol
        if all(a + b*v + g*j == dt for dt, v, j in samples): return (a, b, g)
        return None
    return 'under'

class Run:
    def __init__(self, M, K=12, cmax=10**9):
        self.M = M; self.K = K; self.cmax = cmax; self.formulas = {}; self.log = []; self.events = []; self.ntest = 1 << 15; self.nval = 0
    def go(self, tape, t=0, rounds=10**6, verbose=False, tmax=None):
        skip = 0; excl = []
        for rnd in range(rounds):
            if tmax is not None and t >= tmax: return ('stop', t, tape)
            lines = run_c(self.M, tape, self.cmax, skip, self.K, excl)
            if lines[0].startswith('halt'):
                k = int(lines[0].split()[1]); self.log.append(('halt', t + k)); return ('halt', t + k, tape)
            if lines[0].startswith('limit'):
                self.log.append(('limit', t + self.cmax)); return ('limit', t + self.cmax, lines[1])
            dets = [(int(a.split()[1]), a.split()[2], b) for a, b in zip(lines[0::2], lines[1::2]) if a.startswith('det')]
            key = dets[0][1]
            if len(dets) < self.K:
                # ran out (halt/limit mid-collection is reported after)
                rest = [l for l in lines if not l.startswith('det') and not l.startswith(' ')]
                return ('short', t, tape)
            Ps = [parse_even(d[2], key) for d in dets]
            good = all(P is not None for P in Ps)
            if good:
                D = Ps[0]['E'] - Ps[1]['E']
                good = D >= 1 and D & (D-1) == 0 and all(Ps[i+1]['E'] == Ps[i]['E'] - D and Ps[i+1]['F'] == Ps[i]['F'] + 1 for i in range(self.K-1))
            if not good:
                excl.append(key); continue          # rerun from the same tape without this key
            sh = D.bit_length() - 1; low = Ps[0]['E'] & (D - 1)
            samples = [(dets[i+1][0] - dets[i][0], nu2(Ps[i]['E'] >> sh), nu2(Ps[i]['F'] + 1)) for i in range(self.K-1)]
            fkey = key + '/%d' % sh
            f = fit(samples)
            if isinstance(f, tuple):
                if fkey in self.formulas and self.formulas[fkey] != f: raise RuntimeError('formula changed')
                self.formulas[fkey] = f
            elif fkey in self.formulas:
                a_, b_, g_ = self.formulas[fkey]
                if not all(a_ + b_*v + g_*j == dt for dt, v, j in samples): raise RuntimeError('formula mismatch')
                f = self.formulas[fkey]
            kL, _, tpL = dets[-1]; P = Ps[-1]
            if not isinstance(f, tuple):
                tape = tpL.strip(); t += kL; skip = 1000; self.log.append(('nofit', t, key)); continue
            EF, F = P['E'], P['F']; E = EF >> sh
            sc = lambda x: (x << sh) | low
            N = E - 1 if P['lblock'] else E - (1 << (E.bit_length() - 1))
            if P['Rrest']:
                N = min(N, (1 << (F.bit_length() + P['xeff'])) - 1 - F)
            if N < 2:
                tape = tpL.strip(); t += kL; skip = 1000; self.log.append(('small', t, key)); continue
            a_, b_, g_ = f
            # validation: n test cycles by direct simulation must give exactly the predicted tape
            n = min(N, self.ntest)
            dtn = a_*n + b_*s_nu2(E - n + 1, E) + g_*s_nu2(F + 1, F + n)
            Pn = dict(P)
            if Pn['lblock']:
                Lr = list(Pn['Lrest']); Lr[-2] = (1, Lr[-2][1] + 2*(E.bit_length() - (E-n).bit_length())); Pn['Lrest'] = Lr
            if Pn['Rrest']:
                u = (F+n).bit_length() - F.bit_length()
                if u: RR = list(Pn['Rrest']); RR[0] = (0, RR[0][1] - GP*u); Pn['Rrest'] = RR
            pred = toks(build(Pn, sc(E - n), F + n))
            out = run_c(self.M, tpL.strip(), int(dtn), 4*10**18, 1, [])
            got = toks(out[1])
            self.nval += 1
            if out[0].split()[0] != 'limit' or got != pred:
                self.log.append(('valfail', t, key)); excl.append(key)
                tape = tpL.strip(); t += kL; skip = 0; continue
            dt = a_*N + b_*s_nu2(E - N + 1, E) + g_*s_nu2(F + 1, F + N)
            assert dt.denominator == 1
            E2, F2 = E - N, F + N
            P = dict(P)
            if P['lblock']:
                inc = E.bit_length() - E2.bit_length()
                Lr = list(P['Lrest']); Lr[-2] = (1, Lr[-2][1] + 2*inc); P['Lrest'] = Lr
            if P['Rrest']:
                u = F2.bit_length() - F.bit_length()
                assert 0 <= u <= P['xeff']
                if u:
                    RR = list(P['Rrest']); RR[0] = (0, RR[0][1] - GP*u); P['Rrest'] = RR
            tape = build(P, sc(E2), F2)
            t += kL + int(dt)
            rec = ('jump', t, key, E.bit_length(), N.bit_length(), F2.bit_length(), len(P['S']), len(P['Q']))
            self.log.append(rec)
            if verbose: print(rec, flush=True)
            skip = 0; excl = []
        return ('rounds', t, tape)

if __name__ == '__main__':
    M = sys.argv[1]
    R = Run(M)
    res = R.go('A>0', rounds=int(sys.argv[2]), verbose=True)
    print(res[:2])
