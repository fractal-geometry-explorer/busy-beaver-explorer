"""Counter-jump accelerator, general form (round 2), for the 1RB1LA_1LC1RD_1LA0LC_1RE0RB family.
At a pass start (A on 0) with top block m = 3 or 5:
  left  = Lrest [0 1^floor (even)] 0 1^(2a_1+1) 0 ... 0 1^(2a_t+1)  (odd blocks, top = a_t next to the head)
  right = (0^(GP d_i + GB) 1)_i  Rrest      N = sum 2^(P_i), P_i = P_(i-1) + d_i + 1  (zeros first, LSB first)
  E = stack value of the a's (top = lowest zero run).
Mode 3: one pass pair (P3 + Peven) maps (E, N) -> (E - 1, N + 1); steps 22 + 4 nu2(E) + 6 nu2(N + 1).
Mode 5: two pass pairs map (E, N) -> (E - 1, N + 2); steps 48 + 4 nu2(E) + 6 nu2(N + 1) + 6 nu2(N + 2).
The floor block grows by 2 each time E passes a power of two.  No carry into Rrest beyond its spare room."""
import subprocess, sys, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
PS = os.path.join(HERE, '..', 'c', 'ps')
GB = int(os.environ.get('GB', '2')); GP = int(os.environ.get('GP', '3'))
K3 = [int(x) for x in os.environ.get('K3', '22,4,6').split(',')]
K5 = [int(x) for x in os.environ.get('K5', '48,4,6').split(',')]
pop = lambda x: bin(x).count('1')
def snu(a, b):   # sum of nu2(x) for a <= x <= b
    f = lambda n: n - pop(n) if n > 0 else 0
    return f(b) - f(a - 1)

def toks(s):
    out = []; head = None
    for t in s.split():
        if '>' in t: head = len(out); out.append(['H', t]); continue
        m = re.match(r'^([01])(\^(\d+))?$', t); out.append([int(m.group(1)), int(m.group(3) or 1)])
    return out, head

def norm(tt):
    T, h = tt; T = [list(x) for x in T]
    while T and T[0][0] == 0: T.pop(0); h -= 1
    while T and T[-1][0] == 0: T.pop()
    return T, h

def parse(tape):
    T, h = toks(tape)
    L = T[:h]; R = T[h+1:]
    assert T[h][1] == 'A>0'
    m = R[0][1]; assert R[0][0] == 1 and m in (3, 5)
    i = 1; Q = []
    while i + 1 < len(R) and R[i][0] == 0 and R[i][1] >= GB and (R[i][1] - GB) % GP == 0 and R[i+1] == [1, 1]:
        Q.append((R[i][1] - GB) // GP); i += 2
    Rrest = R[i:]
    j = len(L) - 1; S = []
    while j >= 0 and L[j][0] == 1 and L[j][1] % 2 == 1:
        S.append((L[j][1] - 1) // 2)
        if j >= 2 and L[j-1] == [0, 1] and L[j-2][0] == 1 and L[j-2][1] % 2 == 1: j -= 2; continue
        break
    floor = None
    if j >= 2 and L[j-1] == [0, 1] and L[j-2][0] == 1 and L[j-2][1] % 2 == 0:
        floor = L[j-2][1]; Lrest = L[:j-2]
    else:
        Lrest = L[:j]
    E = 0; P = -1
    for a in S: P += a + 1; E += 1 << P
    N = 0; P = -1
    for q in Q: P += q + 1; N += 1 << P
    return dict(m=m, E=E, N=N, Nb=P + 1, floor=floor, Lrest=Lrest, Rrest=Rrest)

def zr(x):
    out = []; prev = -1
    for b in range(x.bit_length()):
        if x >> b & 1: out.append(b - prev - 1); prev = b
    return out

def fmt(seq):
    res = []
    for x in seq:
        x = tuple(x)
        if x[0] != 'H' and x[1] == 0: continue
        if x[0] != 'H' and res and res[-1][0] == x[0]: res[-1] = (x[0], res[-1][1] + x[1])
        else: res.append(x)
    return ' '.join(x[1] if x[0] == 'H' else (str(x[0]) if x[1] == 1 else '%d^%d' % x) for x in res)

def build(P, E, N, floor, Rrest):
    seq = [tuple(x) for x in P['Lrest']]
    if floor is not None: seq.append((1, floor))
    first = floor is not None or bool(seq and seq[-1][0] == 1)
    for a in reversed(zr(E)):
        if first: seq.append((0, 1))
        seq.append((1, 2 * a + 1)); first = True
    seq.append(('H', 'A>0')); seq.append((1, P['m']))
    for q in zr(N): seq.append((0, GP * q + GB)); seq.append((1, 1))
    seq += [tuple(x) for x in Rrest]
    return fmt(seq)

def jump(P):
    E, N = P['E'], P['N']
    if E < 2: return None
    kE = E - 1 if P['floor'] is not None else E - (1 << (E.bit_length() - 1))
    Rr = P['Rrest']
    if not Rr: umax = None
    elif Rr[0][0] == 0: umax = max(0, (Rr[0][1] - GP) // GP)
    else: umax = 0
    per = 1 if P['m'] == 3 else 2
    k = kE
    if umax is not None: k = min(k, ((1 << (P['Nb'] + umax)) - 1 - N) // per)
    if k <= 0: return None
    if per == 1: dt = K3[0] * k + K3[1] * snu(E - k + 1, E) + K3[2] * snu(N + 1, N + k)
    else: dt = K5[0] * k + K5[1] * snu(E - k + 1, E) + K5[2] * (snu(N + 1, N + 2 * k) - 0) + K5[2] * 0
    if per == 2:
        # 6 nu2(N+1) + 6 nu2(N+2) per cycle: the sum over N+1 .. N+2k of nu2
        dt = K5[0] * k + K5[1] * snu(E - k + 1, E) + K5[2] * snu(N + 1, N + 2 * k)
    fl = P['floor']
    if fl is not None: fl += 2 * (E.bit_length() - (E - k).bit_length())
    N2 = N + per * k
    u = N2.bit_length() - P['Nb']
    Rrest = [list(x) for x in Rr]
    if u > 0 and Rr: Rrest[0][1] -= GP * u
    return k, dt, build(P, E - k, N2, fl, Rrest)

MONS = [0, 0, 0, 0, 0, -1]
def run_ps(M, tape, maxsteps, T):
    r = subprocess.run([PS, M, str(maxsteps), str(T)], input=tape, capture_output=True, text=True).stdout.split('\n')
    for l in r[2:]:
        if l.startswith('mon'):
            x = [int(y) for y in l.split()[1:]]
            MONS[0] += x[0]; MONS[1] = max(MONS[1], x[1]); MONS[2] = max(MONS[2], x[2]); MONS[3] = max(MONS[3], x[3])
            MONS[4] += x[4]
            if x[4] and MONS[5] < 0: MONS[5] = 1
    return r[0].split(), (r[1].strip() if len(r) > 1 else '')

VAL = int(os.environ.get('VAL', '0')); nval = [0]
def main(M, rounds, T=12, chunk=2 * 10**9, logf=None, verbose=True, tape='A>0', t=0, tmax=None):
    nlim = 0
    for rnd in range(rounds):
        if tmax is not None and t >= tmax: break
        hd, tp = run_ps(M, tape, chunk, T)
        if hd[0] == 'halt':
            print('HALT at', t + int(hd[1]), flush=True); return ('halt', t + int(hd[1]), tape)
        t += int(hd[1]); tape = tp
        if hd[0] == 'limit':
            nlim += 1
            if verbose: print('limit', t, len(tape), flush=True)
            if nlim > 20: return ('stuck', t, tape)
            continue
        nlim = 0
        P = parse(tape)
        if logf: logf.write('det %d %s\n' % (t, tape)); logf.flush()
        res = jump(P)
        if res is None: print('nojump?', t); return ('nojump', t, tape)
        k, dt, tape2 = res
        if VAL and dt <= VAL:
            hd2, tp2 = run_ps(M, tape, dt, 10**9)
            if hd2[0] != 'limit' or norm(toks(tp2)) != norm(toks(tape2)):
                print('VALIDATION FAILED at', t); print(tape); print(tp2); print(tape2); sys.exit(1)
            nval[0] += 1
        tape = tape2; t += dt
        if verbose:
            if verbose and rnd % 20 == 0: print('mon', MONS[:5], flush=True)
            print('jump t=%d (10^%d) m=%d Ebits=%d k~2^%d Nbits=%d floor=%s Lrest=%d Rrest=%s' % (
                t, len(str(t)) - 1, P['m'], P['E'].bit_length(), k.bit_length(), (P['N'] + k).bit_length(), P['floor'],
                len(P['Lrest']), P['Rrest'][:6]), flush=True)
    print('validated jumps:', nval[0]); print('monitor: passes %d maxdefects %d max2blocks %d maxevenleft %d fatal-precursor %d' % tuple(MONS[:5]))
    return ('rounds', t, tape)

if __name__ == '__main__':
    M = sys.argv[1]; rounds = int(sys.argv[2]); T = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    with open(sys.argv[4] if len(sys.argv) > 4 else '/dev/null', 'w') as lf:
        r = main(M, rounds, T, logf=lf)
        open(sys.argv[4] + '.last', 'w').write('%s %d\n%s\n' % (r[0], r[1], r[2]))
