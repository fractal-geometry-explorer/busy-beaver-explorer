"""Long exact run of the region-memo accelerator (tools/py/bbtools/regaccel.py), with a per-decade log of the block
list at the right end, and checkpoints (countdown hunt, 21 November 2026).

Every time the accelerated run is at the top level with the head at the right end facing blank tape, and the step
count has DIGITS >= last logged + EVERY decimal digits, the tape left of the head is decoded into runs of 1s
separated by single 0s: a run of K-1 ones is one copy of the block word w (= 1^(K-1) 0, e.g. 111110 for K = 6), and a
long repeated K-cell symbol with one 0 counts as that many copies.  The line shows the list as
`w<count>` (or `we<exponent>` for counts above 10^9) and the other run lengths (7, 8, ... ones: separators, end).

    python3 ratrack.py run MACHINE K SECONDS [mirror] [ckpt=FILE] [every=N] [hb=SECONDS]   # resumes from FILE
                                                     # if it exists; hb: also log every SECONDS
    python3 ratrack.py test MACHINE K [STEPS]   # the decoded snapshots against a direct C run (tools/c/snap.c)
    python3 ratrack.py twin M1 M2 [STEPS]       # build the lockstep product of two twins and check it directly

The run is exact (regaccel is exact, step counts included); a halt is reported with the exact step count.
"""
import os
import pickle
import subprocess
import sys
import tempfile
import threading
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'tools', 'py', 'bbtools'))
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
import regaccel as RA  # noqa: E402


def nd(x):
    return RA.ndigits(x)


def fmt(x):
    return 'e%d' % (nd(x) - 1) if x > 10 ** 9 else str(x)


def runs_of(L, k):
    """the 1-run lengths of the cells of L (list of [symbol, count]); long w-like repeats as ('W', count - 2)"""
    out = []
    cur = 0
    for sym, c in L:
        w = format(sym, '0%db' % k)
        reps = [w] * c if (c <= 3 or w.count('0') != 1) else None
        seq = reps if reps is not None else [w, None, w]
        for x in seq:
            if x is None:
                out.append(('W', c - 2))
                continue
            for ch in x:
                if ch == '1':
                    cur += 1
                else:
                    out.append(cur)
                    cur = 0
    out.append(cur)
    return out


def decode(L, k):
    res = []
    acc = 0
    for r in runs_of(L, k):
        if isinstance(r, tuple):
            acc += r[1]
        elif r == k - 1:
            acc += 1
        else:
            if acc:
                res.append('w%s' % fmt(acc))
                acc = 0
            res.append(str(r))
    if acc:
        res.append('w%s' % fmt(acc))
    return ' '.join(res)


def decode_cells(cells, k):
    """the same decoding for an explicit cell string (used by `test`)"""
    res = []
    acc = 0
    for part in cells.split('0'):
        r = len(part)
        if r == k - 1:
            acc += 1
        else:
            if acc:
                res.append('w%s' % fmt(acc))
                acc = 0
            res.append(str(r))
    if acc:
        res.append('w%s' % fmt(acc))
    return ' '.join(res)


def run(m, k, sec, mir, ck, every, hb=0):
    mm = RA.mirror(m) if mir else m

    def go():
        if ck and os.path.exists(ck):
            s, mark = pickle.load(open(ck, 'rb'))
            for key, v in list(s.memo.items()):      # the FAIL sentinel does not survive pickling
                if type(v) is object:
                    s.memo[key] = RA.FAIL
            print('resumed at digits', nd(s.steps), flush=True)
        else:
            s = RA.Sim(mm, k)
            mark = 0
        t0 = tl = th0 = time.time()
        s.deadline = t0 + sec
        sys.setrecursionlimit(1000000)
        try:
            while time.time() < s.deadline:
                if len(s.R) == 1 and s.d == 1:
                    s.q, s.d = s.basic(s.L, s.R, 1, s.q, s.d, None)
                    d = nd(s.steps)
                    if d >= mark + every or (hb and time.time() - th0 > hb):
                        mark = max(mark, d)
                        th0 = time.time()
                        dec = decode(s.L[1:], k)
                        print('D', d, '%.0fs' % (time.time() - t0), 'nL', len(s.L), 'lead', str(s.steps)[:8] if d < 40000 else '-',
                              dec if len(dec) < 1500 else dec[:300] + ' ... ' + dec[-700:], flush=True)
                        if ck and time.time() - tl > 600:
                            pickle.dump((s, mark), open(ck + '.tmp', 'wb'))
                            os.replace(ck + '.tmp', ck)
                            tl = time.time()
                    continue
                s.q = s.E(s.L, s.R, 1, s.q, s.d, None)
                s.d = 1
        except (RA.Halt, RA.NonHalt, RA.Budget) as e:
            print('EXC', type(e).__name__, s.halted, s.nonhalt, flush=True)
        st = int(s.steps)
        d = nd(st)
        lead = str(st // 10 ** max(0, d - 12))[:6]
        print('RESULT', m, 'K', k, 'mirror' if mir else 'fwd', 'digits', d, 'lead', lead, 'halted', s.halted,
              'nonhalt', s.nonhalt, 'basic', s.nbasic, 'entries', s.nbuilt, 'apps', s.napply, flush=True)
        if s.halted:
            print('HALTSTEPS', st, flush=True)
        if ck:
            pickle.dump((s, mark), open(ck + '.tmp', 'wb'))
            os.replace(ck + '.tmp', ck)
    threading.stack_size(1024 * 1024 * 1024)
    th = threading.Thread(target=go)
    th.start()
    th.join()


def test(m, k, N):
    """every top-level snapshot (head at the right end, blank on the right) up to N steps: the regaccel tape, its
    decoding, against the direct run of tools/c/snap.c and the decoding of its cells"""
    exe = os.path.join(tempfile.gettempdir(), 'bb_snap_ratrack')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(ROOT, 'tools', 'c', 'snap.c')], check=True)
    rec = []
    out = {}

    def go():
        s = RA.Sim(m, k)
        sys.setrecursionlimit(1000000)
        while s.steps < N and not s.halted:
            if len(s.R) == 1 and s.d == 1:
                if 0 < s.steps and (not rec or rec[-1][0] != s.steps):
                    cells = ''.join(format(x, '0%db' % k) * c for x, c in s.L[1:]).lstrip('0')
                    rec.append((s.steps, 'ABCDEFGH'[s.q], cells, decode(s.L[1:], k)))
                s.q, s.d = s.basic(s.L, s.R, 1, s.q, s.d, None)
                continue
            s.q = s.E(s.L, s.R, 1, s.q, s.d, None)
            s.d = 1
        out['s'] = s
    threading.stack_size(512 * 1024 * 1024)
    th = threading.Thread(target=go)
    th.start()
    th.join()
    rec = rec[:20000]
    res = subprocess.run([exe, m], input=''.join('%d\n' % r[0] for r in rec), capture_output=True,
                         text=True).stdout.split('\n')
    bad = 0
    for r, line in zip(rec, res):
        p = line.split(' ')
        ok = (len(p) == 4 and int(p[0]) == r[0] and p[1] == r[1] and p[2] == r[2] and p[3] == '1'
              and decode_cells(p[2], k).lstrip('0 ') == r[3].lstrip('0 '))
        bad += not ok
    print('test %s K=%d: %d snapshots up to %d steps, %d differ (cells, state, decoded list)' % (
        m, k, len(rec), N, bad))
    return 1 if bad else 0


def parse(m):
    T = {}
    for q, row in enumerate(m.split('_')):
        for b in range(2):
            t = row[3 * b:3 * b + 3]
            T[(q, b)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


def product(m1, m2):
    """the lockstep product: states are the pairs reachable from (A, A), in sorted order; a pair whose two rows
    differ on a symbol (in what they write, the move, or one halting) halts there.  Returns (table, pair list)."""
    T1, T2 = parse(m1), parse(m2)
    pairs = [(0, 0)]
    i = 0
    while i < len(pairs):
        a, b = pairs[i]
        for s in range(2):
            t1, t2 = T1[(a, s)], T2[(b, s)]
            if t1 is not None and t2 is not None and t1[:2] == t2[:2] and (t1[2], t2[2]) not in pairs:
                pairs.append((t1[2], t2[2]))
        i += 1
    pairs.sort()
    rows = []
    for a, b in pairs:
        row = ''
        for s in range(2):
            t1, t2 = T1[(a, s)], T2[(b, s)]
            if t1 is None or t2 is None or t1[:2] != t2[:2]:
                row += '---'
            else:
                row += '%d%s%s' % (t1[0], 'R' if t1[1] == 1 else 'L', chr(65 + pairs.index((t1[2], t2[2]))))
        rows.append(row)
    return '_'.join(rows), pairs


def twin(m1, m2, N):
    P, pairs = product(m1, m2)
    print('product', P, 'states', ' '.join('ABCDEF'[a] + 'ABCDEF'[b] for a, b in pairs))
    T1, T2, TP = parse(m1), parse(m2), parse(P)
    t1, t2, tp = {}, {}, {}
    p1 = p2 = pp = 0
    q1 = q2 = qp = 0
    for n in range(N):
        s1, s2, sp = t1.get(p1, 0), t2.get(p2, 0), tp.get(pp, 0)
        assert s1 == s2 == sp and p1 == p2 == pp and pairs[qp] == (q1, q2), n
        a, b, c = T1[(q1, s1)], T2[(q2, s2)], TP[(qp, sp)]
        if c is None:
            print('product halts at step', n + 1, 'pair', pairs[qp], 'reading', sp)
            return
        t1[p1], p1, q1 = a[0], p1 + a[1], a[2]
        t2[p2], p2, q2 = b[0], p2 + b[1], b[2]
        tp[pp], pp, qp = c[0], pp + c[1], c[2]
    print('the two machines and their product agree (tape, head, paired states) for %d steps' % N)


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'run':
        m, k, sec = sys.argv[2], int(sys.argv[3]), float(sys.argv[4])
        ck, every, hb = None, 1, 0
        for a in sys.argv[5:]:
            if a.startswith('ckpt='):
                ck = a[5:]
            if a.startswith('every='):
                every = int(a[6:])
            if a.startswith('hb='):
                hb = float(a[3:])
        run(m, k, sec, 'mirror' in sys.argv[5:], ck, every, hb)
    elif cmd == 'test':
        sys.exit(test(sys.argv[2], int(sys.argv[3]), int(float(sys.argv[4])) if len(sys.argv) > 4 else 10 ** 8))
    elif cmd == 'twin':
        twin(sys.argv[2], sys.argv[3], int(float(sys.argv[4])) if len(sys.argv) > 4 else 10 ** 6)
