"""What the class certificates of pclosure.py say about halting, and how the run from blank tape relates to it.

usage (from the repo root; D = holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure):
  python3 D/hline.py summary CERT.json.gz   classes, pieces, the halting pieces and every piece that leads into a
                                            class with a halting piece
  python3 D/hline.py plain                  plain step-by-step runs: the halting shape H, the two lines of shapes A
                                            and B that lead to it, and their neighbours
  python3 D/hline.py run SECONDS CERT.json.gz
                                            the accelerated run from blank tape: is every node in a class of the
                                            certificate, and how close do the visits of A and B come to the lines
"""
import collections
import gzip
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
M = '1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD'
H = '00001 (1000)^n 101000011011101'
A = '00001 (1000)^n 10100001101000 (0001)^n 01000000101'
B = '00001 (1000)^n 101000010000001011 (1000)^n 101000000101'


def load(path):
    return json.load(gzip.open(path) if path.endswith('.gz') else open(path))


def summary(path):
    c = load(path)
    cl = {(t, tuple(r)): v for t, r, v in c['classes']}
    kinds = collections.Counter(lf['kind'] for v in cl.values() for lf in v)
    print('%d classes (counts mod %d, big >= %d), %d pieces: %s; queue %d' % (
        len(cl), c['mod'], c['big'], sum(map(len, cl.values())), dict(kinds), len(c['todo'])))
    halting = {k for k, v in cl.items() if any(lf['kind'] == 'halt' for lf in v)}
    for k in sorted(halting):
        print('halting class', k)
        for lf in cl[k]:
            print('   counts %s: %s' % (lf['start'], lf['kind']))
    texts = {k[0] for k in halting}
    print('pieces that lead to a halting shape:')
    for k, v in sorted(cl.items()):
        for lf in v:
            if lf['kind'] == 'node' and lf['to'] in texts:
                print('  ', k, 'counts', lf['start'], '->', lf['counts'])


def run_plain(tape, maxsteps):
    T = {}
    for i, s in enumerate(M.split('_')):
        for b in (0, 1):
            t = s[3 * b:3 * b + 3]
            T[(i, b)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    tp = {i: int(ch) for i, ch in enumerate(tape)}
    h, q, n = 0, 5, 0
    while n < maxsteps:
        t = T[(q, tp.get(h, 0))]
        if t is None:
            return 'halts after %d steps' % n
        tp[h] = t[0]
        h += t[1]
        q = t[2]
        n += 1
    return 'no halt in %d steps' % n


def plain():
    for P in (21, 23, 25, 31, 51, 101):
        print('H  P=%d: %s' % (P, run_plain('00001' + '1000' * P + '101000011011101', 10 ** 8)))
    for P in (22, 24, 50):
        print('H  P=%d (even): %s' % (P, run_plain('00001' + '1000' * P + '101000011011101', 3 * 10 ** 6)))
    for name, mid, w, end, off, Ps in (('A', '10100001101000', '0001', '01000000101', 16, (27, 29, 41, 101)),
                                       ('B', '101000010000001011', '1000', '101000000101', 24, (29, 31, 45))):
        for P in Ps:
            for dq in (0, -2, 2):
                Q = 3 * P - off + dq
                print('%s  P=%d Q=3P-%d%s: %s' % (name, P, off, '%+d' % dq if dq else '', run_plain(
                    '00001' + '1000' * P + mid + w * Q + end, 10 ** 8 if dq == 0 else 3 * 10 ** 6)))


def run(seconds, path):
    import pclosure
    c = load(path)
    keys = {(t, tuple(r)) for t, r, v in c['classes']}
    mod = c['mod']
    res = pclosure.real_nodes(seconds)
    first = next(i for i, x in enumerate(res) if x[2])
    out = [x for x in res[first:] if (x[1], tuple(n % mod for n in x[2])) not in keys]
    print('%d nodes, the last at a step count of %d digits; from the first node with a big count on, %d of %d are '
          'not in a class of the certificate' % (len(res), len(str(res[-1][0])), len(out), len(res) - first))
    print('visits of the halting shape H: %d' % sum(1 for x in res if x[1] == H))
    for name, sh, off in (('A', A, 16), ('B', B, 24)):
        v = [tuple(cs) for st, t, cs in res if t == sh]
        ds = [q - 3 * p + off for p, q in v]
        print('%s: %d visits; smallest |Q - 3P + %d| = %s; P mod 8 %s; Q mod 8 %s' % (
            name, len(v), off, min(map(abs, ds)) if ds else None,
            sorted(collections.Counter(p % 8 for p, q in v).items()),
            sorted(collections.Counter(q % 8 for p, q in v).items())))


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'summary':
        summary(sys.argv[2])
    elif cmd == 'plain':
        plain()
    elif cmd == 'run':
        run(float(sys.argv[2]), sys.argv[3])
    else:
        print(__doc__)
