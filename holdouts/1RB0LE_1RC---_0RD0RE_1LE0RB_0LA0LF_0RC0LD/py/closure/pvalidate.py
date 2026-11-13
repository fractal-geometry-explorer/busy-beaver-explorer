"""Check a certificate of pclosure.py against the plain simulator round.c.
usage: python3 pvalidate.py CERT.json pieces|points [SEED] [PER_CLASS]
  pieces: every piece of every class at x = 0 and at one random x: the plain machine must reach the predicted node
          (the same tape, cell by cell) or halt where the piece says halt.
  points: random members of every class (counts with the class residues): exactly one piece must contain the point
          (this tests that the pieces cover the class), and the plain machine must do what that piece says.
"""
import gzip, json, os, random, re, subprocess, sys
from fractions import Fraction
import pclosure
from pclosure import canon, compress, BIG

def parse_form(s):
    k = 0; c = {}
    for part in s.split('+'):
        if '*x' in part:
            a, v = part.split('*x'); c[int(v)] = int(a)
        else:
            k = int(part)
    return k, c

def ev(form, x):
    k, c = form
    return k + sum(a * x.get(v, 0) for v, a in c.items())

def tape(text, counts):
    it = iter(counts); out = []
    for part in text.split():
        if part.startswith('('):
            out.append(part[1:part.index(')')] * next(it))
        else:
            out.append(part)
    return ''.join(out)

def canon_cells(cells):
    return canon(compress([int(c) for c in cells]))

def solve(forms, point):
    """nonnegative integer x with forms(x) = point, or None.  At most 3 variables; brute force on a pivot variable."""
    vs = sorted({v for k, c in forms for v in c})
    eqs = [(c, p - k) for (k, c), p in zip(forms, point)]
    x = {}
    progress = True
    while progress:
        progress = False
        for c, rhs in eqs:
            unk = [v for v in c if v not in x]
            if len(unk) == 1:
                v = unk[0]
                r = rhs - sum(a * x[u] for u, a in c.items() if u in x)
                if r % c[v] or r < 0:
                    return None
                x[v] = r // c[v]; progress = True
    if any(v not in x for v in vs):
        return 'free'
    for c, rhs in eqs:
        if sum(a * x[v] for v, a in c.items()) != rhs:
            return None
    return x

class Plain:
    def __init__(self, machine, state, pre, word, suf):
        here = os.path.dirname(os.path.abspath(__file__))
        exe = '/tmp/round_' + machine[:20].replace('-', '_')
        if not os.path.exists(exe):
            subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(here, '..', '..', 'c', 'round.c')], check=True)
        self.p = subprocess.Popen([exe, machine, state, pre, word, suf], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    def run(self, cells, maxsteps=2 * 10 ** 9):
        self.p.stdin.write('%d %s\n' % (maxsteps, cells)); self.p.stdin.flush()
        f = self.p.stdout.readline().split()
        if f[0] == 'NODE':
            return ('node', f[2].rstrip('0'))
        return (f[0].lower(),)

def expect(leaf, x):
    if leaf['kind'] == 'halt':
        return ('halt',)
    return ('node', tape(leaf['to'], [ev(parse_form(c), x) for c in leaf['counts']]).rstrip('0'))

def main():
    cert = json.load(gzip.open(sys.argv[1]) if sys.argv[1].endswith('.gz') else open(sys.argv[1])); mode = sys.argv[2]
    random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    per = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    pl = Plain(cert['machine'], 'ABCDEF'[pclosure.accel.EVSTATE], *cert['plain'])
    n = bad = 0
    mod = cert['mod']
    for text, res, leaves in cert['classes']:
        if mode == 'pieces':
            for lf in leaves:
                forms = [parse_form(s) for s in lf['start']]
                vs = sorted({v for k, c in forms for v in c})
                for x in ({v: 0 for v in vs}, {v: random.randint(1, 12) for v in vs}):
                    pt = [ev(f, x) for f in forms]
                    got = pl.run(tape(text, pt)); want = expect(lf, x); n += 1
                    if got != want:
                        bad += 1; print('MISMATCH', text, pt, got, want)
                    if not vs:
                        break
        else:
            k = len(res)
            for _ in range(per if k else 1):
                pt = [BIG + (r - BIG) % mod + mod * random.randint(0, 40) for r in res]
                hits = []
                for lf in leaves:
                    x = solve([parse_form(s) for s in lf['start']], pt)
                    if x is not None:
                        hits.append((lf, x))
                n += 1
                if len(hits) != 1 or hits[0][1] == 'free':
                    bad += 1; print('COVER', text, pt, len(hits)); continue
                got = pl.run(tape(text, pt)); want = expect(*hits[0])
                if got != want:
                    bad += 1; print('MISMATCH', text, pt, got, want)
    print('%s: %d runs of the plain simulator, %d problems' % (mode, n, bad))
    return bad == 0

if __name__ == '__main__':
    sys.exit(0 if main() else 1)
