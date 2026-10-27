"""Check the extra-wall pass maps P and Q (and words of them) on the proved model.

For each word, `mixsolve.coset` (the Python forced run, untrusted) gives the coset of starts (w1, w2, w3, w4, E) that
follow it.  Points of the coset near a scaled real geometry are run through `Harness.lean` (the zipper model
`roundZ`, the function of the Lean round theorem `round_run`), and the shapes of every round and the positions after
each pass are compared with the affine pass maps below.  usage: python3 verify_maps.py [K] [points per word]"""
import sys, os, random, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'conc'))
from fractions import Fraction as F
import mixsolve as MS
from lattice import babai
from passmaps import MAPS, apply

HERE = os.path.dirname(os.path.abspath(__file__))
def lean_runs(states, nrounds):
    env = dict(os.environ); env['LEAN_PATH'] = env['LEANLIB'] + ':' + os.path.join(HERE, '..', 'lean', 'out')
    inp = ''.join(f"{nrounds} {x[4]} " + ' '.join(f"W {v}" for v in x[:4]) + '\n' for x in states)
    out = subprocess.run([env.get('LEAN', 'lean'), '--run', os.path.join(HERE, 'Harness.lean')], input=inp,
                         capture_output=True, text=True, env=env).stdout
    runs, cur = [], []
    for l in out.splitlines():
        if l == 'end': runs.append(cur); cur = []
        elif l.startswith('G') or l in ('halt', 'uncovered', 'notwf', 'parse'): cur.append(l)
    return runs

def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    npts = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    words = sys.argv[3].split(',') if len(sys.argv) > 3 else ['P', 'Q', 'PP', 'PQ', 'QP', 'QQ', 'PQQ', 'QPQ', 'PPQP']
    random.seed(1)
    for word in words:
        MS.set_scale(len(word)); C = MS.coset(word)
        if C is None: print(word, 'inconsistent'); continue
        pts = []
        for _ in range(npts):
            geo = [g * (1 + random.uniform(-0.02, 0.02)) for g in MS.geo]
            t = [F(int(g * 2 ** 20)) * 2 ** (K - 20) / MS.geo[4] for g in geo]
            x = [a + b for a, b in zip(C.x0, babai(C.B, [a - b for a, b in zip(t, C.x0)]))]
            pts.append([int(v) for v in x])
        runs = lean_runs(pts, 8 * len(word))
        ok = 0
        for x, r in zip(pts, runs):
            shapes = [l.split()[0] for l in r]
            want = sum(((MS.P_sh if c == 'P' else MS.Q_sh) for c in word), [])
            if shapes != want: print(word, 'shape mismatch', shapes, r[-1:]); continue
            st = [F(v) for v in x]; good = True
            for i, c in enumerate(word):
                st = apply(MAPS[c], st)
                got = [int(v) for v in r[8 * i + 7].split()[1:]]
                if [got[1], got[2], got[3], got[4], got[0]] != [int(v) for v in st]: good = False
            ok += good
            if not good: print(word, 'position mismatch', x)
        print(f"{word}: {ok}/{len(pts)} starts follow the word on the proved model with the predicted positions")

if __name__ == '__main__': main()
