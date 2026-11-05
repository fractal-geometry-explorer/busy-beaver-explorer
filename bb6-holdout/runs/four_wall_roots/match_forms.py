"""The 113 EntryFar roots against the loop-entry classes of the clean-tape tree (EntryForms.lean output): is a root the
value of some class's forms (b, c, W) at integer coordinates inside the class's cone?  Also how the entries' limit
shapes (R/W, (W - b)/W as the free variable grows) sit against the roots.  usage: match_forms.py entries.txt"""
import sys, re
from fractions import Fraction as F
from classify import origins
def entry_far(b, W, R): D = W - b; return 15 * W <= 64 * D and 15 * W + 26 <= 32 * (D + R)
def parse(fn):
    out = []
    for l in open(fn):
        if not l.startswith('E '): continue
        parts = [p.strip() for p in l[2:].split('|')]
        D = int(parts[0]); fs = [list(map(int, p.split())) for p in parts[1:5]]
        ts = [list(map(int, t.split())) for t in parts[5].split(';')]
        out.append((D, fs, ts))
    return out
def main():
  roots = []
  for fn in ['n4.tsv', 'n5.tsv']:
      for line in open(fn):
          f = line.split('\t'); R, b, W = int(f[2]), int(f[3]), int(f[4])
          if W % 6 != 2: continue
          for o in origins(b, W, R):
              if o == ['entry']: rt = (b, W, R)
              else:
                  m = re.findall(r'E=(\d+),R=(\d+),b=(\d+)', ' '.join(o))[-1]; rt = (int(m[2]), int(m[0]), int(m[1]))
              if entry_far(*rt): roots.append((fn[:2], f[1], rt))
  cls = parse(sys.argv[1])
  nv = max(len(fs[0]) - 1 for _, fs, _ in cls)
  print('classes', len(cls), 'variables', nv, 'max depth', max(D for D, _, _ in cls),
        'measure', float(sum(F(1, 2 ** D) for D, _, _ in cls)))
  ev = lambda f, x: f[0] + sum(c * xi for c, xi in zip(f[1:], x))
  hits = 0
  for name, i, (b, W, R) in roots:
      c = W - R - 1
      for D, (fa, fb, fc, fW), ts in cls:
          # solve W and b (and c) for the coordinates; the forms use at most two variables
          cols = [k for k in range(1, len(fW)) if fW[k] or fb[k] or fc[k]]
          if len(cols) == 1:
              k = cols[0]; x = [0] * (len(fW) - 1)
              if fW[k] == 0 or (W - fW[0]) % fW[k]: continue
              x[k - 1] = (W - fW[0]) // fW[k]
          elif len(cols) == 2:
              k1, k2 = cols; det = fW[k1] * fb[k2] - fW[k2] * fb[k1]
              if det == 0: continue
              n1 = (W - fW[0]) * fb[k2] - (b - fb[0]) * fW[k2]; n2 = fW[k1] * (b - fb[0]) - fb[k1] * (W - fW[0])
              if n1 % det or n2 % det: continue
              x = [0] * (len(fW) - 1); x[k1 - 1] = n1 // det; x[k2 - 1] = n2 // det
          else: continue
          if ev(fW, x) == W and ev(fb, x) == b and ev(fc, x) == c and all(ev(t, x) >= 0 for t in ts):
              hits += 1; print('HIT', name, i, D, x)
  print('roots', len(roots), 'exact hits', hits)

if __name__ == "__main__": main()
