"""Partition check over the union of split-path files written by check_tree.py --paths: the paths must form a
complete prefix code (no path a prefix of another, no duplicates, measures 2^-len summing to 1).
usage: python3 kraft.py paths1.txt paths2.txt ..."""
import sys
from fractions import Fraction as F
paths = []
for fn in sys.argv[1:]:
    paths.extend(l.strip() for l in open(fn) if l.strip())
paths.sort()
pre = sum(1 for i in range(1, len(paths)) if paths[i].startswith(paths[i - 1]))
dup = len(paths) - len(set(paths))
tot = sum(F(1, 2 ** len(p)) for p in paths)
print('paths %d; prefix violations %d; duplicates %d; total measure %s' % (len(paths), pre, dup, float(tot)))
print('PARTITION VALID' if pre == 0 and dup == 0 and tot == 1 else 'PARTITION NOT VERIFIED')
