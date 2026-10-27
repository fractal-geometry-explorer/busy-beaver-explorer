"""Sum the outputs of PassShapes.lean over the trees for R < 178 (each tree weighted equally, as PassStats.lean
averages them) and print them next to the tree for R >= 178.

usage: python3 passshapes_sum.py passshapes_20.out passshapes_20_small_a.out passshapes_20_small_b.out
"""
import re
import sys

pat = re.compile(r'^(\S+) d=(\d+): cut leaves (\d+), measure ([\d.e-]+) \(decided ([\d.e-]+)\); met four walls: (\d+) '
                 r'leaves, measure ([\d.e-]+); met any extra-wall shape: measure ([\d.e-]+); slice cut leaves (\d+) '
                 r'\(four walls: (\d+)\)')
walls = re.compile(r'^  most walls in one round start on the path, by measure: \[(.*)\]')
rows = {}
for fn in sys.argv[1:]:
    w = None
    for line in open(fn):
        mw = walls.match(line)
        if mw and w is not None:
            # (walls, measure) pairs; four or more walls in any shape
            pairs = re.findall(r'\((\d+), ([\d.e-]+)\)', mw.group(1))
            rows[w]['four_any'] = sum(float(x) for k, x in pairs if int(k) >= 4)
            continue
        m = pat.match(line)
        if m:
            w = m.group(1)
            rows[w] = dict(d=int(m.group(2)), leaves=int(m.group(3)), cut=float(m.group(4)), dec=float(m.group(5)),
                           four_leaves=int(m.group(6)), four=float(m.group(7)), ew=float(m.group(8)),
                           slice_cuts=int(m.group(9)), slice_four=int(m.group(10)))


def show(name, rs):
    n = len(rs)
    if n == 0:
        return
    cut = sum(r['cut'] for r in rs) / n
    dec = sum(r['dec'] for r in rs) / n
    four = sum(r['four'] for r in rs) / n
    four_any = sum(r.get('four_any', 0.0) for r in rs) / n
    ew = sum(r['ew'] for r in rs) / n
    leaves = sum(r['leaves'] for r in rs)
    fl = sum(r['four_leaves'] for r in rs)
    sc = sum(r['slice_cuts'] for r in rs)
    sf = sum(r['slice_four'] for r in rs)
    und = cut - dec
    print(f'{name} ({n} trees): cut {cut:.6f} of a class (decided halts {dec:.6f}, the rest {und:.6f}); '
          f'met G W W W W {four:.6f} = {100 * four / und:.2f}% of the rest; four walls in any shape {four_any:.6f} = '
          f'{100 * four_any / und:.2f}%; any extra-wall shape {ew:.6f} = '
          f'{100 * ew / und:.2f}% of the rest; cut leaves {leaves} ({fl} with four walls), slice cut leaves {sc} '
          f'({sf} with four walls)')


small = [r for w, r in rows.items() if w != 'sym']
show('R < 178', small)
if 'sym' in rows:
    show('R >= 178', [rows['sym']])
missing = [R for R in range(2, 178, 2) if str(R) not in rows]
if missing:
    print('missing R:', missing)
worst = sorted(((r.get('four_any', 0.0) / max(r['cut'] - r['dec'], 1e-30), w) for w, r in rows.items()),
               reverse=True)[:5]
print('largest shares of four walls (any shape) in a tree\'s undecided cut measure:',
      ', '.join(f'R = {w}: {100 * s:.2f}%' for s, w in worst))
