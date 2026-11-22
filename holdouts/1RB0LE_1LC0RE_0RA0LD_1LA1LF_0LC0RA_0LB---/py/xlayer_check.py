"""Check a run against the law of the X layout, and list the changes of era.

Reads the events printed by c/cascade_events.c, keeps the full ones (the tape left of the head exactly
0^inf 1 0 [N]) and parses each, in tokens of two cells (z = 00, a = 10, c = 01, d = 11), as

    N | A> | Z | d c a X d | C | R          (the X layout, X a word of k >= 1 digits)
    N | A> | Z | d | C | R                  (the plain layout, k = 0)

with Z and X in digits za = 0, aa = 1, C in digits zc = 0, cc = 1 followed by one c, R in digits az = 0, aa = 1, all
lowest digit first, and N base 3 (3-cell digits 100 = 0, 110 = 1, 010 = 2, lowest next to the head).

The law checked for two consecutive full events in the X layout with the same widths: N + 1 and Z + 1; when Z
wraps, X + 1 (mod 2^k) and C + 24/2^k, and 3 more when X wraps; when C wraps, R + 3.  (In other words
2^k C + 3 X gains 27 at every wrap of Z.)  Every pair of consecutive full events whose widths differ is printed: these
are the changes of era.

usage (from the repository root):
  gcc -O2 -o cascade_events holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/c/cascade_events.c
  ./cascade_events MACHINE 0 300000000 0 | python3 holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/py/xlayer_check.py
"""
import sys, re, collections
T = {'00': 'z', '10': 'a', '01': 'c', '11': 'd'}
D3 = {'100': 0, '110': 1, '010': 2}
PAT = re.compile(r'^((?:za|aa)+)d(?:ca((?:za|aa)*)d)?((?:zc|cc)+)c((?:az|aa)+)$')

def bits(s, one):
    return sum(1 << (i // 2) for i in range(0, len(s), 2) if s[i:i + 2] == one)

def parse(line):
    f = line.split()
    if len(f) < 5:
        return None
    k, p, L, _, R = f
    n = nw = 0; pw = 1; l = L
    while len(l) >= 3 and l[-3:] in D3:
        n += D3[l[-3:]] * pw; pw *= 3; nw += 1; l = l[:-3]
    if l.lstrip('0') != '10':
        return 'inner'
    s = R + '0000'
    t = ''.join(T[s[i:i + 2]] for i in range(0, len(s) - 2, 2)).rstrip('z')
    m = PAT.match(t)
    if not m:
        return 'other'
    z, x, c, r = m.groups(); x = x or ''
    return dict(k=int(k), nw=nw, n=n, zw=len(z) // 2, z=bits(z, 'aa'), xw=len(x) // 2, x=bits(x, 'aa'),
                cw=len(c) // 2, c=bits(c, 'cc'), rw=len(r) // 2, r=bits(r, 'aa'))

def show(e):
    return 'step %d: N %d (%d digits), Z %d (%d), X %d (%d), C %d (%d), R %d (%d)' % (
        e['k'], e['n'], e['nw'], e['z'], e['zw'], e['x'], e['xw'], e['c'], e['cw'], e['r'], e['rw'])

WID = ('zw', 'xw', 'cw', 'rw')
stats = collections.Counter(); prev = None; changes = []; lastfull = None
for line in sys.stdin:
    e = parse(line)
    if e is None or e == 'inner':
        continue
    if e == 'other':
        stats['full event of another shape'] += 1; prev = None; continue
    if lastfull is not None and any(lastfull[w] != e[w] for w in WID):
        changes.append((lastfull, e))
    lastfull = e
    if prev is not None and prev['xw'] > 0 and all(prev[w] == e[w] for w in WID):
        p = prev; k = p['xw']; q = dict(p)
        q['n'] = p['n'] + 1; q['z'] = p['z'] + 1
        if q['n'] == 3 ** p['nw']:
            q['n'] = 0; q['nw'] += 1
        if q['z'] == 1 << p['zw']:
            q['z'] = 0; q['x'] = p['x'] + 1; add = 24 >> k
            if q['x'] == 1 << k:
                q['x'] = 0; add += 3
            q['c'] = p['c'] + add
            if q['c'] >= 1 << p['cw']:
                q['c'] -= 1 << p['cw']; q['r'] = p['r'] + 3
        if all(q[a] == e[a] for a in ('n', 'nw', 'z', 'x', 'c', 'r')):
            stats['X layout, k = %d: by the law' % k] += 1
        else:
            stats['MISMATCH'] += 1
            if stats['MISMATCH'] <= 5:
                print('mismatch', show(p), '->', show(e), file=sys.stderr)
    prev = e
for a, v in sorted(stats.items()):
    print(a, v)
print('changes of width between consecutive full events of the two layouts:')
for a, b in changes:
    print('  ' + show(a) + '\n    -> ' + show(b))
