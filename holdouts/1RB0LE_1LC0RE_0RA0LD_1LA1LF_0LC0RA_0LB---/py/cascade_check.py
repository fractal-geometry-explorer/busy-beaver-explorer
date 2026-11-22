"""Check a run against the cascade rule of the later eras.

Reads the events printed by cascade_events.c (state A on a 0, a base-3 digit of N to the left, a digit of Z to
the right).  Those whose left part is not exactly 0^inf 1 0 [N] are turns inside a sweep and are skipped; every
other one is parsed as

    0^inf 1 0 [N] A> 0 [Z] 1 1 [C] 0 1 [R] 0^inf

with tokens of two cells right of the head (z = 00, a = 10, c = 01, d = 11): Z in digits za = 0, aa = 1, C in
digits zc = 0, cc = 1 followed by one c, R in digits az = 0, aa = 1, all lowest digit first; N base 3 in 3-cell
digits 100 = 0, 110 = 1, 010 = 2, lowest digit next to the head.  For every two consecutive events that both
have this shape it checks the cascade: N + 1, Z + 1; when Z wraps, C + 3; when C wraps, R + 3 (R may gain a
digit, then C loses one and Z gains one: an era change, counted separately).

usage (from the repository root):
  gcc -O2 -o cascade_events holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/c/cascade_events.c
  ./cascade_events MACHINE 0 300000000 0 | python3 holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/py/cascade_check.py
"""
import sys, re, collections
T = {'00': 'z', '10': 'a', '01': 'c', '11': 'd'}
D3 = {'100': 0, '110': 1, '010': 2}
PAT = re.compile(r'^((?:za|aa)+)d((?:zc|cc)+)c((?:az|aa)+)$')

def shape(t):
    """A token string in words: Zk (za/aa digits), Ck (zc/cc digits and a c), Ak (az/aa digits), other tokens as they are."""
    out = []; i = 0
    m = re.match(r'(?:za|aa)+', t)
    if m:
        out.append('Z%d' % (len(m.group(0)) // 2)); i = m.end()
    while i < len(t):
        m = re.compile(r'(?:zc|cc)+c').match(t, i)
        if m and len(m.group(0)) >= 3:
            out.append('C%d' % ((len(m.group(0)) - 1) // 2)); i = m.end(); continue
        m = re.compile(r'(?:az|aa)+').match(t, i)
        if m and t[m.end():m.end() + 1] in ('', 'z', 'd', 'c') and len(m.group(0)) >= 2:
            out.append('A%d' % (len(m.group(0)) // 2)); i = m.end(); continue
        out.append(t[i]); i += 1
    return ' '.join(out)

def bits(s, one):
    return sum(1 << (i // 2) for i in range(0, len(s), 2) if s[i:i + 2] == one)

def parse(line):
    f = line.split()
    if len(f) < 5:
        return None
    k, p, L, _, R = f
    s = R + '0000'
    t = ''.join(T[s[i:i + 2]] for i in range(0, len(s) - 2, 2)).rstrip('z')
    n = nw = 0; pw = 1; l = L
    while len(l) >= 3 and l[-3:] in D3:
        n += D3[l[-3:]] * pw; pw *= 3; nw += 1; l = l[:-3]
    if l.lstrip('0') != '10':  # not a full event: N does not reach the left end 0^inf 1 0 (an inner turn of a sweep)
        return 'inner'
    m = PAT.match(t)
    if not m:
        sh = shape(t)  # the widths of the words, X's value hidden: runs of a z / a a written A
        sh = re.sub(r'(?:(?:z a|A\d+) ?)+', lambda w: 'X%d ' % sum(1 if x == 'z a' else int(x[1:]) for x in re.findall(r'z a|A\d+', w.group(0))), sh).strip()
        sh = re.sub(r'X(\d+)$', r'R\1', sh)  # the last word is R
        return ('N%d ' % nw) + sh
    z, c, r = m.groups()
    return dict(k=int(k), nw=nw, n=n, zw=len(z) // 2, z=bits(z, 'aa'), cw=len(c) // 2, c=bits(c, 'cc'),
                rw=len(r) // 2, r=bits(r, 'aa'))

def step(e):
    """The predicted next event, and whether it is an era change."""
    q = dict(e); era = False
    q['n'] = e['n'] + 1
    if q['n'] == 3 ** e['nw']:
        q['n'] = 0; q['nw'] += 1
    q['z'] = e['z'] + 1
    if q['z'] == 1 << e['zw']:
        q['z'] = 0
        q['c'] = e['c'] + 3
        if q['c'] >= 1 << e['cw']:
            q['c'] -= 1 << e['cw']
            q['r'] = e['r'] + 3
            if q['r'] >= 1 << e['rw']:
                era = True
    return q, era

stats = collections.Counter(); prev = None; eras = []; widths = {}; shapes = {}
for line in sys.stdin:
    e = parse(line)
    if e == 'inner':
        stats['inner (skipped)'] += 1; continue
    if isinstance(e, str):
        k = int(line.split()[0]); w = shapes.setdefault(e.split(' ', 1)[1], [k, 0, 0])
        w[1] = k; w[2] += 1
        prev = None; stats['full event of another shape'] += 1; continue
    w = widths.setdefault((e['cw'], e['rw']), [e['k'], 0, 0, 99, 0])
    w[1] = e['k']; w[2] += 1; w[3] = min(w[3], e['zw']); w[4] = max(w[4], e['zw'])
    if prev is not None:
        q, era = step(prev)
        keys = ('nw', 'n', 'zw', 'z', 'cw', 'c', 'rw', 'r')
        if era:
            eras.append((prev, e)); stats['era change'] += 1
        elif all(q[x] == e[x] for x in keys):
            stats['by the rule'] += 1
        else:
            stats['MISMATCH'] += 1
            if stats['MISMATCH'] <= 5:
                print('mismatch', prev, e, file=sys.stderr)
    prev = e
for k, v in sorted(stats.items()):
    print(k, v)
print('widths of C and R: first and last step, number of full events in the layout, widths of Z')
for (cw, rw), (a, b, n, z0, z1) in sorted(widths.items(), key=lambda x: x[1][0]):
    print('  C %d, R %d: steps %d to %d, %d events, Z %d to %d' % (cw, rw, a, b, n, z0, z1))
print('full events of other shapes (seen 50 times or more; Zk, Ck words of k digits, Xk a word of k a z / a a digits, Rk the last such word):')
for sh, (a, b, n) in sorted(shapes.items(), key=lambda x: x[1][0]):
    if n >= 50:
        print('  %s: steps %d to %d, %d events' % (sh, a, b, n))
for a, b in eras:
    print('era change at step %d: (Z, C, R) widths %d %d %d -> %d %d %d, R %d -> %d, N %d -> %d'
          % (b['k'], a['zw'], a['cw'], a['rw'], b['zw'], b['cw'], b['rw'], a['r'], b['r'], a['n'], b['n']))
