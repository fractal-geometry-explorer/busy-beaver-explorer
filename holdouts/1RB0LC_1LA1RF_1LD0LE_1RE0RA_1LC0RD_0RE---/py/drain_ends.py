"""Read the output of py/rsim_events.py and print the tape as a list of blocks (10)^n each time the list, apart from
its last block, changes: the ends of the drains.  The blocks left of the first (10)^10 are the reservoir
(words 1010101, each a block (10)^3); its size is printed.  usage: python3 py/drain_ends.py events.txt"""
import re, sys


def expand(parts):
    out = []
    for p in parts:
        if p.startswith('('):
            continue
        if p.startswith('['):
            out.append(p[1:-1].replace('>', ''))
            continue
        if '^' in p:
            w, c = p.rsplit('^', 1)
            c = int(c)
            if len(w) * c > 2000000 and w.count('1') * 2 != len(w):
                out.append('R%dR' % c)
            else:
                out.append(w * c)
    return ''.join(out)


def blocks(s):
    s = s.lstrip('0')
    L = []
    for m in re.finditer(r'R[0-9]+R|(?:10)+|1|0', s):
        g = m.group(0)
        if g[0] == 'R':
            L.append('RES' + g[1:-1])
        elif g == '1':
            L.append('|')
        elif g == '0':
            L.append('o')
        else:
            L.append(len(g) // 2)
    out, i = [], 0
    while i < len(L):
        x = L[i]
        if isinstance(x, int) and i + 1 < len(L) and L[i + 1] == '|':
            out.append(x); i += 2
        elif x == '|':
            out.append(0); i += 1
        else:
            out.append(x); i += 1
    while out and out[-1] == 'o':
        out.pop()
    return out


def comp(L):
    o, i = [], 0
    while i < len(L):
        for p in (1, 2, 3, 4):
            seg = L[i:i + p]; c = 1
            while L[i + c * p:i + (c + 1) * p] == seg:
                c += 1
            if c >= 2 and len(seg) == p:
                o.append('(%s)^%d' % (' '.join(map(str, seg)), c)); i += c * p; break
        else:
            o.append(str(L[i])); i += 1
    return ' '.join(o)


prev = prevline = None
for line in open(sys.argv[1]):
    parts = line.split()
    if not parts or parts[0] != 'L' or parts[2] != 'E':
        continue
    L = blocks(expand(parts[3:]))
    if 10 not in L:
        continue
    k = L.index(10)          # the list of blocks starts with (10)^10; left of it, the reservoir
    res = [x for x in L[:k] if x == 3 or str(x).startswith('RES')]
    r = sum(int(str(x)[3:]) if str(x).startswith('RES') else 1 for x in res)
    body = L[k:]
    if len(body) < 2:
        continue
    key = tuple(body[:-1])
    if key != prev:
        if prevline:
            print('   last before:', prevline)
        print(parts[1], 'reservoir', r, '| list', comp(body))
    prev, prevline = key, '%s %s' % (parts[1], comp(body[-4:]))
