"""phases.py FILE [THRESH] [MINLEN]: group consecutive turn lines of c/msim_turns (mode t) by their skeleton: the words of the
runs of at least THRESH copies, in order, with the head position.  Prints one line per group: first step, number of
lines, and the skeleton with first -> last counts."""
import sys, re
T = int(sys.argv[2]) if len(sys.argv) > 2 else 50
MINLEN = int(sys.argv[3]) if len(sys.argv) > 3 else 1
def skel(line):
    f = line.split(); step = int(f[0]); st = f[1]; sk = [st]; cn = []
    for tok in f[2:]:
        if tok == '|': sk.append('|'); continue
        m = re.match(r'(\d+)\^(\d+)$', tok)
        if m and int(m.group(2)) >= T: sk.append(m.group(1)); cn.append(int(m.group(2)))
    return step, tuple(sk), cn
cur = None; out = []
def flush():
    if cur and cur[3] >= MINLEN:
        step, sk, c0, n, c1 = cur; i = 0; parts = []
        for w in sk:
            if w == '|' or not w[0].isdigit(): parts.append(w)
            else:
                parts.append('%s^%d' % (w, c0[i]) if c0[i] == c1[i] else '%s^(%d->%d)' % (w, c0[i], c1[i])); i += 1
        print(step, 'x%d' % n, ' '.join(parts))
for line in open(sys.argv[1]):
    if not line[0].isdigit(): continue
    step, sk, cn = skel(line)
    if cur and cur[1] == sk: cur[3] += 1; cur[4] = cn
    else:
        flush(); cur = [step, sk, cn, 1, cn]
flush()
