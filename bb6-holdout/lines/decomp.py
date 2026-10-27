"""The machine's tail as a sum over its segment lines: each GMM state a class of even n reaches within D digits is a
line; its contribution is 2^-depth times its own tail (rline, cut = total - depth).  usage: decomp.py D total"""
import subprocess, sys, json
D, TOT = int(sys.argv[1]), int(sys.argv[2])
CS = '../csearch/'
lines = []
for l in subprocess.run([CS + 'r1dlines', str(D)], capture_output=True, text=True).stdout.split('\n'):
    if l.startswith('L '):
        _, bits, am, m0, aE, E0, rd = l.split(); lines.append(tuple(map(int, (bits, am, m0, aE, E0))))
out = []
for (bits, am, m0, aE, E0) in lines:
    r = subprocess.run(['nice', '-n', '19', CS + 'rline', str(TOT - bits), str(am), str(m0), str(aE), str(E0)], capture_output=True, text=True)
    hb = {}
    for l in r.stdout.split('\n'):
        if l.startswith('hbin'): _, h, v = l.split(); hb[float(h)] = float(v)
    tail = [sum(v for h, v in hb.items() if h >= x / 4 - 1e-9) for x in range(0, 80)]   # quarter-halving grid
    reach = max([h for h, v in hb.items() if v > 0] + [-9]) + 0.125
    out.append(dict(bits=bits, line=(am, m0, aE, E0), tail=tail, reach=reach))
json.dump(out, open(f'../lines/decomp_{D}_{TOT}.json', 'w'))
print(len(out), 'lines')
for x in range(4, 15):
    contrib = sorted(((2.0 ** -o['bits']) * o['tail'][4 * x], o) for o in out)[::-1]
    s = sum(c for c, _ in contrib)
    top = contrib[0]
    print('x=%2d  sum over lines %.3e   top line share %.2f (depth %d, reach %.2f)' % (x, s, top[0] / s if s else 0, top[1]['bits'], top[1]['reach']))
