"""The machine's segment lines (GMM states reached by classes of even n, from r1dlines) against random lines with the
same 2-adic shape: per-line tails from rline at a common cut.  usage: machlines.py depth cut seed"""
import random, subprocess, sys, json
D, cut, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
CS = '../csearch/'
R = random.Random(seed)
def v2(x):
    x = abs(x); k = 0
    while x % 2 == 0: x //= 2; k += 1
    return k
def tails(am, m0, aE, E0):
    r = subprocess.run([CS + 'rline', str(cut), str(am), str(m0), str(aE), str(E0)], capture_output=True, text=True)
    if r.returncode != 0: return None
    hb = {}
    for l in r.stdout.split('\n'):
        if l.startswith('hbin'): _, h, v = l.split(); hb[float(h)] = float(v)
    return [sum(v for h, v in hb.items() if h >= x - 1e-9) for x in range(25)]
lines = []
for l in subprocess.run([CS + 'r1dlines', str(D)], capture_output=True, text=True).stdout.split('\n'):
    if l.startswith('L '):
        _, bits, am, m0, aE, E0, rd = l.split(); lines.append(tuple(map(int, (bits, am, m0, aE, E0))))
print(len(lines), 'machine lines up to depth', D)
res = []
for (bits, am, m0, aE, E0) in lines:
    tm = tails(am, m0, aE, E0)
    # random line with the same valuations of the direction and random offsets of the right parity
    va, vE = v2(am), v2(aE)
    oE = aE >> vE                       # odd part of aE (1 for every machine line so far)
    raE = oE << vE
    while True:
        ram = (2 * R.randint(0, 1 << 40) + 1) << va
        ram %= raE
        if ram > 0 and v2(ram) == va: break
    rm0 = 2 * R.randint(0, 1 << 24); rE0 = 2 * R.randint(0, 1 << 24) + 1
    tr = tails(ram, rm0, raE, rE0) if ram < raE else None
    res.append(dict(bits=bits, line=(am, m0, aE, E0), tm=tm, rline=(ram, rm0, raE, rE0), tr=tr))
json.dump(res, open(f'../lines/mach_{D}_{cut}_{seed}.json', 'w'))
ok = [r for r in res if r['tm'] and r['tr']]
print(len(ok), 'pairs computed;', sum(1 for r in res if not r['tm']), 'machine lines and', sum(1 for r in res if not r['tr']), 'random lines failed')
print(' x  machine: reach share  mean tail   | random same shape: reach share  mean tail')
N = len(ok)
for x in range(2, 19):
    a = [r['tm'][x] for r in ok]; b = [r['tr'][x] for r in ok]
    print('%2d   %.4f  %.3e   |   %.4f  %.3e' % (x, sum(t > 0 for t in a) / N, sum(a) / N, sum(t > 0 for t in b) / N, sum(b) / N))
