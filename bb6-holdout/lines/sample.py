"""Per-segment tails of random lines of GMM states (rline), against the plane tail.
usage: sample.py nlines cut seed"""
import random, subprocess, sys, math, json
N, cut, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
R = random.Random(seed)
BIN = '../csearch/rline'
out = []
while len(out) < N:
    p, q = R.randint(1, 31), R.randint(1, 31)
    if p >= q or math.gcd(p, q) % 2 == 0: continue
    am, aE = 2 * p, 2 * q
    m0 = 2 * R.randint(0, 1 << 20); E0 = 2 * R.randint(0, 1 << 20) + 1
    r = subprocess.run([BIN, str(cut), str(am), str(m0), str(aE), str(E0)], capture_output=True, text=True)
    hb = {}
    for l in r.stdout.split('\n'):
        if l.startswith('hbin'): _, h, v = l.split(); hb[float(h)] = float(v)
    lost = float(r.stderr.split('undecided ')[1].split(',')[0])
    tail = [sum(v for h, v in hb.items() if h >= x - 1e-9) for x in range(0, 25)]
    out.append(dict(am=am, m0=m0, aE=aE, E0=E0, lost=lost, tail=tail))
json.dump(out, open(f'../lines/lines_{cut}_{seed}.json', 'w'))
plane = {3: 4.1336e-2, 4: 1.7660e-3, 5: 2.0761e-4, 6: 5.4962e-5, 7: 8.084e-6, 8: 2.561e-6, 9: 1.940e-7, 10: 5.509e-8, 11: 8.01e-9, 12: 2.57e-9, 13: 1.85e-10, 14: 5.20e-11, 15: 7.2e-12, 16: 2.3e-12, 17: 1.1e-13, 18: 2.7e-14}
print('lost: mean %.2e max %.2e' % (sum(o['lost'] for o in out) / N, max(o['lost'] for o in out)))
print(' x   plane      mean       median     q90        q99        zero-share')
for x in range(3, 19):
    v = sorted(o['tail'][x] for o in out)
    mean = sum(v) / N
    print('%2d  %.3e  %.3e  %.3e  %.3e  %.3e  %.2f' % (x, plane.get(x, 0), mean, v[N // 2], v[int(N * 0.9)], v[int(N * 0.99)], sum(1 for t in v if t == 0) / N))
