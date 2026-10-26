"""Anatomy of a record run: the longest chain of end meetings, split into lead-in, plain-loop stretch and exit.
usage: anatomy.py n ..."""
import subprocess, sys, re
CS = '../csearch/'
LOOP = {'GWWW', 'GBW', 'GMB', 'GMWW'}
for n in sys.argv[1:]:
    out = subprocess.run([CS + 'lined_tr', 'n'], input=n + '\n', capture_output=True, text=True, env={'TRACE': '1'}).stdout.split('\n')
    shape = ''; ev = []
    for l in out:
        if l.startswith('round'): shape = l.split(':')[1]
        m = re.search(r'end meeting: d = (\d+) \((\w+)\), ([\d.]+) halvings below the width, chain (\d+)', l)
        if m: ev.append((shape, m.group(2), float(m.group(3)), int(m.group(1))))
    # the chain: consecutive end meetings with d' = pred(d), pred(d) = (d-2)/2 if d = 2 mod 4 else d/2 + 4
    best = max(range(len(ev)), key=lambda i: ev[i][2])
    i = best
    pred = lambda d: (d - 2) // 2 if d % 4 == 2 else d // 2 + 4
    while i > 0 and ev[i][3] == pred(ev[i - 1][3]): i -= 1
    run = ev[i:best + 1]
    inloop = [s in LOOP for s, _, _, _ in run]
    first = inloop.index(True) if True in inloop else len(run)
    last = len(run) - 1 - inloop[::-1].index(True) if True in inloop else -1
    print(f'n = {n} ({int(n).bit_length()} digits): run of {len(run)} meetings from {run[0][2]:.2f} to {run[-1][2]:.2f} halvings;'
          f' lead-in {first}, loop {last - first + 1 if last >= first else 0}, exit {len(run) - 1 - last if last >= 0 else 0}')
    print('   ' + ' '.join(f'{s}/{o[0]}' for s, o, h, c in run))
