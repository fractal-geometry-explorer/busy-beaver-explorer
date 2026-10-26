"""Check the hybrid simulator against direct simulation on random small configurations (gap + 3 to 6 walls)."""
import sys, random, subprocess, os
sys.path.insert(0, '../conc')
from buildtape import build
import hybsim
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
SCR = os.path.dirname(os.path.abspath(__file__)) + '/../val_tape.txt'
agree = disagree = 0; halts = 0
for trial in range(N):
    k = random.randint(3, 6); Wd = random.randint(60, 3000)
    # walls alternate odd, even, ...; at least 5 apart; last 1 at Wd-1
    while True:
        ps = sorted(random.sample(range(6, Wd - 4), k)); ok = all(b - a >= 5 for a, b in zip(ps, ps[1:]))
        ps = [p + ((i % 2 == 0) != (p % 2 == 1)) for i, p in enumerate(ps)]
        ok = ok and all(b - a >= 4 for a, b in zip(ps, ps[1:])) and ps[-1] <= Wd - 4
        Wd2 = Wd + (((Wd - 1) % 2 == 0) != (k % 2 == 0))      # last cell must be a 1
        if ok: break
    marks = [('G', 1)] + [('W', p) for p in ps]
    try:
        t = build(marks, Wd2)
    except AssertionError as e:
        continue
    open(SCR, 'w').write(t)
    out = subprocess.run(['../csearch/tmrun', SCR, '3', 'E', '20000000000'], capture_output=True, text=True).stdout.split('\n')[0]
    res = hybsim.run(hybsim.config_from(marks, Wd2), log=lambda *a: None); res.pop('cfg')
    if out.startswith('HALT'):
        st = int(out.split()[3].rstrip(','))
        same = res['result'] == 'halt' and res['steps'] == st; halts += 1
    elif out.startswith('clean'):
        n = int(out.split()[4])
        same = res['result'] == 'clean' and res['n'] == n
    else:
        same = None
    if same: agree += 1
    else:
        disagree += 1; print("DISAGREE", marks, Wd2, out, res)
print(f"{agree} agree, {disagree} disagree, {halts} halts")
