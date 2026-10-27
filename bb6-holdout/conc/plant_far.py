"""Search small tapes E where a loop state with the last wall far from the end (R = 2^(4P+1)) also has left fuel for P
passes with a, b in a loop-like geometry; follow each in the mark model and on the real machine."""
import sys, subprocess
from plant_end import run
from buildtape import build
P = int(sys.argv[1]); E0 = int(sys.argv[2]); E1 = int(sys.argv[3]); want = int(sys.argv[4]) if len(sys.argv) > 4 else 3
R = 1 << (4 * P + 1); M = 1 << (6 * P + 1); found = 0
for E in range(E0, E1, 4):
    c = E - 1 - R
    if c <= 0 or c % 2 == 0: continue
    b0 = ((578 + 392 * c - 280 * E) * pow(147, -1, M)) % M
    for b in range(b0, c, M):
        if b % 2 or b < 20: continue
        for a in (b // 4 | 1, b // 2 | 1, b // 8 | 1):
            if not (5 < a < b - 4): continue
            out = run(a, b, c, E, rounds=200, verbose=False)
            ds = [d for sh, dd, bad, h in out for d in dd]
            if not ds or min(ds) > 4: continue
            tape = build([('G', 1), ('W', a), ('W', b), ('W', c)], E)
            open('../plant_far.tape', 'w').write(tape)
            res = subprocess.run(['../csearch/tmrun', '../plant_far.tape', '3', 'E', str(10 ** 12)], capture_output=True, text=True).stdout.strip().split('\n')[0]
            print(f"E = {E}, a = {a}, b = {b}, c = {c} (R = {R}, start {E - c - 1} cells from the end); model meeting distances {ds[:14]}; machine: {res}", flush=True)
            found += 1
            break
        if found >= want: break
    if found >= want: break
