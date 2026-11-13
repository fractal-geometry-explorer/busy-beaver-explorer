"""Runs the block macro machine from record 1 for N records; prints every reset (countdown block exhausted) and
progress every EVERY records.  usage: python3 run_macro.py N EVERY"""
import sys, time
from blockmm import macro_step, STATS, CR, CL
N = int(float(sys.argv[1])); every = int(float(sys.argv[2]))
cur = ((), 0, [(0, 1), (1, 0)]); steps = 4; rec = 1
t0 = time.time()
while rec < N:
    r = macro_step(*cur)
    if r[0] is None:
        print('HALT', rec, steps, r); break
    cur, st, _ = r; steps += st; rec += 1
    bl = cur[2]
    if bl and bl[0][0] <= 1 and len(bl) > 2 and bl[1][0] > 100:
        print('reset rec %d step %d | %s' % (rec, steps, ' '.join('%d%s' % (D, 'oi'[x]) for D, x in bl[:8])), flush=True)
    if rec % every == 0:
        w = 1 + sum(2 * D + 1 for D, x in bl)
        print('rec', rec, 'step', steps, 'blocks', len(bl), 'width', w, 'time', round(time.time() - t0, 1), flush=True)
print('END rec', rec, 'steps', steps, 'symbolic runs', STATS['runs'], 'right rules', len(CR), 'left rules', len(CL))
