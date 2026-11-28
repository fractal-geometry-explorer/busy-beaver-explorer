#!/usr/bin/env python3
"""longrun wrapper for one contractsat instance (not resumable: a SAT call cannot be checkpointed, so a chunk
that ends early starts again).  usage: lr_run.py MACHINE side W b,Z,D keysfile"""
import os, sys, json, time, subprocess
ck = os.environ.get('LR_CKPT', '.')
res = os.path.join(ck, 'result.txt')
if os.path.exists(res):
    sys.exit(0)
m, side, W, runs, keys = sys.argv[1:6]
t0 = time.time()
out = os.path.join(ck, 'cert.json')
p = subprocess.run([sys.executable, '-u', 'contractsat.py', m, side, '0', W, '--runs', runs, '--keys', keys,
                    '--out', out + '.tmp'], capture_output=True, text=True)
lines = [l for l in p.stdout.splitlines() if 'round ' not in l]
if p.returncode != 0 or not any(l.startswith(('CERT', 'NONE')) for l in lines):
    sys.stderr.write(p.stdout[-2000:] + p.stderr[-2000:])
    sys.exit(2)
if os.path.exists(out + '.tmp'):
    os.rename(out + '.tmp', out)
with open(res + '.tmp', 'w') as f:
    f.write('\n'.join(lines) + '\nseconds %.0f\n' % (time.time() - t0))
os.rename(res + '.tmp', res)
