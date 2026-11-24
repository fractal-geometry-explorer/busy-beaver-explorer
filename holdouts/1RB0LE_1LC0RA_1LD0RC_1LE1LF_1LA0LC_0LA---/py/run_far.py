"""Run the block-list map (py/blockmap.py, with jumps) from blank tape; print a line every K refills, every rule the
first time it is used, and stop at a window no rule covers.  usage: run_far.py SECONDS K"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import blockmap as B
M = B.Map(B.START); t = time.time(); refills = 0; seen = set()


def mag(v): return f"10^{len(str(v)) - 1}" if v > 0 else '0'


try:
    while time.time() - t < float(sys.argv[1]):
        if not B.jump(M): M.fast()
        for r in M.rules:
            if r not in seen:
                seen.add(r); print('first', r, 'at refill', refills, 'sweep', mag(M.sweeps), flush=True)
        if M.left and M.left[0][0] == 0:
            refills += 1
            if refills % int(sys.argv[2]) == 0:
                runs = len(M.left) + sum(1 for x in M.R if type(x) is tuple)
                big = max(v for v, c in M.left)
                print(refills, 'refills', mag(M.sweeps), 'sweeps', runs, 'runs', 'largest done block', mag(big),
                      round(time.time() - t), 's', flush=True)
except B.Unknown as e:
    print('UNKNOWN window at refill', refills, 'sweep', M.sweeps, e)
print('end', refills, 'refills', mag(M.sweeps), 'sweeps', {k: (v if v < 10**6 else mag(v)) for k, v in M.rules.items()})
