"""Abstract search over block_sim's one-stack tape: pair counts capped at K, blocks as queues with a learned middle.

usage: K=6 RUNLIMIT=20000 python3 block_search.py [exact bounces before abstracting]
Prints CLOSED if the set of abstract tapes closes, or FAIL with the chain of tapes that leads to a halt.
"""
import sys, time, collections, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mover_sim as ms
import block_sim as u

nb = int(sys.argv[1]) if len(sys.argv) > 1 else 0
K = int(os.environ.get('K', '6')); RL = int(os.environ.get('RUNLIMIT', '20000'))
u.CFG.update(K=10**30, NF=10**12, NE=10**12, MAXMOVES=10**12, YMAX=10**9, exact=True)
S = ms.start(); Y = list(S.Y); u.normalize(Y)
for i in range(nb): u.bounce(Y); u.normalize(Y)
u.CFG.update(K=K, NF=int(os.environ.get('NF', '2')), NE=int(os.environ.get('NE', '2')),
             MAXMOVES=int(os.environ.get('MAXMOVES', '20000')), YMAX=int(os.environ.get('YMAX', '60')), exact=False)
u.BIG = u.Big()
A = u.abstract_of(Y)
print('start after', nb, 'bounces:', u.show(A)[:300], flush=True)
seen = {u.key(A): A}; par = {u.key(A): None}; t0 = time.time(); rnd = 0
while True:
    rnd += 1; u.CHANGED[0] = False
    q = collections.deque(seen.values()); n = 0; new = 0
    while q:
        st = q.popleft(); n += 1
        outs, fails = u.successors(st, RL)
        if fails:
            print('FAIL', fails[:2]); kk = u.key(st); i = 0
            while kk is not None and i < int(os.environ.get('CH', '40')):
                print('  ', u.show(seen[kk])[:400]); kk = par[kk]; i += 1
            sys.exit(1)
        for B in outs:
            kk = u.key(B)
            if kk not in seen: seen[kk] = B; par[kk] = u.key(st); q.append(B); new += 1
        if n % 20000 == 0:
            print(rnd, n, 'states', len(seen), 'queue', len(q), 'GQ', len(u.GQ), '%.0fs' % (time.time() - t0), flush=True)
    print('round', rnd, 'states', len(seen), 'new', new, 'GQ', len(u.GQ), 'changed', u.CHANGED[0], flush=True)
    if not u.CHANGED[0] and new == 0: break
print('CLOSED', len(seen), 'states, GQ', sorted(map(repr, u.GQ)))
