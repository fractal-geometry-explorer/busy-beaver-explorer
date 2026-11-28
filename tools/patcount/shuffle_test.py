#!/usr/bin/env python3
"""shuffle_test.py TM [--samples S] [--tmax T] [--run N] [--rad R] [--seed X]

Can any invariant written in pattern counts exclude the halt?  A cheap necessary test.

Take configurations of the real run at random times.  For a vocabulary V (n-grams of raw cells, or n-grams of
run-length tokens), rearrange each half tape beyond an exact window of radius R so that the multiset of V-patterns
on that side is unchanged (a random Euler trail of the n-gram graph, first and last n-1 tokens fixed).  The new tape
has the same abstract description as the real one.  Run the machine from it.  If it halts, the counter program
built from V reaches the halt from a state it must contain, whatever the solver and whatever cap: V is refuted
for this machine.  If no rearranged tape halts, V survives the test (nothing is proved).

Vocabularies: cells:n   n-grams of cells
              d1:n      n-grams of tokens 1^d 0 read outward from the head
              d0:n      n-grams of tokens 0^z 1 read outward
              runs:n    n-grams of maximal runs (symbol, length)
"""
import sys, random, subprocess, os, re, argparse
here = os.path.dirname(os.path.abspath(__file__))
def tok(s, kind):
    if kind == 'cells': return list(s)
    if kind == 'd1':
        parts = s.split('0'); out = [p + '0' for p in parts[:-1]]
        if parts[-1]: out.append(parts[-1])
        return out
    if kind == 'd0':
        return re.findall(r'0*1|0+$', s)
    if kind == 'runs':
        return [m.group(0) for m in re.finditer(r'0+|1+', s)]
MODES = ['random']
def euler_shuffle(t, n, rng):
    """random sequence with the same n-gram multiset, the same first n-1 and last n-1 tokens"""
    k = len(t)
    if n == 1:
        if k <= 2: return t
        mid = t[1:]; rng.shuffle(mid); return t[:1] + mid
    if k <= n: return t
    adj = {}
    for i in range(k - n + 1):
        adj.setdefault(tuple(t[i:i + n - 1]), []).append(t[i + n - 1])
    mode = rng.choice(MODES)
    if mode == 'random':
        for v in adj.values(): rng.shuffle(v)
    else:  # adversarial: rare n-grams as early (or as late) as possible; ties at random
        from collections import Counter
        freq = Counter(); 
        for node, v in adj.items():
            for x in v: freq[node + (x,)] += 1
        sgn = 1 if mode == 'rare-first' else -1
        for node, v in adj.items():
            rng.shuffle(v); v.sort(key=lambda x: -sgn * freq[node + (x,)])   # popped from the end: rare first if sgn=1
    start = tuple(t[:n - 1]); stack = [(start, None)]; out = []
    while stack:                       # Hierholzer
        node, lab = stack[-1]
        a = adj.get(node)
        if a: x = a.pop(); stack.append((node[1:] + (x,), x))
        else: out.append(lab); stack.pop()
    out = out[:-1][::-1]
    res = list(start) + out
    assert len(res) == k
    return res
def main():
    ap = argparse.ArgumentParser(); ap.add_argument('tm'); ap.add_argument('--samples', type=int, default=60)
    ap.add_argument('--tmax', type=int, default=3000000); ap.add_argument('--run', type=int, default=1000000)
    ap.add_argument('--rad', type=int, default=8); ap.add_argument('--seed', type=int, default=1); ap.add_argument('--shuffles', type=int, default=4); ap.add_argument('--iter', type=int, default=0); ap.add_argument('--logsteps', type=float, default=4.5)
    ap.add_argument('--vocab', default='cells:3,cells:5,cells:8,cells:12,cells:16,d1:1,d1:2,d1:3,d1:4,d0:1,d0:2,d0:3,d0:4,runs:1,runs:2,runs:3,runs:4')
    ap.add_argument('--adversarial', action='store_true')
    a = ap.parse_args(); rng = random.Random(a.seed); R = a.rad
    if a.adversarial: MODES.extend(['rare-first', 'rare-last'])
    times = sorted(rng.randrange(1000, a.tmax) for _ in range(a.samples))
    dump = subprocess.run([here + '/tmrun', 'dump', a.tm] + [str(x) for x in times], capture_output=True, text=True).stdout.split('\n')
    cfgs = []
    for l in dump:
        p = l.split(' ')
        if p[0] == 'HALT': print(a.tm, 'real run halts', l); return
        if len(p) == 3: cfgs.append((int(p[0]), p[1], p[2]))
    if a.iter:
        # iterated test: rearrange, run a random number of steps, rearrange again, ...  This samples the forward
        # closure of the counter program started from real late configurations.
        for voc in a.vocab.split(','):
            kind, n = voc.split(':'); n = int(n); live = [(q, L, Rs) for (q, L, Rs) in cfgs]; nh = 0; first = None; rounds = 0
            for rd in range(a.iter):
                if not live: break
                rounds = rd + 1; jobs = []
                for (q, L, Rs) in live:
                    if L == '-': L = ''
                    nearL, farL = L[max(0, len(L) - R):], L[:max(0, len(L) - R)][::-1]
                    nearR, farR = Rs[:R + 1], Rs[R + 1:]
                    nl = ''.join(euler_shuffle(tok(farL, kind), n, rng)) if farL else ''
                    nr = ''.join(euler_shuffle(tok(farR, kind), n, rng)) if farR else ''
                    jobs.append('%d %s %s %d' % (q, (nl[::-1] + nearL) or '-', nearR + nr, int(10 ** rng.uniform(0, a.logsteps))))
                out = subprocess.run([here + '/tmrun', 'step', a.tm], input='\n'.join(jobs) + '\n', capture_output=True, text=True).stdout.strip().split('\n')
                nl2 = []
                for l in out:
                    p = l.split(' ')
                    if p[0] == 'HALT':
                        nh += 1
                        if first is None: first = rd + 1
                    else: nl2.append((int(p[0]), p[1], p[2]))
                live = nl2
            print('%s R=%d %-8s ITER chains=%d rounds=%d halted_chains=%d first_halt_round=%s' % (a.tm, R, voc, len(cfgs), rounds, nh, first), flush=True)
        return
    for voc in a.vocab.split(','):
        kind, n = voc.split(':'); n = int(n); jobs = []; owner = []; distinct = 0
        for ci, (q, L, Rs) in enumerate(cfgs):
            nearL, farL = L[max(0, len(L) - R):], L[:max(0, len(L) - R)][::-1]     # far parts read outward
            nearR, farR = Rs[:R + 1], Rs[R + 1:]
            for _ in range(a.shuffles):
                nl = ''.join(euler_shuffle(tok(farL, kind), n, rng)) if farL else ''
                nr = ''.join(euler_shuffle(tok(farR, kind), n, rng)) if farR else ''
                if nl == farL and nr == farR: continue
                distinct += 1
                jobs.append('%d %s %s' % (q, (nl[::-1] + nearL) or '-', nearR + nr)); owner.append(ci)
        res = subprocess.run([here + '/tmrun', 'run', a.tm, str(a.run)], input='\n'.join(jobs) + '\n', capture_output=True, text=True).stdout.split()
        halted = [int(x) for x in res if int(x) >= 0]; hc = len(set(o for o, x in zip(owner, res) if int(x) >= 0))
        print('%s R=%d %-8s rearranged=%d halted=%d configs_with_halt=%d/%d median_halt_step=%s' % (
            a.tm, R, voc, distinct, len(halted), hc, len(cfgs), sorted(halted)[len(halted) // 2] if halted else '-'), flush=True)
main()
