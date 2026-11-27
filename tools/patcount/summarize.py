#!/usr/bin/env python3
"""summarize.py FILE...: table of halted chains per machine and vocabulary from shuffle_test.py --iter output"""
import re, sys, collections
res = collections.defaultdict(dict); vocs = []
for f in sys.argv[1:]:
    for l in open(f):
        m = re.match(r'(\S+) R=\d+ (\S+)\s+ITER chains=(\d+) rounds=(\d+) halted_chains=(\d+)', l)
        if m:
            res[m.group(1)][m.group(2)] = '%s/%s' % (m.group(5), m.group(3))
            if m.group(2) not in vocs: vocs.append(m.group(2))
def key(tm): return [int(res[tm].get(v, '99/1').split('/')[0]) for v in vocs]
print('| machine | ' + ' | '.join(vocs) + ' |'); print('|---|' + '---|' * len(vocs))
for tm in sorted(res, key=key): print('| %s | ' % tm + ' | '.join(res[tm].get(v, '-') for v in vocs) + ' |')
