"""Where 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA--- could halt, and which cursor collisions its run produces.

usage: python3 scan.py halts [L]     every round that halts starts from a tape containing 001111 (or starting with
                                     000111): all tapes  P w Q  with w any word of up to L cells (default 12) and P, Q
                                     from a list of run/separator contexts, one round each (py/tok.round_)
       python3 scan.py run [STEPS]   the run from blank tape (py/tok.Sim) to STEPS (default 1e10): no round starts
                                     from a tape containing 1111; the states of the moving cursor; every meeting of
                                     the moving cursor with the next cursor (gap of at most 4 pairs, or a separator
                                     between them), with counts
       python3 scan.py arrive [ROUNDS]   every state of the moving cursor seen in `run` taken as a stalled cursor, a
                                     second cursor sent at it with both phases and both parities of the gap: does any
                                     of these collisions halt? (the moving cursor's states met on the way are added
                                     and tried in turn, until no new state appears)

Tapes are printed as in the README: runs of 01 as numbers, | = 00110, other cells in quotes; in `run` and `arrive`
runs longer than 4 pairs are written E (even) or O (odd).
"""
import collections, itertools, json, os, sys
from tok import Sim, SEP, norm, cells, round_

K = 4


def ab(n):
    return str(n) if n <= K else ('E' if n % 2 == 0 else 'O')


def segs(t):
    out = []; i = 0; buf = ''
    while i < len(t):
        if t[i:i + 4] == SEP:
            if buf: out.append('"' + buf + '"'); buf = ''
            out.append('|'); i += 4; continue
        x = t[i]
        if type(x) is list:
            if buf: out.append('"' + buf + '"'); buf = ''
            out.append(x[0])
        else:
            buf += str(x)
        i += 1
    if buf: out.append('"' + buf + '"')
    return out


def parse(s):
    t = []
    for w in s.split():
        if w == '|': t += SEP
        elif w[0] == '"': t += [int(c) for c in w.strip('"')]
        else: t.append([int(w)])
    return norm(t)


def lead_window(a, first_run=True):
    """The moving (first) cursor with its run on the left, back to the separator before it, and 4 tokens after."""
    g = segs(a)
    ci = next((i for i, x in enumerate(g) if type(x) is str and x[0] == '"'), None)
    if ci is None: return None
    j = ci
    while j > 0 and g[j - 1] != '|': j -= 1
    j = max(0, j - 1)
    if j == 0 and not first_run: return None
    k = min(len(g), ci + 5)
    w = ' '.join(ab(x) if type(x) is int else x for x in g[j:k])
    return ('^ ' + w) if j == 0 else w


def cmd_halts(L):
    def T(*parts):
        out = []
        for p in parts:
            if p == '|': out += SEP
            elif type(p) is int: out.append([p])
        return out
    pres = [[9], [9, '|', 9], [9, '|', 1], [1, '|', 1], [9, '|', 2], [2], [3], [1], [9, '|', 9, '|', 3], []]
    posts = [[9], ['|', 9], [1, '|', 9], [], ['|', 1, '|', 1], [2, '|', 9], [3]]
    n = 0; H = set()
    for pre in pres:
        for k in range(L + 1):
            for bits in itertools.product((0, 1), repeat=k):
                for post in posts:
                    toks = norm(T(*pre) + list(bits) + T(*post)); n += 1
                    if round_(toks)[0] is None: H.add(cells(toks))
    bad = [h for h in H if '001111' not in h and not h.startswith('000111')]
    print(f'{n} tapes, {len(H)} halt in their first round; without 001111 and not starting with 000111: {len(bad)}')
    return 1 if bad else 0


def cmd_run(N):
    s = Sim(); lead = collections.Counter(); meet = collections.Counter(); bad = []
    def log(sim, b, a):
        c = cells(a)
        if '1111' in c or c.startswith('000111'): bad.append(sim.steps)
        w = lead_window(a)
        if w: lead[w] += 1
        g = segs(a)
        cur = [i for i, x in enumerate(g) if type(x) is str and x[0] == '"']
        if len(cur) >= 2:
            i, j = cur[0], cur[1]
            mid = g[i + 1:j]
            if len(mid) <= 3 and all(x == '|' or (type(x) is int and x <= 4) for x in mid):
                meet[' '.join(str(x) for x in g[i:j + 1])] += 1
    s.log = log
    s.run(max_steps=N)
    print(f'{s.steps} steps, {s.rounds} rounds ({s.jumps} jumps): rounds starting from a tape with 1111: {len(bad)}')
    kinds = collections.Counter()
    for w, v in lead.items():
        for x in w.split():
            if x[0] == '"': kinds[x] += v; break
    print('moving cursor:', ', '.join(f'{k} ({v})' for k, v in kinds.most_common()), f'; {len(lead)} windows')
    print('meetings of the moving cursor with the next one (explicit rounds):')
    for k, v in sorted(meet.items(), key=lambda kv: -kv[1]): print(f'  {v:6d}  {k}')
    json.dump(dict(lead), open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lead_windows.json'), 'w'),
              indent=0, sort_keys=True)
    return 1 if bad else 0


REP = {'E': ['10', '12'], 'O': ['11', '13']}


def cmd_arrive(R):
    here = os.path.dirname(os.path.abspath(__file__))
    W = json.load(open(os.path.join(here, 'lead_windows.json')))
    seen = set(); Q = collections.deque()
    for w in W:
        t = [x for x in w.split() if x != '$']
        if t[0] != '|': continue
        w2 = ' '.join(t)
        if w2 not in seen: seen.add(w2); Q.append(w2)
    n = 0; halts = []
    while Q:
        p = Q.popleft(); toks = p.split(); slots = [i for i, t in enumerate(toks) if t in REP]
        for ch in itertools.product(*[REP[toks[i]] for i in slots]):
            tt = list(toks)
            for i, v in zip(slots, ch): tt[i] = v
            body = ' '.join(tt)
            for c in ('"0"', '"1"'):
                for z in (8, 9):
                    s = f'300 | 9 {c} {z} {body} | 9 | 9'
                    q = Sim(); q.toks = parse(s); n += 1; new = []
                    def log(sim, b, a):
                        w = lead_window(a, first_run=False)
                        if w and w not in seen: new.append(w)
                    q.log = log
                    q.run(max_rounds=R)
                    if q.halted:
                        halts.append(s); print('HALT', p, '::', s, flush=True)
                    for w in new:
                        if w not in seen: seen.add(w); Q.append(w)
    print(f'{len(seen)} stalled states, {n} collisions tried, {len(halts)} halt')
    return 0


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'halts'
    if cmd == 'halts': sys.exit(cmd_halts(int(sys.argv[2]) if len(sys.argv) > 2 else 12))
    if cmd == 'run': sys.exit(cmd_run(float(sys.argv[2]) if len(sys.argv) > 2 else 1e10))
    if cmd == 'arrive': sys.exit(cmd_arrive(int(sys.argv[2]) if len(sys.argv) > 2 else 300))
