"""farrun MACHINE MAXSTEPS OUT.jsonl [KEEP]: run rsim, record the tape as run lengths at every visit of the right end."""
import sys, json, time
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import RSim, Halt

def runs_of_ones(items):
    """items: list of (word, count) in tape order -> list of [tuple of run lengths, count] ; zero gaps are not recorded"""
    out = []
    cur = 0
    def emit(vals, c):
        if not vals or c == 0: return
        vals = tuple(vals)
        if len(set(vals)) == 1:
            v = vals[0]; c *= len(vals); vals = (v,)
        if out and out[-1][0] == vals: out[-1][1] += c
        else: out.append([vals, c])
    for w, c in items:
        if '0' not in w:
            cur += len(w) * c; continue
        parts = w.split('0')
        a = len(parts[0]); b = len(parts[-1])
        inner = [len(p) for p in parts[1:-1] if p]
        if cur + a: emit([cur + a], 1)
        emit(inner, 1)
        if c > 1:
            per = ([a + b] if a + b else []) + inner
            emit(per, c - 1)
        cur = b
    if cur: emit([cur], 1)
    return out

def fmt(rl):
    o = []
    for vals, c in rl:
        t = ' '.join(map(str, vals))
        if len(vals) > 1: t = '[' + t + ']'
        o.append(t if c == 1 else f'{t}x{c}')
    return ' '.join(o)

if __name__ == '__main__':
    m = sys.argv[1]; mx = int(float(sys.argv[2])); out = open(sys.argv[3], 'a')
    sim = RSim(m); sim.KEEP = int(sys.argv[4]) if len(sys.argv) > 4 else 32
    t0 = time.time(); last = [0]
    def right(s):
        if s.steps - last[0] < 100: return
        last[0] = s.steps
        items = [(it[0], it[1]) for it in s.L] + [(''.join(map(str, s.buf)), 1)]
        rl = runs_of_ones(items)
        out.write(json.dumps({'steps': s.steps, 'state': 'ABCDEF'[s.s], 'list': fmt(rl), 'sec': round(time.time() - t0, 1), 'jumps': s.njumps, 'samples': s.nsamp}) + '\n'); out.flush()
    sim.on_right_end = right
    try:
        sim.run(mx); print('running', sim.steps)
    except Halt:
        print('HALT', sim.steps); out.write(json.dumps({'halt': sim.steps}) + '\n')
