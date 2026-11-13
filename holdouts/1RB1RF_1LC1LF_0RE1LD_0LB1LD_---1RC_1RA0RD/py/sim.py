"""sim.py: run a machine from a given tape string (cells, head marked 'S>' before its cell) until a predicate."""
import re
def parse_m(m):
    t = {}
    for i, part in enumerate(m.split('_')):
        for y in (0, 1):
            tr = part[3*y:3*y+3]
            t[(i, y)] = None if tr[2] in '-Z' else (int(tr[0]), 1 if tr[1] == 'R' else -1, ord(tr[2]) - 65)
    return t
def expand(s):
    """'0 0 (10)^3 1^4 B> 0' style -> (dict tape, head, state)"""
    cells, head, st = [], None, None
    for tok in s.split():
        if tok.endswith('>'): head = len(cells); st = ord(tok[0]) - 65; continue
        m = re.match(r'^\(?([01]+)\)?(?:\^(\d+))?$', tok)
        cells += [int(c) for c in m.group(1)] * int(m.group(2) or 1)
    return {i: c for i, c in enumerate(cells)}, head, st
def run(m, s, maxsteps, stop=None):
    t = parse_m(m) if isinstance(m, str) else m
    tape, h, st = expand(s)
    for k in range(maxsteps):
        y = tape.get(h, 0)
        tr = t[(st, y)]
        if tr is None: return ('halt', k + 1, tape, h, st)
        tape[h] = tr[0]; h += tr[1]; st = tr[2]
        if stop and stop(tape, h, st, k + 1): return ('stop', k + 1, tape, h, st)
    return ('run', maxsteps, tape, h, st)
def show(tape, h, st):
    lo, hi = min(min(tape), h), max(max(tape), h)
    return ''.join((chr(65+st)+'>' if i == h else '') + str(tape.get(i, 0)) for i in range(lo, hi + 1))
