"""The counter: read every sweep end of the run as (b0, [(phase, block), ...]) and check the two regular rules.

A tape between sweeps is 1 (0010)^b0 m1 (0010)^b1 ... mk (0010)^bk 000 with each marker mi one of
    phase 0: 1    phase 0': 0    phase 1: 0011    phase 2: 011    phase 3: 11    phase 4: 00111
(a stretch of cells between blocks is split into markers with as few markers as possible; blocks between markers can
be empty).  One sweep finds the last marker j not in phase 4 and

  regular sweep (turn): markers j+1..k go from phase 4 to 0, each block after them grows by 1; marker j goes up one
     phase (0' -> 1), and the blocks around it change by  phase 0: -2 / +2,  0': -1 / +1,  1, 2: 0 / +1,
     3: -1 / +1  (the block before it / after it).  It needs the block before marker j to be at least 2 (phase 0) or
     1 (phases 0' and 3).
  overflow (all markers in phase 4): b0 grows by 2, every marker becomes phase 0', the blocks b1..b(k-1) grow by 1,
     and a new marker in phase 1 with an empty block appears at the end.

Every other sweep is a *merge*: a turn whose block condition fails (the marker runs into the one before it).

usage: python3 model.py MACHINE [STEPS [EXAMPLES]]   (default 1e9 steps)
"""
import sys
from collections import Counter

from sim import rl

MARKERS = {'1': '0', '0': "0'", '0011': '1', '011': '2', '11': '3', '00111': '4'}
NEXT = {'0': '1', "0'": '1', '1': '2', '2': '3', '3': '4'}
DELTA = {'0': (-2, 2), "0'": (-1, 1), '1': (0, 1), '2': (0, 1), '3': (-1, 1)}
NEED = {'0': 2, "0'": 1, '1': 0, '2': 0, '3': 1}


def split(s):
    """Fewest markers spelling s, or None."""
    best = {0: []}
    for i in range(len(s)):
        if i not in best:
            continue
        for w in MARKERS:
            if s.startswith(w, i):
                j = i + len(w)
                if j not in best or len(best[j]) > len(best[i]) + 1:
                    best[j] = best[i] + [MARKERS[w]]
    return best.get(len(s))


def parse(line):
    """'S steps tape' -> (steps, b0, [(phase, block)]) or (steps, None, None)."""
    p = line.split()
    steps, toks = int(p[1]), p[2:]
    if not toks or not toks[0].startswith('1'):
        return steps, None, None
    toks = ([toks[0][1:]] if len(toks[0]) > 1 else []) + toks[1:]
    blocks, phases, lastm = [], [], True
    blocks.append(0)
    for t in toks:
        if t[0] == 'B':
            if not lastm:
                return steps, None, None
            blocks[-1] = int(t[1:])
            lastm = False
        else:
            ms = split(t)
            if ms is None:
                return steps, None, None
            for x in ms:
                phases.append(x)
                blocks.append(0)
            lastm = True
    return steps, blocks[0], list(zip(phases, blocks[1:]))


def regular(b0, ms):
    """The next sweep end by the two regular rules, or (kind, None) when the sweep is a merge."""
    ph = [p for p, _ in ms]
    bl = [b0] + [b for _, b in ms]
    j = len(ph) - 1
    while j >= 0 and ph[j] == '4':
        j -= 1
    if j < 0:
        if not ph:
            return 'merge', ('no marker', bl[0], 'left end')
        bl2 = [bl[0] + 2] + [b + 1 for b in bl[1:-1]] + [bl[-1], 0]
        return 'overflow', (bl2[0], list(zip(["0'"] * len(ph) + ['1'], bl2[1:])))
    p = ph[j]
    if bl[j] < NEED[p]:
        return 'merge', (p, bl[j], ph[j - 1] if j > 0 else 'left end')
    for i in range(j + 1, len(ph)):
        ph[i] = '0'
        bl[i + 1] += 1
    d0, d1 = DELTA[p]
    ph[j] = NEXT[p]
    bl[j] += d0
    bl[j + 1] += d1
    return 'turn', (bl[0], list(zip(ph, bl[1:])))


WORD = {v: k for k, v in MARKERS.items()}


def canonical(b0, ms):
    """Write (b0, markers) as a tape and read it back: some spellings coincide (0' with an empty block before
    phase 2 is the word 0011, phase 1), and the reading with the fewest markers is the one used."""
    toks = ['1' + ('' if b0 else '')]
    if b0:
        toks.append(f'B{b0}')
    for p, b in ms:
        if toks[-1][0] != 'B':
            toks[-1] += WORD[p]
        else:
            toks.append(WORD[p])
        if b:
            toks.append(f'B{b}')
    return parse('S 0 ' + ' '.join(toks))[1:]


def check(M, steps, examples=0, out=print):
    lines = rl(M, steps)
    prev, kinds, merges, fe = None, Counter(), Counter(), 0
    shown = 0
    for line in lines:
        if line.startswith('F'):
            fe += 1
            continue
        if not line.startswith('S'):
            continue
        st, b0, ms = parse(line)
        assert b0 is not None, line
        if prev is not None:
            kind, res = regular(*prev)
            if kind == 'merge':
                merges[res] += 1
                kinds['merge'] += 1
                if shown < examples:
                    out(f'  merge at step {st}: {prev[0]} {prev[1]} -> {b0} {ms}')
                    shown += 1
            else:
                assert canonical(*res) == (b0, ms), (st, kind, prev, res, (b0, ms))
                kinds[kind] += 1
        prev = (b0, ms)
    out(f'{M}: {sum(kinds.values())} sweeps to {float(steps):.0e} steps: {kinds["turn"]} regular turns, '
        f'{kinds["overflow"]} overflows (all agree with the rules), {kinds["merge"]} merges; {fe} entries into F')
    out('  merges by (turning phase, block before it, marker before that): ' +
        ', '.join(f'{k}: {v}' for k, v in sorted(merges.items(), key=lambda kv: -kv[1])))
    return kinds, merges, fe


if __name__ == '__main__':
    check(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else '1e9', int(sys.argv[3]) if len(sys.argv) > 3 else 0)
