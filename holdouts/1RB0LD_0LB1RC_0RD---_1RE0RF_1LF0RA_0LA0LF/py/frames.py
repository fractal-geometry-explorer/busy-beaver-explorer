"""Data for the explainer's two widgets, from the exact visit-level simulator `vsim.py`:
  tracks: every STEP-th sample configuration of the first VMAX visits, as (tape width, [(distance of the token's
          right end from the right end of the tape, token class)]);
  frames: NF consecutive sample configurations from visit V0 on, as token lists.
usage: python3 frames.py MACHINE STATE OUT.json [VMAX STEP [V0:NF ...]]"""
import json, sys
from vsim import VSim, bootstrap
DIG = {'0011': 'a', '0011001': 'b', '001101': 'c', '00111': 'd', '00101': 'e', '0': 'z', '001': 'f'}
def canon(items):
    """A digit just born at the left end reads 0 W 1 ... to the greedy tokenizer: 0 0 0 0 1 1 = 0 0 a."""
    if len(items) > 2 and items[0] == '0' and items[1] == ('W', 1) and isinstance(items[2], str) and items[2][0] == '1':
        rest = items[2][1:]
        return ['00', ('W', 0), '0011' + rest] + list(items[3:])
    return items


def toks(items):
    items = canon(items)
    out = []
    for it in items:
        if isinstance(it, tuple):
            out.append(it[1])
        else:
            out.append(DIG.get(it, '[' + it + ']'))
    return out
def main():
    M, Q, OUT = sys.argv[1:4]
    VMAX, STEP = (int(x) for x in sys.argv[4:6]) if len(sys.argv) > 4 else (30000, 12)
    wins = [tuple(int(y) for y in w.split(':')) for w in sys.argv[6:]]   # V0:NF windows
    cells, n = bootstrap(M, Q)
    v = VSim(M, Q, cells, n)
    tracks = []
    frames = [[] for _ in wins]
    while v.visits < max([VMAX] + [a + b for a, b in wins]):
        if v.visits % STEP == 0 and v.visits < VMAX:
            width = sum(4 * it[1] if isinstance(it, tuple) else len(it) for it in v.items)
            pos, row = width, []
            for k, it in enumerate(v.items):
                ln = 4 * it[1] if isinstance(it, tuple) else len(it)
                if isinstance(it, str) and k > 0 and k < len(v.items) - 1:
                    row.append([pos - ln, DIG.get(it, 'x')])
                pos -= ln
            tracks.append([v.visits, v.steps, width, row])
        for k, (V0, NF) in enumerate(wins):
            if V0 <= v.visits < V0 + NF:
                frames[k].append([v.visits, v.steps, toks(v.items)])
        if v.visit() != 'ok':
            break
    json.dump({'machine': M, 'tracks': tracks, 'frames': frames}, open(OUT, 'w'), separators=(',', ':'))
if __name__ == '__main__':
    main()
