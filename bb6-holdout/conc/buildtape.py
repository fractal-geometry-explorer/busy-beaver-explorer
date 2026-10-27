"""Tape for a mark configuration at a round start: leftmost 1 at cell 0, gap at 1..3 with the head on cell 3 in state E,
stripes alternating, marks as runs (W = 00, G = 000, M = 11, B = 111), last 1 at cell W - 1."""
import sys
def build(marks, Wd):
    runs = {}
    for t, p in marks:
        ln = {'W': 2, 'G': 3, 'M': 2, 'B': 3}[t]; sym = 0 if t in 'WG' else 1
        for i in range(p, p + ln): runs[i] = (sym, i > p)
    cells = []
    for i in range(Wd):
        if i == 0: v = 1
        elif i in runs and runs[i][1]: v = cells[-1]
        else: v = 1 - cells[-1]
        if i in runs: assert v == runs[i][0], f"parity clash at cell {i} for mark {runs[i]}"
        cells.append(v)
    assert cells[-1] == 1, "last cell must be the last 1"
    return ''.join(map(str, cells))
if __name__ == '__main__':
    a, b, c, E = map(int, sys.argv[1:5])
    t = build([('G', 1), ('W', a), ('W', b), ('W', c)], E)
    open(sys.argv[5], 'w').write(t)
    print(len(t), t[:24], '...', t[-24:])
