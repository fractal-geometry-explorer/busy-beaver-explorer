"""Exhaustive search of the relaxed run of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---: every choice of cut or no cut.

At every round start whose tape is  m | ...  (the first run followed by a separator: the only way the real budget
runs out) the search tries both the plain round and the round with the first run removed.  Tapes are deduplicated
and those longer than MAXTAPE tokens dropped.  It reports halts, the words seen directly before a separator, double
separators `| |`, and a shortest history for each of `"110" |`, `"1110" |` and 1111.

usage: python3 relaxbfs.py ROUNDS [START [MAXTAPE]]     default START '4' (round 1 from blank tape), MAXTAPE 400
exit code 1 if a halt is found
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tok import round_, show, SEP, cells
from scan import parse, segs


def kinds(t):
    g = segs(t); out = set()
    for i, x in enumerate(g):
        if i + 1 < len(g) and g[i + 1] == '|' and (type(x) is str): out.add(x)
    if '1111' in cells(t): out.add('1111')
    return out


def key(t): return tuple(tuple(x) if type(x) is list else x for x in t)
def unkey(k): return [list(x) if type(x) is tuple else x for x in k]


def search(start, R, maxtape):
    front = {key(start)}; seen = set(front); par = {}; C = collections.Counter(); ex = {}
    for r in range(R):
        nxt = set()
        for k0 in front:
            t = unkey(k0)
            opts = [t]
            if t and type(t[0]) is list and len(t) > 1 and t[1:5] == SEP: opts.append(t[1:])
            for o in opts:
                n, _ = round_(o)
                if n is None: return 'HALT', r, show(o), C, ex, par
                if len(n) > maxtape: continue
                k = key(n)
                if k in seen: continue
                seen.add(k); nxt.add(k); par[k] = k0
                for w in kinds(n):
                    C[w] += 1; ex.setdefault(w, k)
        front = nxt
    return 'none', R, len(seen), C, ex, par


def history(k, par, n=12):
    ch = []
    while k in par and len(ch) < n: ch.append(k); k = par[k]
    return [show(unkey(c))[:140] for c in reversed(ch)]


if __name__ == '__main__':
    R = int(sys.argv[1]); start = parse(sys.argv[2] if len(sys.argv) > 2 else '4')
    res, r, info, C, ex, par = search(start, R, int(sys.argv[3]) if len(sys.argv) > 3 else 400)
    if res == 'HALT':
        print(f'HALT in round {r + 1} from {info}'); sys.exit(1)
    print(f'{R} rounds, {info} tapes, no halt')
    print('directly before a separator (and 1111):', dict(C))
    for w in ('"110"', '"1110"', '1111'):
        if w in ex:
            print(f'a history of {w}' + (' |' if w != '1111' else '') + ':')
            for x in history(ex[w], par): print('   ', x)
