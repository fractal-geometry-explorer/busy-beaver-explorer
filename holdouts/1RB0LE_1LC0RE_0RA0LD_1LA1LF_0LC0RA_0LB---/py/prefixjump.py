"""Jumping over eras when the chain has a defect: the chain law on the longest grammar prefix, any tape after it.

In the siblings with E1 = 0RE (1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC---, _1LA---, _1LE---) the full events often
leave the grammar of wordchain.py: somewhere along the chain a separator or a run of digits is out of phase by half
a digit (for example `a c W` where the grammar has `a d W`, a W followed by U digits with no `c` between them, or a
stock of `c z` tokens after the last W).  lean/Layers.lean proves the chain law with any tape B after the last
word (`encT B`), so the law still holds on the longest prefix of the chain that is in the grammar, for as long as no
carry leaves the last word of that prefix.  This script jumps with that: at each full event it parses the longest
prefix, jumps (by S, as in wordchain.py) to the last event before a carry would leave it, writes that tape with the
same tail, and runs cell by cell until the next full event with a prefix that can jump.  Spot checks: SPOT random
events of each jump, rebuilt from S with the same tail and run cell by cell for up to 5 events, each compared with
the law (prefix and tail).

usage (from the repository root):
  python3 .../py/prefixjump.py MACHINE JUMPS [SPOT]
"""
import random
import re
import sys

from wordchain import PR, Sim, add_n, bits, decode, jump, ptab, S_of, show, tape_left, tape_right

GP = re.compile(r'^((?:za|aa)+)d((?:(?:zc|cc)*c(?:az|aa)*ad)*)((?:zc|cc)*)c((?:az|aa)*)')
CELLS = {'z': '00', 'a': '10', 'c': '01', 'd': '11'}


def parse_prefix(tok):
    """(words of the longest grammar prefix, the cells after it) or None."""
    m = GP.match(tok)
    if not m:
        return None
    z, mid, wl, ul = m.groups()
    words = [bits(z, 'aa')]
    for w, u in PR.findall(mid):
        words += [bits(w, 'cc'), bits(u, 'aa')]
    words += [bits(wl, 'cc'), bits(ul, 'aa')]
    return words, ''.join(CELLS[c] for c in tok[m.end():])


def spot(tr, n, nw, w, tail, j, count, rng):
    W = [len(x) for x in w]
    m = len(w) - 1
    S = S_of(w)
    done = bad = 0
    for _ in range(count):
        e0 = rng.randrange(0, j)
        s = Sim(tr, 1 << 18)
        nn, nnw = add_n(n, nw, e0)
        s.load(tape_left(nn, nnw), tape_right(decode(S + e0 * 3 ** m, W)) + tail)
        for q in range(1, 6):
            if e0 + q > j:
                break
            e, _ = s.run_to_event(10 ** 6)
            if e in ('HALT', None):
                break
            p = parse_prefix(e[2])
            if p is None or p[0] != decode(S + (e0 + q) * 3 ** m, W) or p[1] != tail \
                    or (e[0], e[1]) != add_n(n, nw, e0 + q):
                bad += 1
                break
            done += 1
    return done, bad


def main():
    M, jumps = sys.argv[1], int(sys.argv[2])
    nspot = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    tr = ptab(M)
    rng = random.Random(1)
    s = Sim(tr)
    e, _ = s.run_to_event(10 ** 9)
    events = 1
    k = 0
    checked = [0, 0]
    kinds = {'in the grammar': 0, 'prefix and a defect': 0, 'no prefix': 0}
    end = 'no halt'
    while k < jumps:
        if e in ('HALT', None):
            end = 'HALT' if e == 'HALT' else 'stopped: no full event within 10^8 steps'
            break
        n, nw, tok = e
        p = parse_prefix(tok)
        if p is None:
            kinds['no prefix'] += 1
        else:
            w, tail = p
            kinds['prefix and a defect' if tail else 'in the grammar'] += 1
            j, w2 = jump(w)
            if j > 0:
                d, b = spot(tr, n, nw, w, tail, j, nspot, rng)
                checked[0] += d
                checked[1] += b
                n, nw = add_n(n, nw, j)
                events += j
                k += 1
                if k % 50 == 0:
                    print('jump %d: about 10^%d events, %s, tail %d cells' % (k, len(str(events)) - 1, show(n, nw, w2)[:90], len(tail)))
                    sys.stdout.flush()
                s.load(tape_left(n, nw), tape_right(w2) + tail)
        e, _ = s.run_to_event(10 ** 8)
        events += 1
    print('%s: %d jumps, about 10^%d events (so at least that many steps), %s; full events met: %s; '
          'spot checks: %d events, %d mismatches' % (M, k, len(str(events)) - 1, end, kinds, checked[0], checked[1]))


if __name__ == '__main__':
    main()
