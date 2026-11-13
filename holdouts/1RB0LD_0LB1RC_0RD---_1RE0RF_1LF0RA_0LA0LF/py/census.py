"""Census of the visits, with the exact visit simulator: how many are plain counter increments (the increment
`bump` of lean/Counter.lean is defined), what the others meet first, how many digits are born at the left end and
how many of those births follow an overflow (every digit d before the visit).

usage: python3 census.py MACHINE STATE NEARSTATE STEPS"""
import sys
from vsim import VSim, bootstrap

DIG = {'0011': 'a', '0011001': 'b', '001101': 'c', '00111': 'd', '00101': 'e', '0': 'z', '001': 'f'}


def first_odd(items):
    """None for a plain visit, else what the head meets that the counter rule does not cover."""
    if items[0] != '00':
        return 'left end ' + items[0]
    i = 2
    while i < len(items):
        it = items[i]
        if it not in DIG or DIG[it] in 'zf':
            return 'word ' + DIG.get(it, it)
        x = DIG[it]
        g = items[i + 1][1] if i + 1 < len(items) and isinstance(items[i + 1], tuple) else 0
        if x != 'd':
            return None if g >= 1 else 'empty gap'
        i += 2
    return 'end'


def main():
    M, Q, A, N = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4])
    cells, n = bootstrap(M, Q)
    v = VSim(M, Q, cells, n, A)
    cnt, plain, tot, births, overflows = {}, 0, 0, 0, 0
    while v.steps < N:
        before = v.items
        k = first_odd(before)
        tot += 1
        if k is None:
            plain += 1
        else:
            cnt[k] = cnt.get(k, 0) + 1
        if v.visit() != 'ok':
            print('HALT at visit', v.visits)
            break
        if v.items[0] != '00':
            births += 1
            if all(DIG.get(it) == 'd' for it in before[1:-1] if isinstance(it, str)):
                overflows += 1
    print(f'steps {v.steps} visits {tot} plain {plain} ({100 * plain / tot:.3f}%) births {births} '
          f'after overflow {overflows} near misses {len(v.events)}')
    for k, c in sorted(cnt.items(), key=lambda x: -x[1])[:40]:
        print(c, k)


if __name__ == '__main__':
    main()
