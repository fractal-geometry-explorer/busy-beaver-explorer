"""The countdown map at the resets.  A reset is a left record whose first block is (0, o) with a long block Y after
it; the next record starts the new phase with countdown Y + 1.  Writing X for that Y, the next reset has

    X' = floor(3X/2) + 1   (X even)        X' = floor(3X/2) + 3 = (3X + 5)/2   (X odd)

This script lists the resets of a run and checks that rule at each.  The run is either a recp file (direct
simulation) or the block macro machine run here for N records, from this machine's start or from the twin's
(1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, this table started in state D; record 6 at step 157).

usage: python3 reset_map.py FILE            (recp output)
       python3 reset_map.py own|twin N      (macro run)"""
import sys


def f(X):
    return 3 * X // 2 + (1 if X % 2 == 0 else 3)


def records_file(fn):
    from check_macro import parse
    for line in open(fn):
        if '|' in line:
            st, rn, c, bl = parse(line)
            yield rn, st, bl


def records_macro(which, N):
    from blockmm import macro_step
    if which == 'own':
        cur, rn, steps = ((), 0, [(0, 1), (1, 0)]), 1, 4
    else:
        cur, rn, steps = ((), 0, [(3, 0), (0, 0), (1, 1), (1, 1), (1, 1), (1, 0)]), 6, 157
    while rn < N:
        yield rn, steps, cur[2]
        r = macro_step(*cur)
        if r[0] is None:
            print('HALT at record', rn, 'step', steps); return
        cur, s, _ = r; steps += s; rn += 1


def main():
    recs = records_macro(sys.argv[1], int(float(sys.argv[2]))) if sys.argv[1] in ('own', 'twin') else records_file(sys.argv[1])
    Xs = []
    prev = None
    for rn, st, bl in recs:
        if prev and len(bl) > 2 and len(prev) > 1 and prev[0] == (0, 0) and bl[0][0] > prev[0][0] + 5:
            Xs.append((prev[1][0], rn, st))
        prev = bl
    bad = 0
    for (X, rn, st), (X2, _, _) in zip(Xs, Xs[1:]):
        ok = f(X) == X2
        bad += not ok
        print('reset at record %d, step %d: X = %d -> next %d (rule: %d)%s' % (rn, st, X, X2, f(X), '' if ok else '  MISMATCH'))
    if Xs:
        print('last reset at record %d, step %d: X = %d' % (Xs[-1][1], Xs[-1][2], Xs[-1][0]))
    print('%d resets, %d transitions, %d mismatches' % (len(Xs), max(len(Xs) - 1, 0), bad))


if __name__ == '__main__':
    main()
