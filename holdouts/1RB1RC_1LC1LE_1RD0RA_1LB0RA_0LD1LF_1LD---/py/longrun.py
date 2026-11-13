"""The run from blank tape on the counter list (counters.py), visit by visit with exact step counts.  Prints a line
whenever the first counter or the prefix changes, and every event that is not an ordinary visit when asked.

usage: python3 longrun.py VISITS [events]
"""
import sys, time
from collections import Counter
from counters import step, Unknown, LAST

def main():
    N = int(float(sys.argv[1])); show = len(sys.argv) > 2
    cs, ss, steps, v = [2, 2], ['0'], 28, 1          # visit 1 (step 28): (10)^2 0 (10)^2
    kinds = Counter(); t0 = time.time(); prev = None; slots = []
    try:
        while v < N:
            cs, ss, st, kind = step(cs, ss)
            steps += st; v += 1; kinds[kind] += 1
            head = (cs[0], ss[0] if ss else '', cs[1] if len(cs) > 1 else None)
            if kind in ('slot', 'merge'):
                slots.append((v, kind, LAST.get('x') if LAST.get('j', 0) > 1 else 10 ** 9, len(cs)))
            if head[:2] != prev or (show and kind != 'ordinary'):
                print('visit %d step %d (~10^%d) m=%d %s first: %s' % (v, steps, len(str(steps)) - 1, len(cs), kind,
                      ' '.join(str(c) + ' ' + s for c, s in zip(cs[:4], ss[:4]))), flush=True)
                prev = head[:2]
    except Unknown as u:
        print('OUTSIDE THE RULE at visit', v, u, cs, ss)
    print('visits %d steps %d (~10^%d) m=%d events %s  %.0fs' % (v, steps, len(str(steps)) - 1, len(cs), dict(kinds), time.time() - t0))
    if slots:
        print('zero-slot events: %d; smallest counter left of a slot (not the first counter): %d; x <= 3 at: %s' % (
            len(slots), min(x for _, _, x, _ in slots), [(a, k, x) for a, k, x, _ in slots if x <= 3][:20]))
    print('counters:', cs)
    print('separators:', ''.join(ss))

if __name__ == '__main__':
    main()
