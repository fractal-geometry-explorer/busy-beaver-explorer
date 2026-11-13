"""Classify consecutive events of `c/family events` output against the round rule.

An event lists the merged suffix [n1, ..., nk] (n1 = b1 + 1).  Between consecutive events the model allows:
  same / same*  : one round on the whole suffix, blocks change by eff(k) (same* = with the extra +2 on the first
                  block, phase 1 -> 2);
  upN / up*N    : the same round, but N new (shallower) blocks became visible on the left;
  down          : the first block was used up and the head now starts one block further right;
  X             : anything else (left-end events, spawning of a new last block, merges after a block runs out,
                  F-events).  With a second argument these are printed.

usage: ../c/family events MACHINE STEPS > ev.txt; python3 check_rounds.py ev.txt [show]
"""
import sys


def eff(m):
    if m == 1:
        return [2]
    return [-4] + [-18 * 5 ** i for i in range(m - 2)] + [12 * 5 ** (m - 2)]


def classify(a, b):
    if len(b) == len(a) - 1 and b == a[1:]:
        return "down"
    if len(b) >= len(a):
        d = [y - x for x, y in zip(a, b[len(b) - len(a):])]
        e = eff(len(a))
        up = "" if len(b) == len(a) else str(len(b) - len(a))
        if d == e:
            return "up" + up if up else "same"
        e[0] += 2
        if d == e:
            return "up*" + up if up else "same*"
    return "X"


def main(path, show=False):
    ev = []
    for line in open(path):
        f = line.split()
        if f[0] == "HALT":
            break
        L = list(map(int, f[2:]))
        if L == [0]:
            continue  # the head turning at the right end of the tape, not an event
        L[0] -= 1
        ev.append((int(f[0]), int(f[1]), L))
    cnt = {}
    for (t0, p0, a), (t1, p1, b) in zip(ev, ev[1:]):
        k = classify(a, b)
        if k == "X" and show:
            print(t0, p0, a, "->", t1, p1, b)
        cnt[k] = cnt.get(k, 0) + 1
    print(len(ev), "events", cnt)


if __name__ == "__main__":
    main(sys.argv[1], len(sys.argv) > 2)
