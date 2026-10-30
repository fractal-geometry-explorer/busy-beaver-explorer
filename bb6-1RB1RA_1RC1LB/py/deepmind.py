"""Compare this folder's maps with the ones in google-deepmind/cryptids (BusyBeaver/BB6/Accelerations/
M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean, `next` and `highLevelNext`).

usage: python3 deepmind.py [MACRO_STEPS]

DeepMind's state C(a, L, R) is state C on the 0 in  0 1^(L_2+1) 0 1^(L_1+1) 0 1^(a+1) C>0 1^(R_1) 00 1^(R_2+1) 00 ...
This folder's X(ls, n, cs) of lean/Macro.lean is  ... 1^(l_1) 0 A> 1^n 000 1^(c_1) 00 1^(c_2) ...; from it A crosses
1^n and A0, B0 write two more 1s, so n + 2 steps later the machine is at C(n + 1, ls - 1, (c_1, c_2 - 1, ...)).

The script checks two things:
  base   both runs from blank tape, translated this way, pass through the same configurations in the same order, but
         cut at different moments: each map has configurations the other skips (DeepMind's even-a rule stops after
         one block of a carry, the macro step here runs the carry over all the 2s and the sweep back right);
  high   DeepMind's high-level map (the section R = []) is the event map of waves.py `step`: the event (b_1, ..., b_n),
         A on the blank right of the tape, is C(b_n + 1, (b_(n-1) - 1, ..., b_1 - 1), []) two steps later, and the
         two orbits agree event for event.  The super step of lean/Wave.lean is every fourth event.
"""
import sys

import macro
import waves


def bump(L):
    return [L[0] + 1] + L[1:] if L else [0]


def transfer(L, R):
    for d in R:
        L = [d] + bump(L)
    return (L[0] + 1, L[1:], []) if L else (0, [], [])


def dm_next(s):
    """DeepMind's `next`; None is the halt."""
    a, L, R = s
    r, Rt = (R[0], R[1:]) if R else (0, [])
    if a == 0:
        if not L:
            return None
        if L[0] == 0:
            return transfer([r + 2, 0] + L[1:], Rt)
        return transfer([L[0] - 1] + L[1:], [r + 2] + Rt)
    k = (a - 1) // 2
    if (a - 1) % 2 == 0:
        for _ in range(k):
            L = bump(L)
        return transfer(L, [r + k + 2] + Rt)
    if not L:
        return (k, [], [0, r + k] + Rt)
    return (L[0] + k + 1, L[1:], [0, r + k] + Rt)


def dm_high_next(s):
    """DeepMind's `highLevelNext`: `next` until R is empty again."""
    s = dm_next(s)
    while s is not None and s[2]:
        s = dm_next(s)
    return s


def from_x(ls, n, cs):
    return (n + 1, [l - 1 for l in ls], [cs[0]] + [c - 1 for c in cs[1:]] if cs else [])


def from_event(b):
    return (b[-1] + 1, [x - 1 for x in reversed(b[:-1])], [])


def main(argv):
    k = int(argv[0]) if argv else 100000
    ours = [from_x(*x[2:]) for x in macro.run(k)]
    dm, s = [], (3, [0], [])
    while len(dm) < 3 * len(ours) and s is not None:
        dm.append(s)
        s = dm_next(s)
    where = {}
    for i, d in enumerate(dm):
        where.setdefault(repr(d), i)
    idx = [where.get(repr(o)) for o in ours]
    hit = [i for i in idx if i is not None]
    order = all(x < y for x, y in zip(hit, hit[1:]))
    last = hit[-1] + 1
    print(f"base: {len(ours)} macro configurations here, {last} DeepMind states over the same stretch; "
          f"{len(hit)} shared, in the same order: {order}")
    b, s, same, n = list(waves.START), from_event(waves.START), 0, 20000
    for _ in range(n):
        same += from_event(b) == s
        b, _ = waves.step(b)
        s = dm_high_next(s)
    print(f"high: {same} of {n} events equal to DeepMind's high-level states")
    return 0 if order and same == n else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
