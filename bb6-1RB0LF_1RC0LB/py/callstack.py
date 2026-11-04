"""The two-stack form (py/twostack.py) read as a recursive program, and the counter it conserves.

In the two-stack form the right stack R is a call stack and the left stack L is a data stack.  An entry v<n> of R is a
frame: a loop that still has to run n/2 times and then push v onto L.  Rule R1 is one turn of the cursor frame's loop:

    pop b, pop a (entries -1 below the bottom of L), push 0, and call the frame (a+2)<b>; when it returns, its value
    is on top of L.  A frame with gap 0 returns at once by pushing its value.

So, while every gap is even, one turn is the function

    I(L a b) = I^(b/2)(L 0) (a+2),

and the end entry runs I forever.  An odd gap runs down to -1, and rule R2 ends that frame differently: it takes 1
from the value of the frame below it (its caller) and is replaced by the frame (a'+2)<x-2>, where a' is the top of L
and x the frame's own value.

The counter.  Let Phi = (sum of L) + (sum of v + n over the frames of R other than the end).  R1 and R2 leave Phi
unchanged, and so does a frame returning, except at the two ends of the row:

* an R1 turn of the end frame adds 2 (this is the counter's tick: Phi/2 counts the turns of the end frame);
* an entry -1 taken from below the bottom of L, and an R2 whose caller is the end, change Phi by a small amount
  that `events` reports.

`lean/Counter.lean` proves the same statement for `mstep`, with Phi written in macro terms (`mphi` below; kernel
only).  This file only checks it on the run and reports how often each kind of step happens.

usage:
  python3 py/callstack.py check T     T steps of the two-stack form: how Phi changes, by kind of step (rule, at the
                                      bottom of L, at the end of the row)
  python3 py/callstack.py flips T     T steps: every R2, with the caller's value before and after and the number of
                                      times that caller has been flipped
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from macro import M0, mstep  # noqa: E402
from twostack import END, cursor, from_macro, zstep  # noqa: E402


def phi(z):
    """Sum of L plus v + n over the frames other than the end."""
    return sum(v + g for v, g in z if g is not END)


def mphi(c):
    """Phi of a macro configuration, as `BB6e.phi` in lean/Counter.lean."""
    if c[0] == "F":
        _, S, ws, _ = c
        return sum(S) + sum(m + g - 1 for m, g in ws)
    if c[0] == "B":
        _, S, h, ws, _ = c
        return sum(S) + h + sum(m + g - 1 for m, g in ws)
    return sum(c[1])


def start():
    c = M0
    while c[0] != "F":
        c = mstep(c)
    return from_macro(c)


def kind(z):
    """Which rule applies to z and whether it touches an end of the row: (rule, at_bottom, at_end)."""
    i = cursor(z)
    x, n = z[i]
    if n is END or n >= 1:
        return "R1", i < 2, n is END
    nxt = z[i + 1][1] if i + 1 < len(z) else END
    return "R2", i < 1, nxt is END


def check(T):
    """Returns a Counter of (rule, at_bottom, at_end, change of Phi)."""
    z, out = start(), Counter()
    for _ in range(T):
        r, bot, end = kind(z)
        z2 = zstep(z)
        if z2 is None:
            out["stuck"] += 1
            break
        out[(r, bot, end, phi(z2) - phi(z))] += 1
        z = z2
    return out


def flips(T):
    """Follow frames by identity; for every R2, record (caller value before, flips of the caller so far)."""
    z = start()
    ids = [object() for _ in z]
    nflip = Counter()
    out = Counter()
    for _ in range(T):
        i = cursor(z)
        x, n = z[i]
        pad = max(0, 2 - i)
        ids = [object() for _ in range(pad)] + ids
        zz = [[-1, 0]] * pad + [list(e) for e in z]
        i += pad
        if n is not END and n == -1:
            caller = ids[i + 1]
            y, m = zz[i + 1]
            out[(y, nflip[caller], m is END)] += 1
            nflip[caller] += 1
        z2 = zstep(z)
        # rebuild identities: R1 replaces entries i-2, i-1 by a fresh 0 and a fresh frame; R2 replaces i-1, i the same way
        # (the caller keeps its identity); the end-with-0 case replaces the caller by a fresh end
        if n is END or n >= 1:
            ids = ids[:i - 2] + [object(), object()] + ids[i:]
        elif zz[i + 1][1] is END and zz[i + 1][0] == 0:
            ids = ids[:i - 1] + [object(), object()]
        else:
            ids = ids[:i - 1] + [object(), object()] + ids[i + 1:]
        # norm drops leading [-1, 0] entries
        drop = len(ids) - len(z2)
        ids = ids[drop:]
        z = z2
    return out


def main(argv):
    if argv[0] == "check":
        for k, v in sorted(check(int(argv[1])).items(), key=str):
            print(" ", k, v)
    elif argv[0] == "flips":
        for k, v in sorted(flips(int(argv[1])).items(), key=str):
            print("  caller value, earlier flips, caller is end:", k, v)


if __name__ == "__main__":
    main(sys.argv[1:])
