"""Conserved quantities of the simple linear kind, for any machine.

A quantity  Q = a * (number of 1s) + b * (head position) + W[state]  (mod m)  is conserved if every non-halting
transition (s, y) -> (w, d, s') keeps it:  a * (w - y) + b * d + W[s'] - W[s] = 0 (mod m).  Each transition is
checked against the table, so a conserved Q holds along every run from every tape, by induction on the steps.

What it gives: from blank tape in state A, Q = W[A] at every step.  A halting configuration (state s reading y) can
then be reached only with  a * ones + b * pos = W[A] - W[s]  (mod m), which constrains the tapes a halt could come
from (in bb6-holdout, a mod-3 count of the 1s with a state weight ruled out some halting candidates).

usage: python3 -m bbtools.invariants MACHINE [MAX_MODULUS]
"""
import itertools
import sys

from .machine import Machine, STATES


def conserved(m, mod, use_pos=True):
    """All (a, b, W) mod `mod` with (a, b) != (0, 0) and W[A] = 0 (W is fixed up to a constant) that are conserved.
    Without use_pos, b = 0."""
    trans = [(s, y, t) for s in range(m.n) for y in (0, 1) if (t := m.table[s][y]) is not None]
    out = []
    for a in range(mod):
        for b in (range(mod) if use_pos else [0]):
            if a == 0 and b == 0:
                continue
            # W is determined along transitions from W[A] = 0: propagate, then check every transition.
            W = [None] * m.n
            W[0] = 0
            changed, ok = True, True
            while changed and ok:
                changed = False
                for s, y, (w, d, s2) in trans:
                    if W[s] is not None:
                        need = (W[s] - a * (w - y) - b * d) % mod
                        if W[s2] is None:
                            W[s2] = need
                            changed = True
                        elif W[s2] != need:
                            ok = False
                            break
            if not ok:
                continue
            free = [i for i in range(m.n) if W[i] is None]
            for vals in itertools.product(range(mod), repeat=len(free)):
                W2 = list(W)
                for i, v in zip(free, vals):
                    W2[i] = v
                if all((a * (w - y) + b * d + W2[s2] - W2[s]) % mod == 0 for s, y, (w, d, s2) in trans):
                    out.append((a, b, tuple(W2)))
    return out


def primitive(sols, mod):
    """Drop solutions that are a multiple of another by a unit or that live in a proper divisor's modulus."""
    keep = []
    seen = set()
    for a, b, W in sols:
        key = None
        g = 0
        for x in (a, b) + W:
            g = _gcd(g, x)
        if _gcd(g, mod) != 1:
            continue
        for u in range(1, mod):
            if _gcd(u, mod) == 1:
                k = (a * u % mod, b * u % mod, tuple(x * u % mod for x in W))
                key = k if key is None or k < key else key
        if key not in seen:
            seen.add(key)
            keep.append((a, b, W))
    return keep


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def describe(a, b, W, mod):
    terms = []
    if a:
        terms.append("ones" if a == 1 else f"{a}*ones")
    if b:
        terms.append("pos" if b == 1 else f"{b}*pos")
    ws = ", ".join(f"{STATES[i]}:{w}" for i, w in enumerate(W))
    return f"{' + '.join(terms)} + W[state]  (mod {mod}),  W = {{{ws}}}"


def halting_constraints(m, a, b, W, mod):
    """For each halting transition (s, y): the value a*ones + b*pos must have when it is reached from blank tape."""
    return [(f"{STATES[s]}{y}", (W[0] - W[s]) % mod) for s in range(m.n) for y in (0, 1) if m.table[s][y] is None]


def main(argv):
    m = Machine.parse(argv[0])
    top = int(argv[1]) if len(argv) > 1 else 12
    found = False
    for mod in range(2, top + 1):
        for a, b, W in primitive(conserved(m, mod), mod):
            found = True
            hc = ", ".join(f"{h}: {v}" for h, v in halting_constraints(m, a, b, W, mod))
            print(f"{describe(a, b, W, mod)};  at a halt from blank tape a*ones + b*pos = {hc}")
    if not found:
        print(f"no conserved quantity a*ones + b*pos + W[state] modulo 2..{top}")


if __name__ == "__main__":
    main(sys.argv[1:])
