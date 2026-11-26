"""Closed sets of residue classes for the digit map of 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA
(lean/DigitMap.lean): f(10a + d) = 31a + K[d // 2].

For each modulus M the script closes the class of 22 under f, a class standing for all its members (the members
c + M*t, t = 1..10, take every branch).  The closure is every class unless 31 divides M; for M = 31*q it is the
classes that are K[r] mod 31 for some r (and the start), which only records the r of the step before: K is
one-to-one mod 31.  Since x mod 10 is free in every class mod 31^j, no closed set restricts the next r, in line
with `rlist_onto` of lean/DigitClosed.lean.  The halt of this machine is not a value of the orbit either: it
depends on where a 772-digit budget runs out, so a closed set of residues could not decide it in any case.

usage (from the repository root): python3 holdouts/1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA/py/residues.py [MAX]
"""
import sys

K = (15, 27, 47, 35, 36)


def f(x):
    return 31 * (x // 10) + K[x % 10 // 2]


def closure(M):
    seen, todo = {22 % M}, [22 % M]
    while todo:
        c = todo.pop()
        for t in range(1, 11):
            d = f(c + M * t) % M
            if d not in seen:
                seen.add(d)
                todo.append(d)
    return seen


if __name__ == '__main__':
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    proper = [M for M in range(2, top + 1) if len(closure(M)) < M]
    print(f'M = 2..{top}: the closure of the class of 22 is every class except for {len(proper)} moduli, '
          f'all multiples of 31: {all(M % 31 == 0 for M in proper)}')
    c = closure(31)
    print('mod 31 the closure is', sorted(c), '= K mod 31 and the start:', c == {k % 31 for k in K} | {22})
    free = all({x % 10 // 2 for x in range(c0, c0 + 961 * 10, 961)} == set(range(5)) for c0 in closure(961))
    print('every class of the closure mod 961 has members with each r = 0..4:', free)
