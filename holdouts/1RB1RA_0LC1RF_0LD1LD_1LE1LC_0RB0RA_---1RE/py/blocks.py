"""The block-list rule of 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE, and its checks against the machine itself.

At each visit of the right end in state B (`B> 0^inf`) the tape is a list of blocks of 1s separated by single 0s,
`b = [b0, b1, ..., z]` front first (a block may be 0: two 0s in a row; leading zeros are dropped).  `step(b)` is the
next visit (raises Halt where the machine halts):

* z odd: the target is z;  z even: the target e is the last even block before z (all blocks between e and z odd);
  no even block: the sweep reaches the left end in state C and the machine halts (F reads 0);
* every odd block between e and z must have length >= 3, or the machine halts (F reads 0 on the way back);
* x = the block left of e (empty if e is the front block):
    x >= 1: x loses 1, and e gains 4 (z gains 2 if e is z);
    x  = 0: x becomes 2, and e gains 1 (z loses 1 if e is z); e = 0 here halts;
* if e is not z: z loses 2; if z was 0, it disappears and the block before it loses 2 instead.

`sweep(ns)` is the same rule on the nearest-first list, written exactly as the Lean definition in lean/Macro.lean
(where theorem `visit` proves it for every list).

usage:
  python3 blocks.py random N        compare step() with the machine on N random block lists (values 0..9)
  python3 blocks.py run VISITS      compare step() with the machine from blank tape at every visit
  python3 blocks.py lean N          compare step() with the Lean-mirror sweep() on N random lists
"""
import random
import sys

M = "1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE"


class Halt(Exception):
    pass


def target(b):
    m = len(b)
    if b[-1] % 2:
        return m - 1
    e = m - 2
    while e >= 0 and b[e] % 2:
        e -= 1
    return e


def step(b):
    b = list(b)
    m = len(b)
    e = target(b)
    if e < 0:
        raise Halt('left end')
    if e < m - 1:
        for i in range(e + 1, m - 1):
            if b[i] < 3:
                raise Halt('odd block %d < 3 on the way back' % i)
    if e == 0 or b[e - 1] == 0:
        if b[e] == 0:
            raise Halt('empty target after an empty block')
        if e == 0:
            b.insert(0, 2)
            e += 1
        else:
            b[e - 1] = 2
        gain = -3
    else:
        b[e - 1] -= 1
        gain = 0
    m = len(b)
    if e == m - 1:
        b[e] += 2 + gain
    else:
        b[e] += 4 + gain
        if b[-1] == 0:
            b.pop()
            if b[-1] < 3:
                raise Halt('last block < 3 after an empty z')
        b[-1] -= 2
    while b and b[0] == 0:
        b.pop(0)
    return b


# --- the Lean definition, nearest block first (lean/Macro.lean) ---
def casc(ls, os):
    for i, n in enumerate(os):
        if n >= 3:
            ls = [n - 3, ls[0] + 3] + ls[1:]
        elif n == 2 and i == len(os) - 1:
            return [0, ls[0] + 3] + ls[1:]
        else:
            return None
    return [ls[0] + 1] + ls[1:]


def fill(ns, e, os):
    if ns and ns[0] >= 1:
        return casc([e + 1, ns[0] - 1] + ns[1:], os)
    rest = ns[1:]
    if e == 0:
        return None
    if e == 1:
        return [0, 2] + rest if not os else None
    return casc([e - 2, 2] + rest, os)


def scanC(ns, os):
    while ns:
        n, ns = ns[0], ns[1:]
        if n % 2 == 0:
            return fill(ns, n, os)
        os = [n] + os
    return None


def sweep(ns):
    if not ns:
        return None
    z, ns = ns[0], ns[1:]
    if z == 0:
        return scanC(ns, [])
    if z % 2 == 0:
        return scanC(ns, [z])
    return fill(ns, z, [])


# --- the machine, run-length coded (runs of one symbol crossed at once when the head stays in its state or
# alternates between two states that both keep the symbol) ---
def parse(Mt):
    T = {}
    for i, g in enumerate(Mt.split('_')):
        for r in range(2):
            t = g[3 * r:3 * r + 3]
            T[(i, r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


class RL:
    def __init__(s, Mt=M):
        s.T = parse(Mt); s.L = []; s.R = []; s.st = 0; s.steps = 0; s.cur = 0

    def pop(s, side):
        if not side:
            return 0
        x = side[-1]; x[1] -= 1
        if x[1] == 0:
            side.pop()
        return x[0]

    def push(s, side, sym, n=1):
        if side and side[-1][0] == sym:
            side[-1][1] += n
        else:
            side.append([sym, n])

    def step(s):
        tr = s.T[(s.st, s.cur)]
        if tr is None:
            return False
        w, d, ns = tr
        ahead = s.R if d == 1 else s.L
        behind = s.L if d == 1 else s.R
        if w == s.cur and ahead and ahead[-1][0] == s.cur:
            tr2 = s.T[(ns, s.cur)]
            if ns == s.st or (tr2 and tr2[0] == s.cur and tr2[1] == d and tr2[2] == s.st):
                n = ahead[-1][1] + 1
                ahead.pop(); s.push(behind, w, n); s.steps += n
                if ns != s.st and n % 2:
                    s.st = ns
                s.cur = s.pop(ahead)
                return True
        s.push(behind, w); s.st = ns; s.steps += 1; s.cur = s.pop(ahead)
        return True

    def at_visit(s):
        return s.st == 1 and not s.R and s.cur == 0

    def blocks(s):
        L = [list(x) for x in s.L]
        while L and L[0][0] == 0:
            L.pop(0)
        out = []
        for sym, c in L:
            if sym == 1:
                out.append(c)
            else:
                out.extend([0] * (c - 1))
        if L and L[-1][0] == 0:
            out.append(0)
        while out and out[0] == 0:
            out.pop(0)
        return out


def machine_next(b, maxsteps=10 ** 7):
    """Run the machine from the visit with block list b to the next visit: (blocks, steps) or 'HALT'."""
    r = RL()
    for i, x in enumerate(b):
        if i:
            r.push(r.L, 0)
        if x:
            r.push(r.L, 1, x)
    r.st = 1; r.cur = 0
    while r.steps < maxsteps:
        if not r.step():
            return 'HALT', r.steps
        if r.at_visit():
            return r.blocks(), r.steps
    return 'TIMEOUT', r.steps


def main():
    what, n = sys.argv[1], int(float(sys.argv[2]))
    if what == 'random':
        random.seed(1)
        bad = halts = 0
        for _ in range(n):
            b = [random.randint(0, 9) for _ in range(random.randint(1, 6))]
            while b and b[0] == 0:
                b.pop(0)
            if not b:
                continue
            got, _ = machine_next(b)
            try:
                exp = step(b)
            except Halt:
                exp = 'HALT'; halts += 1
            if got != exp:
                bad += 1
                print('MISMATCH', b, 'machine:', got, 'rule:', exp)
        print('random lists: %d, halting %d, mismatches %d' % (n, halts, bad))
    elif what == 'run':
        r = RL(); b = None; v = 0
        while v < n:
            if not r.step():
                print('HALT', r.steps); return
            if r.at_visit():
                v += 1
                cur = r.blocks()
                if b is not None and step(b) != cur:
                    print('MISMATCH at visit', v); return
                b = cur
        print('visits 1..%d from blank tape (%d steps): the rule matches at every visit' % (n, r.steps))
    elif what == 'lean':
        random.seed(2)
        bad = 0
        for _ in range(n):
            b = [random.randint(0, 9) for _ in range(random.randint(1, 7))]
            while b and b[0] == 0:
                b.pop(0)
            if not b:
                continue
            try:
                exp = step(b)
            except Halt:
                exp = None
            got = sweep(b[::-1])
            if got is not None:
                got = got[::-1]
                while got and got[0] == 0:
                    got.pop(0)
            if got != exp:
                bad += 1
                print('MISMATCH', b, exp, got)
        print('random lists: %d, step() and the Lean sweep differ on %d' % (n, bad))


if __name__ == '__main__':
    main()
