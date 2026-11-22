"""The right-end layer of the six machines with this tape structure (README.md, "The right-end layer").

usage (from the repository root):
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlayer.py check [STEPS]     # the model against the runs
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlayer.py explore [N] [MAXM] [I]  # every parity input
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlayer.py same [N]          # one model for six
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlayer.py halts [K] [M]     # halting end forms
  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/endlayer.py rules             # the common rules

The tape, read at a return of the head to the left end, is in group form: groups `1 (01)^(m-1)` of m single 1s
separated by `000`.  Write it as tokens: `m` (a group and `000`), `m_s` (a group and s zeros, s != 3), `m$` (the last
group).  Away from the ends every m is odd; the rightward sweep reads the groups in pairs (a, b) and a round trip
turns the pair into  1 x (a-1)/2, then b+2  (the running XOR of Sweep.lean / Bulk.lean, in this notation).

The *tail* is what follows the last complete pair of odd groups.  `G(tail)` is one round trip of the machine on a
tape made of 16 such pairs and the tail, the head arriving at the tail in the first-slot state (E for this machine):
a finite run, computed here by plain simulation.  It does not look at the pairs on its left except to sweep them
(checked on every call: the pairs come back as they should).  So the right end evolves on its own: after a round
trip the tape there is (image of the pairs) + G(tail), and the only thing the rest of the tape decides is whether
the first token of G(tail) is in the first or the second slot of a pair at the next round trip (the parity of the
running XOR there).  `check` compares this with the real runs of all six machines; `explore` follows the tails for
every sequence of parities.

`check` needs a C compiler (it builds c/endtails.c into a temporary directory).
"""
import collections
import functools
import os
import random
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

# the six holdouts with this tape structure (README.md, "Related machines"); MIRROR: sweeps run the other way
MACHINES = ['1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---', '1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE',
            '1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE', '1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---',
            '1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---', '1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---']
MIRROR = {'1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE', '1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE'}
# the states in which the rightward sweep meets a group in the first / second slot of a pair (E / A here, renamed
# in the others)
SLOTS = {MACHINES[0]: 'EA', MACHINES[1]: 'EF', MACHINES[2]: 'EF', MACHINES[3]: 'CD', MACHINES[4]: 'BC', MACHINES[5]: 'BC'}
END = -1  # the separator of the last group


# ---------------------------------------------------------------- tokens
def tok2cells(tl):
    return ''.join('1' + '01' * (m - 1) + ('0' * s if s >= 0 else '') for m, s in tl)


def toks(s):
    """The tokens of a cell string that starts at a group (None if it is not a list of groups)."""
    s = s.rstrip('0')
    if not s:
        return ()
    t = [((len(g) + 1) // 2, len(z)) for g, z in re.findall(r'(1(?:01)*)(0*)', s)]
    if not s.startswith('1') or tok2cells(t) != s:
        return None
    t[-1] = (t[-1][0], END)
    return tuple(t)


def fmt(t):
    if isinstance(t, str):
        return t
    return ' '.join(f'{m}' if s == 3 else (f'{m}$' if s == END else f'{m}_{s}') for m, s in t)


def parse(text):
    out = []
    for x in text.split():
        if x.endswith('$'):
            out.append((int(x[:-1]), END))
        elif '_' in x:
            a, b = x.split('_')
            out.append((int(a), int(b)))
        else:
            out.append((int(x), 3))
    return tuple(out)


def regular(x):
    return x[1] == 3 and x[0] % 2 == 1


def split(U, y):
    """The next tail, from the output U of a round trip: y = 0 if U[0] is in the first slot of a pair at the next
    round trip, y = 1 if in the second (its partner, an odd group of the bulk, then only adds single 1s, so it is
    written as 1)."""
    U = list(U)
    i = 0
    if y == 1:
        if len(U) > 1 and regular(U[0]):
            i = 1
        else:
            U = [(1, 3)] + U
    while i + 1 < len(U) and regular(U[i]) and regular(U[i + 1]):
        i += 2
    return tuple(U[i:])


def bulk_image(t, i):
    """The image of the pairs of odd groups of t from index i, and the index where they stop."""
    out = []
    while i + 1 < len(t) and regular(t[i]) and regular(t[i + 1]):
        out += [(1, 3)] * ((t[i][0] - 1) // 2) + [(t[i + 1][0] + 2, 3)]
        i += 2
    return out, i


# ---------------------------------------------------------------- the model
def table(m, mirror=False):
    t = {}
    for s, part in enumerate(m.split('_')):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            d = 1 if x[1] == 'R' else -1
            t[(s, r)] = None if x[2] == '-' else (int(x[0]), -d if mirror else d, ord(x[2]) - 65)
    return t


class Model:
    NPRE = 16

    def __init__(self, machine):
        self.machine = machine
        self.T = table(machine, machine in MIRROR)
        self.a = ord(SLOTS[machine][0]) - 65
        self.pre = [(1, 3)] * (2 * self.NPRE)
        self.ref = self._run(((2, END),))[1]

    def _run(self, tail, maxsteps=10 ** 6):
        pc = tok2cells(self.pre)
        cells = pc + tok2cells(tail)
        n = len(cells) + 4000
        tape = bytearray(n)
        base = 20
        for i, c in enumerate(cells):
            tape[i + base] = int(c)
        p, st, off, went, T = base, self.a, base + len(pc), False, self.T
        for _ in range(maxsteps):
            tr = T[(st, tape[p])]
            if tr is None:
                return 'HALT', None
            tape[p], p, st = tr[0], p + tr[1], tr[2]
            if p > off:
                went = True
            if went and p < base + 40:
                break
            if p >= n - 5:
                return 'RUNAWAY', None
        else:
            return 'TIMEOUT', None
        # the pairs come back one cell to the left, like the whole tape; the tail's image starts at off - 1
        return ''.join(map(str, tape[off - 1:])), bytes(tape[base + 48:off - 1])

    @functools.lru_cache(maxsize=None)
    def G(self, tail):
        """One round trip on the tail: its image (a token tuple), or 'HALT' (or a reason the model does not apply)."""
        s, left = self._run(tuple(tail))
        if left is None:
            return s
        if left != self.ref:
            return 'LOOKS-LEFT'
        t = toks(s)
        return t if t is not None else 'NOT-GROUPS'


# ---------------------------------------------------------------- check against the runs
def endtails(machine, steps, w=600):
    src = os.path.join(HERE, '..', 'c', 'endtails.c')
    exe = os.path.join(tempfile.gettempdir(), 'endtails_' + str(os.getpid()))
    subprocess.run(['cc', '-O2', '-o', exe, src], check=True)
    out = subprocess.run([exe, machine, '1' if machine in MIRROR else '0', str(steps), str(w)], check=True,
                         capture_output=True, text=True).stdout
    os.remove(exe)
    return [ln.split() for ln in out.splitlines()]


def check(machine, steps):
    """Every round trip of the run: the tail, the model's image of it, and the tape after the round trip."""
    M = Model(machine)
    a, b = SLOTS[machine]
    rows = [r for r in endtails(machine, steps) if len(r) == 3]
    stats = collections.Counter()
    tails = collections.Counter()
    for (k0, s0, c0), (k1, s1, c1) in zip(rows, rows[1:]):
        if s0 not in (a, b):
            stats['skipped (head did not reach X)'] += 1
            continue
        t0, t1 = toks(c0), toks(c1)
        i = 0 if s0 == a else 1
        if i == 1:
            if not regular(t0[0]):
                stats['skipped (X in a defect)'] += 1
                continue
            pred = [(t0[0][0] + 2, 3)]
        else:
            pred = []
        more, i = bulk_image(t0, i)
        pred += more
        tail = t0[i:]
        if len(pred) < 15:
            stats['skipped (tail too long for X)'] += 1
            continue
        ps, ts = fmt(tuple(pred[-15:])), fmt(t1)
        pos = ts.find(ps)
        if pos < 0:
            stats['bulk mismatch'] += 1
            continue
        tails[tail] += 1
        stats['round trips'] += 1
        if fmt(M.G(tail)) != ts[pos + len(ps):].strip():
            stats['MODEL MISMATCH'] += 1
    return stats, tails


# ---------------------------------------------------------------- every parity input
def explore(machine, limit, maxm, start=((2, END),)):
    """Breadth-first search of the tails reachable from `start` when the parity bit of every round trip is free."""
    M = Model(machine)
    seen = {start: None}
    q = collections.deque([start])
    bad = []
    while q and len(seen) < limit:
        t = q.popleft()
        U = M.G(t)
        if isinstance(U, str):
            bad.append((t, U))
            continue
        for y in (0, 1):
            n = split(U, y)
            if max(m for m, s in n) > maxm:
                continue
            if n not in seen:
                seen[n] = t
                q.append(n)
    return seen, q, bad


# ---------------------------------------------------------------- the common rules, as checks of G
def ones(k):
    return [(1, 3)] * k


def rule_checks(M, contexts, rng):
    """Each common rule of README.md checked on random rests X (G is exact, so each check is a theorem about one tape)."""
    G = M.G
    fails = collections.Counter()
    n = collections.Counter()
    for X in contexts:
        X = list(X)
        gx = G(tuple(X))
        a, b, j, c = rng.choice([1, 3, 5, 7, 9]), rng.randint(1, 9), rng.randint(1, 6), rng.randint(2, 9)
        if not isinstance(gx, str):
            n['pair'] += 1
            if G(tuple([(a, 3), (b, 3)] + X)) != tuple(ones((a - 1) // 2) + [(b + 2, 3)] + list(gx)):
                fails['pair'] += 1
        n['even'] += 1
        exp = ones(j - 1) + ([(1, 3), (3, 0), (b - 1, 3)] if b > 1 else [(1, 3), (3, 2)]) + X
        if G(tuple([(2 * j, 3), (b, 3)] + X)) != tuple(exp):
            fails['even'] += 1
        n['touch'] += 1
        if G(tuple([(3, 0), (c, 3)] + X)) != tuple([(1, 3), (1, 3), (c - 1, 3)] + X):
            fails['touch'] += 1
        n['halt'] += 1
        if G(tuple([(2 * j, 3), (1, 0)] + X)) != 'HALT':
            fails['halt'] += 1
    return n, fails


def main(argv):
    cmd = argv[0] if argv else 'check'
    if cmd == 'check':
        steps = int(float(argv[1])) if len(argv) > 1 else 10 ** 8
        for m in MACHINES:
            stats, tails = check(m, steps)
            print(f'{m}: {dict(stats)}, {len(tails)} different tails')
    elif cmd == 'explore':
        limit = int(argv[1]) if len(argv) > 1 else 20000
        maxm = int(argv[2]) if len(argv) > 2 else 40
        mach = MACHINES[int(argv[3])] if len(argv) > 3 else MACHINES[0]
        seen, q, bad = explore(mach, limit, maxm)
        print(f'{mach}: {len(seen)} tails reached from 2$ (groups up to {maxm}), {len(q)} not yet followed; '
              f'{len(bad)} halt or leave the model: {[(fmt(t), u) for t, u in bad[:5]]}')
        lens = collections.Counter(sum(2 * m + 2 for m, s in t) for t in seen)
        print('longest tail:', max(lens), 'cells')
    elif cmd == 'same':
        limit = int(argv[1]) if len(argv) > 1 else 3000
        seen, _, _ = explore(MACHINES[0], limit, 40)
        Ms = [Model(m) for m in MACHINES]
        diff = 0
        for t in seen:
            r = {fmt(M.G(t)) for M in Ms}
            if len(r) > 1:
                diff += 1
                print('differ:', fmt(t), r)
        print(f'{len(seen)} tails: the six machines give the same image for {len(seen) - diff}')
    elif cmd == 'halts':
        k = int(argv[1]) if len(argv) > 1 else 3
        mm = int(argv[2]) if len(argv) > 2 else 5
        M = Model(MACHINES[0])
        import itertools
        body = [(m, s) for m in range(1, mm + 1) for s in (3, 2, 0)]
        total = 0
        halting = []
        for n in range(k):
            for bd in itertools.product(body, repeat=n):
                for e in range(1, mm + 1):
                    t = tuple(bd) + ((e, END),)
                    total += 1
                    if M.G(t) == 'HALT':
                        halting.append(t)
        print(f'{total} tails of at most {k} tokens (groups up to {mm}, gaps 3, 2, 0): {len(halting)} halt')
        pat = all(any(x[0] % 2 == 0 and x[1] == 3 and y == (1, 0) for x, y in zip(t, t[1:])) for t in halting)
        print('every halting one contains an even group followed by a touching 1 (`2j 1_0`):', pat)
        for t in halting[:20]:
            print('  ', fmt(t))
    elif cmd == 'rules':
        rng = random.Random(1)
        seen, _, _ = explore(MACHINES[0], 4000, 40)
        ctx = rng.sample(list(seen), 1500)
        for m in MACHINES:
            n, fails = rule_checks(Model(m), ctx, rng)
            print(f'{m}: ' + ', '.join(f'{r}: {n[r] - fails[r]}/{n[r]}' for r in n))
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main(sys.argv[1:])
