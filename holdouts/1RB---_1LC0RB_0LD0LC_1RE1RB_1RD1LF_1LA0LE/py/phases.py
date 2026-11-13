"""Phase map of 1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE, measured by simulation (trusted, not Lean).

A phase start is the moment the head, in state C, is at the left end of the tape with  C>0 0^4 111 (01)^n P  (P a word, blank beyond); the phase map is n' = (3n + d)/2 with (P', d) depending only on P and the parity of n.

usage: python3 phases.py check [STEPS]    compare the phase map with the C simulator (tools/c/tmrun) at every phase
                                          start of the run from blank tape
       python3 phases.py orbit [PHASES]   iterate the phase map from the run's first phase start, exactly (big
                                          integers), the word P by simulation of each new (P, residue) once
       python3 phases.py bfs [WORDS]      explore every word P reachable for every sequence of residues: halts
                                          reachable or not, and a shortest residue sequence to a halt
       python3 phases.py walk [N] [LEN]   the same graph walked with random residues (the coin-flip heuristic)
"""
import os
import random
import subprocess
import sys
from collections import deque
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, '../../../tools/c')
CONFIG = {'machine': '1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE', 'kind': 'mirror', 'state': 'C', 'gap': 5}
M = CONFIG['machine']
STATES = 'ABCDEF'


def parse_machine(text):
    t = {}
    for i, tr in enumerate(text.split('_')):
        for s in (0, 1):
            x = tr[3 * s:3 * s + 3]
            t[(i, s)] = None if x[2] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t


TABLE = parse_machine(M)


class Sim:
    """A plain simulator on a bytearray, the head starting at the end of `left` on the first cell of `right`."""

    def __init__(self, left, state, right, room=4 * 10 ** 6):
        self.tape = bytearray(2 * room + len(left) + len(right))
        self.off = room + len(left)
        for i, v in enumerate(left):
            self.tape[self.off - len(left) + i] = v
        for i, v in enumerate(right):
            self.tape[self.off + i] = v
        self.h, self.st, self.steps = self.off, state, 0
        self.lo, self.hi = self.off - len(left), self.off + len(right) - 1

    def step(self):
        r = TABLE[(self.st, self.tape[self.h])]
        if r is None:
            return False
        w, d, n = r
        self.tape[self.h] = w
        self.h += d
        self.st = n
        self.steps += 1
        if self.h < self.lo:
            self.lo = self.h
        elif self.h > self.hi:
            self.hi = self.h
        return True

    def word(self, a, b):
        return ''.join('01'[x] for x in self.tape[a:b])


S = STATES.index(CONFIG['state'])
KIND = CONFIG['kind']
NRES = 3 if KIND == 'suffix' else 2


def start(P, n):
    """The phase-start configuration for word P and counter n: (left cells, state, right cells)."""
    if KIND == 'suffix':        # P 1^n SFX S>0 at the right end
        return [int(x) for x in P] + [1] * n + [int(x) for x in CONFIG['sfx']], S, [0]
    if KIND == 'bounce':        # P (10)^n 111 S>0 at the right end
        return [int(x) for x in P + '10' * n + '111'], S, [0]
    # mirror: S>0 0^gap 111 (01)^n P at the left end
    return [], S, [0] * CONFIG['gap'] + [1, 1, 1] + [int(x) for x in '01' * n + P]


def recog_cells(cells, h, st):
    """(P, n) if the configuration (cells, head index h, state letter st) is a phase start, else None."""
    if st != CONFIG['state']:
        return None
    if KIND == 'suffix':
        sfx = CONFIG['sfx']
        if h != len(cells) - 1 or cells[h] != '0':
            return None
        s = ''.join(cells[:h])
        if not s.endswith('11' + sfx):
            return None
        i = len(s) - len(sfx)
        j = i
        while j > 0 and s[j - 1] == '1':
            j -= 1
        return s[:j].lstrip('0'), i - j
    if KIND == 'bounce':
        if h != len(cells) - 1 or cells[h] != '0':
            return None
        s = ''.join(cells[:h])
        if not s.endswith('111'):
            return None
        s = s[:-3]
        i, k = len(s), 0
        while i >= 2 and s[i - 2:i] == '10':
            k += 1
            i -= 2
        return s[:i].lstrip('0'), k
    if h != 0:
        return None
    s = ''.join(cells)
    g = CONFIG['gap']
    if not s.startswith('0' * g + '111') or s[g + 3:g + 4] == '1':
        return None
    s = s[g + 3:]
    i, k = 0, 0
    while s[i:i + 2] == '01':
        k += 1
        i += 2
    return s[i:].rstrip('0'), k


def recog(sim):
    if sim.st != S:
        return None
    if KIND == 'mirror':
        if sim.h != sim.lo:
            return None
    elif sim.h != sim.hi:
        return None
    return recog_cells(list(sim.word(sim.lo, sim.hi + 1)), sim.h - sim.lo, STATES[sim.st])


def offset(n, n2):
    """The constant d of the phase map: n' = MULT*(n//3) + d (suffix kind), n' = (3n + d)/2 (bounce kinds)."""
    return n2 - CONFIG['mult'] * (n // 3) if KIND == 'suffix' else 2 * n2 - 3 * n


def apply_map(n, d):
    return CONFIG['mult'] * (n // 3) + d if KIND == 'suffix' else (3 * n + d) // 2


def run_phase(P, n, maxsteps=5 * 10 ** 7):
    left, st, right = start(P, n)
    sim = Sim(left, st, right)
    while sim.steps < maxsteps:
        if not sim.step():
            return 'HALT'
        if sim.steps >= 2:
            r = recog(sim)
            if r is not None:
                return r
    return None


@lru_cache(None)
def T(P, r):
    """(P', d) for the phase from word P with counter residue r, from three sample counters (they must agree),
    or 'HALT' / 'NONE' / 'AMBIG'."""
    outs = set()
    m = NRES
    for base in (len(P) + 10, len(P) + 17, len(P) + 25):
        n = m * base + r
        res = run_phase(P, n)
        if res is None:
            outs.add('NONE')
        elif res == 'HALT':
            outs.add('HALT')
        else:
            outs.add((res[0], offset(n, res[1])))
    if len(outs) != 1:
        return 'AMBIG'
    return outs.pop()


def tmrun_events(steps):
    exe = os.path.join(HERE, 'tmrun')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(TOOLS, 'tmrun.c')], check=True)
    side = 'L' if KIND == 'mirror' else 'R'
    out = subprocess.run([exe, M, str(steps), 'at', CONFIG['state'], side, '1000000000'], capture_output=True,
                         text=True).stdout
    os.remove(exe)
    for line in out.splitlines():
        p = line.split(' ', 1)
        if p[0] in ('running', 'halted'):
            continue
        cells, h, st = [], None, None
        for tok in p[1].split():
            if '>' in tok:
                st, tok = tok[0], tok[2:]
                h = len(cells)
            b, _, e = tok.partition('^')
            cells += [b] * int(e or 1)
        x = recog_cells(cells, h, st)
        if x is not None:
            yield int(p[0]), x


def check(steps):
    evs = list(tmrun_events(steps))
    n = 0
    for (t0, x), (t1, y) in zip(evs, evs[1:]):
        P, c = x
        if c < 6:
            continue
        e = T(P, c % NRES)
        z = (e[0], apply_map(c, e[1])) if isinstance(e, tuple) else e
        if z != y:
            print(f'MISMATCH: phase start {x} at step {t0}: map gives {z}, machine {y} at step {t1}')
            return 1
        n += 1
    print(f'{len(evs)} phase starts up to step {evs[-1][0]}; the map agrees at all {n} transitions checked; '
          f'last {evs[-1][1][0]!r} {evs[-1][1][1]}')
    return 0


def first_phase():
    for t, x in tmrun_events(10 ** 6):
        if x[1] >= 6:
            return t, x


def orbit(phases):
    sys.set_int_max_str_digits(0)
    t, (P, n) = first_phase()
    print(f'first phase start at step {t}: P = {P!r}, n = {n}')
    words = {}
    for i in range(1, phases + 1):
        e = T(P, n % NRES)
        if not isinstance(e, tuple):
            print(f'phase {i}: {e} (word {P!r}, residue {n % NRES}, n has {n.bit_length()} bits)')
            return
        P, n = e[0], apply_map(n, e[1])
        words[P] = words.get(P, 0) + 1
        if i <= 30 or i % (phases // 10 or 1) == 0:
            print(f'phase {i}: P = {P!r}, n = {n if n < 10 ** 20 else "%d bits" % n.bit_length()}')
    print(f'{phases} phases, no halt; {len(words)} distinct words, longest {max(map(len, words))}')


def bfs(limit):
    seen, todo, g = {''}, deque(['']), {}
    while todo and len(g) < limit:
        P = todo.popleft()
        g[P] = [T(P, r) for r in range(NRES)]
        for e in g[P]:
            if isinstance(e, tuple) and e[0] not in seen:
                seen.add(e[0])
                todo.append(e[0])
    bad = [(P, r, e) for P, row in g.items() for r, e in enumerate(row) if not isinstance(e, tuple)]
    print(f'{len(g)} words expanded (longest {max(map(len, g))}); {len(bad)} transitions that do not return to a '
          f'phase start: {bad[:6]}')
    prev, q = {'': None}, deque([''])
    while q:
        p = q.popleft()
        for r, e in enumerate(g.get(p, [])):
            if e == 'HALT':
                path = [(p, r)]
                while prev[p]:
                    p, r0 = prev[p]
                    path.append((p, r0))
                print(f'shortest residue sequence to a halt: {len(path)} phases: ' +
                      ' '.join(f'{w!r}:{r}' for w, r in reversed(path)))
                return g
            if isinstance(e, tuple) and e[0] not in prev and e[0] in g:
                prev[e[0]] = (p, r)
                q.append(e[0])
    print('no halt reachable among the words expanded')
    return g


def walk(n, length):
    random.seed(1)
    halts, tot = 0, 0
    for _ in range(n):
        P = ''
        for _ in range(length):
            e = T(P, random.randrange(NRES))
            tot += 1
            if not isinstance(e, tuple):
                halts += e == 'HALT'
                break
            P = e[0]
    print(f'{n} random walks of up to {length} phases: {halts} halts in {tot} phases')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    arg = [int(float(x)) for x in sys.argv[2:]]
    if cmd == 'check':
        sys.exit(check(arg[0] if arg else 200000000))
    if cmd == 'orbit':
        orbit(arg[0] if arg else 1000)
    if cmd == 'bfs':
        bfs(arg[0] if arg else 300)
    if cmd == 'walk':
        walk(arg[0] if arg else 100, arg[1] if len(arg) > 1 else 1000)
