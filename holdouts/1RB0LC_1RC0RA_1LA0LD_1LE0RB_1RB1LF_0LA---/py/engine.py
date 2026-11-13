"""An exact run-length simulator of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---, and the tape read as runs.

The tape is kept as two stacks of cells and of runs of the pair 01 (left of the head: 10).  Single machine steps,
plus two jumps, both theorems of lean/Rules.lean:  A> (01)^n -> (10)^n A>  (`pass_run`)  and
(10)^n A>1 -> A>1 (10)^n  (`back_run`).  An *event* is the head in state A reading 0 with blank tape on its left.

At an event the tape is printed as tokens:  n = (01)^n,  | = 00110 (a separator),  "..." = other cells (cursors).

usage: python3 engine.py check [STEPS] [EVERY]   compare with the C simulator (tools/c/tmrun): the step of every
                                                  event, and the whole tape at every EVERY-th event
       python3 engine.py run [STEPS]             print the tape at the first event after 10, 100, 1000, ... steps
       python3 engine.py events [STEPS]          print every event
"""
import os, re, subprocess, sys

M = '1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---'
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, '../../../tools/c')
T = {('A', 0): (1, 1, 'B'), ('A', 1): (0, -1, 'C'), ('B', 0): (1, 1, 'C'), ('B', 1): (0, 1, 'A'),
     ('C', 0): (1, -1, 'A'), ('C', 1): (0, -1, 'D'), ('D', 0): (1, -1, 'E'), ('D', 1): (0, 1, 'B'),
     ('E', 0): (1, 1, 'B'), ('E', 1): (1, -1, 'F'), ('F', 0): (0, -1, 'A'), ('F', 1): None}


class Eng:
    """L, R: stacks (the end of the list is next to the head; R's last entry is the cell under the head).
    Entries: 0, 1, or [n]: on R the run (01)^n read from the head, on L the run (10)^n read towards the head."""

    def __init__(s, cells=()):
        s.L = []; s.R = []; s.st = 'A'; s.steps = 0; s.halted = False
        for b in reversed(cells): s.push(s.R, b)

    @staticmethod
    def push(S, b):
        if b == 0 and S and S[-1] == 1:
            S.pop()
            if S and type(S[-1]) is list: S[-1][0] += 1
            else: S.append([1])
        else:
            S.append(b)

    def at_event(s):
        return s.st == 'A' and not s.L and (not s.R or type(s.R[-1]) is list or s.R[-1] == 0)

    def step(s):
        R = s.R; L = s.L; st = s.st
        if R:
            top = R[-1]
            if type(top) is list:
                if st == 'A':                      # pass_run
                    n = top[0]; R.pop()
                    if L and type(L[-1]) is list: L[-1][0] += n
                    else: L.append([n])
                    s.steps += 2 * n
                    return
                if top[0] == 1: R.pop()
                else: top[0] -= 1
                R.append(1); cur = 0
            else:
                cur = R.pop()
        else:
            cur = 0
        if st == 'A' and cur == 1 and L and type(L[-1]) is list and L[-1][0] >= 3:
            n = L[-1][0]; L[-1][0] = 1             # back_run over n-1 pairs: (10)^(n-1) = 1 (01)^(n-2) 0
            R.append(0); R.append([n - 2]); R.append(1); R.append(1)
            s.steps += 2 * (n - 1)
            return
        tr = T[(st, cur)]
        if tr is None:
            R.append(cur); s.halted = True
            return
        w, d, s.st = tr
        s.steps += 1
        if d == 1:
            s.push(L, w)
        else:
            s.push(R, w)
            if L:
                t = L[-1]
                if type(t) is list:
                    if t[0] == 1: L.pop()
                    else: t[0] -= 1
                    L.append(1); c = 0
                else:
                    c = L.pop()
            else:
                c = 0
            s.push(R, c)

    def run_event(s):
        """Advance to the next event; False if the machine halts."""
        while True:
            s.step()
            if s.halted: return False
            if s.at_event(): return True

    def cells(s):
        out = []
        for x in reversed(s.R):
            out.append('01' * x[0] if type(x) is list else str(x))
        return ''.join(out).rstrip('0')

    def tokens(s):
        segs = []
        for x in reversed(s.R):
            if type(x) is list and x[0] > 2:
                if segs and type(segs[-1]) is int: segs[-1] += x[0]
                else: segs.append(x[0])
                continue
            x = '01' * x[0] if type(x) is list else str(x)
            if segs and type(segs[-1]) is str: segs[-1] += x
            else: segs.append(x)
        return tokens(segs)


def tokens(segs):
    """Runs of 01 (maximal, read from the left), separators 00110, other cells in quotes."""
    out = []
    def run(n):
        if out and out[-1].isdigit(): out[-1] = str(int(out[-1]) + n)
        else: out.append(str(n))
    for x in segs:
        if type(x) is int:
            run(x); continue
        i = 0; buf = ''
        while i < len(x):
            j = i
            while x.startswith('01', j): j += 2
            if j > i or x.startswith('00110', i):
                if buf: out.append('"' + buf + '"'); buf = ''
                if j > i: run((j - i) // 2); i = j
                else: out.append('|'); i += 5
            else:
                buf += x[i]; i += 1
        if buf: out.append('"' + buf + '"')
    if out and out[-1][0] == '"':
        t = out[-1].strip('"').rstrip('0')
        out[-1:] = ['"' + t + '"'] if t else []
    return out


def check(steps, every):
    exe = os.path.join(HERE, 'tmrun')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(TOOLS, 'tmrun.c')], check=True)
    p = subprocess.Popen([exe, M, str(steps), 'at', 'A', 'L', '100000000'], stdout=subprocess.PIPE, text=True)
    e = Eng(); n = full = 0
    for line in p.stdout:
        a = line.split(' ', 2)
        if a[0] in ('running', 'halted') or not a[1].startswith('A>0'):
            continue
        e.run_event(); n += 1
        if int(a[0]) != e.steps:
            print(f'MISMATCH: event {n} at step {a[0]}, engine {e.steps}'); return 1
        if n % every == 0 or n < 300:
            cells = []
            for tok in line.split()[1:]:
                m = re.fullmatch(r'(?:[A-F]>)?([01])(?:\^(\d+))?', tok)
                cells.append(m.group(1) * int(m.group(2) or 1))
            if ''.join(cells).rstrip('0') != e.cells():
                print(f'MISMATCH: tape at event {n}, step {a[0]}'); return 1
            full += 1
    print(f'{n} events up to step {e.steps}: the engine has the same step at every one and the same tape at the '
          f'{full} compared; {len(e.tokens())} tokens at the end')
    return 0


def run(steps, every_event):
    e = Eng(); n = 0; nxt = 10
    while e.steps < steps:
        if not e.run_event():
            print(f'HALT after {e.steps} steps'); return
        n += 1
        if every_event or e.steps >= nxt:
            print(e.steps, n, ' '.join(e.tokens()))
            while nxt <= e.steps: nxt *= 10
    print(f'no halt in {e.steps} steps ({n} events)')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    N = int(float(sys.argv[2])) if len(sys.argv) > 2 else 300000000
    if cmd == 'check':
        sys.exit(check(N, int(sys.argv[3]) if len(sys.argv) > 3 else 200))
    run(N, cmd == 'events')
