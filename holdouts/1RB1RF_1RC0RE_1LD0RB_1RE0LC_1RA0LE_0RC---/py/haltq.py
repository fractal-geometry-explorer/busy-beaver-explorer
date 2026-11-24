"""Which queues lead to a halt, for 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---.

The machine can halt only where three cursor cells 1 stand side by side (`a 1 1 1`) and a cursor 0 arrives directly
right of them (lean/Escape.lean, lean/HaltRules.lean `tohalt`), and only if the triple has the right cells on its
left: the cursor 0 in front of it must follow a block of a single a, as in `b a 0 a 1 1 1` (`left` below lists the
contexts that work).  In the run such a triple forms when a cursor reaches a cursor that a birth left half way across
a separator; it is left standing only if a birth happens at exactly that visit.  Then the tape is

    1 a b a 0 a 1 1 1 a^10 Q 0 a 1 B>        Q = (b a^n1)^q1 (b a^n2)^q2 ...: the queue right of the triple

and the part right of the triple runs like a machine of its own until the first cursor reaches the triple.  Three
outcomes (this program decides which, by the exact accelerated simulator py/qsim.py; its jumps are validated, not
proved):

    HALT    the first cursor to reach the triple is a 0: the machine halts;
    arr     a cursor reaches the triple and the machine does not halt (it is a 1, or the left context is not one
            that halts): the triple is destroyed;
    alone   every cursor right of the triple is used up before one reaches it (cursors meeting cancel), so the
            triple's own 1 becomes the active cursor and moves on: destroyed, no halt.

usage:
    python3 haltq.py one N QMAX          the queue (b a^N)^q for q = 1 .. QMAX; prints the q of each outcome
    python3 haltq.py grid N1 N2 C        the queues (b a^N1)^c1 (b a^N2)^c2, 0 <= c1, c2 < C, as a map
    python3 haltq.py queue "N:Q N:Q ..."  one queue, e.g. "254:3 1022:12"
    python3 haltq.py sizes QMAX          which (b a^N)^q halt, for each N = 4^j - 2 up to 65534
    python3 haltq.py left                which small contexts X in `1 a b a^2 b a^2 X 0 a 1 1 1 0 a^22 0 B>` halt
    PRE="1 a b a^2 b a^2 0 a 1 1 1 a^10" python3 haltq.py sizes 30     the same with another left part
"""
import os
import sys
from qsim import Sim, Halt, B
from escape import expand

PRE = os.environ.get("PRE", "1 a b a 0 a 1 1 1 a^10")


def start(blocks, pre=PRE):
    s = Sim()
    s.L, s.R, s.s = [], [], B
    for c in expand(pre):
        s.push_L(int(c))
    for n, q in blocks:
        if q:
            s.L.append(('S', n, q))
    for c in expand("0 a 1"):
        s.push_L(int(c))
    s.canon()
    return s


def triple_at(L):
    for i in range(len(L) - 2):
        if L[i] == 1 and L[i + 1] == 1 and L[i + 2] == 1:
            return i
    return None


def classify(blocks, maxv=10 ** 7):
    """('HALT' | 'arr1' | 'alone' | 'open', visits stopped at, steps)"""
    s = start(blocks)
    prev, v = list(s.L), 0
    try:
        while v < maxv:
            s.trip(); s.sample(); s.check_pending(); v += 1
            if triple_at(s.L) is None:
                j = triple_at(prev)
                cursors = [x for x in prev[j + 3:-1] if type(x) is int]
                return ('arr' if cursors else 'alone'), v, s.steps
            prev = list(s.L)
            s.try_jump()
    except Halt:
        return 'HALT', v, s.steps
    return 'open', v, s.steps


def intervals(res):
    out, i = [], 0
    while i < len(res):
        j = i
        while j < len(res) and res[j] == res[i]:
            j += 1
        out.append((res[i], i + 1, j)); i = j
    return out


def one(n, qmax):
    res = [classify([(n, q)])[0] for q in range(1, qmax + 1)]
    return ', '.join('%s q=%d..%d' % x if x[1] != x[2] else '%s q=%d' % (x[0], x[1]) for x in intervals(res))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'sizes'
    if cmd == 'one':
        print(one(int(sys.argv[2]), int(sys.argv[3])))
    elif cmd == 'sizes':
        qmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
        for j in range(1, 9):
            n = 4 ** j - 2
            print('(b a^%d)^q:' % n, one(n, qmax), flush=True)
    elif cmd == 'grid':
        n1, n2, C = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        print('(b a^%d)^c1 (b a^%d)^c2: rows c1, columns c2 = 0 .. %d;  H halt, . no halt (a cursor arrives), ' 
              '_ no halt (no cursor arrives)' % (n1, n2, C - 1))
        for c1 in range(C):
            row = ''
            for c2 in range(C):
                if c1 == c2 == 0:
                    row += ' '; continue
                r = classify([(n1, c1), (n2, c2)])[0]
                row += {'HALT': 'H', 'arr': '.', 'alone': '_', 'open': '?'}[r]
            print('%3d %s' % (c1, row), flush=True)
    elif cmd == 'left':
        import itertools
        from escape import run
        toks = ['a', 'a^2', 'a^3', 'a^14', 'b', '0', '1']
        xs = [' '.join(p) for k in range(4) for p in itertools.product(toks, repeat=k)]
        good = []
        for x in xs:
            hist, end = run("1 a b a^2 b a^2 %s 0 a 1 1 1 0 a^22 0" % x, 2)
            if end and end[0] == 'HALT':
                good.append(x)
        print('%d of %d contexts X halt: %s' % (len(good), len(xs), ', '.join(repr(x) for x in good)))
    elif cmd == 'queue':
        blocks = [tuple(int(x) for x in t.split(':')) for t in sys.argv[2].split()]
        print(classify(blocks))
