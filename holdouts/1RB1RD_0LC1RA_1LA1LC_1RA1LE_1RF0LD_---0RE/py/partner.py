"""1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE against 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE, phase map against phase map.

The two phase maps (py/phasemap.py here and in the other folder, both proved case by case in their lean/Phases.lean)
correspond under

    phi:  e(x, z) -> e(x, z),   r(x, y) -> a(x, y - 1),   q(m, k, t) -> q(m, k/2, t)      (k even)

in every case except two: the all-ones phases r(0, y) / a(0, y) and q(0, k, 0).  `check` verifies the commutation
next(phi p) = phi(next p) (up to a phase that one map skips: within three phases of A and four of B) for all small phases and lists where it fails.
`orbits K` runs both orbits from blank tape for K phases and prints where they are in step (a fixed lag in
phases) and where they part; `fatal N` compares the all-ones lengths that halt (FA for the other machine from
r(0, n), FB for this one from a(0, n)).  Since phi sends r(0, n) to a(0, n - 1), an all-ones moment shared by the two
runs halts both only if n is in FA and n - 1 in FB; that never happens below N.

usage (from the repository root):
  python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/partner.py check [N]
  python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/partner.py orbits [K]
  python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/partner.py fatal [N]
"""
import importlib.util
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


B = load("mapB", os.path.join(HERE, "phasemap.py"))
A = load("mapA", os.path.join(HERE, "..", "..", "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE", "py", "phasemap.py"))


def phi(p):
    if p[0] == 'e':
        return p
    if p[0] == 'r':
        return ('a', p[1], p[2] - 1) if p[2] >= 1 else None
    return ('q', p[1], p[2] // 2, p[3]) if p[2] % 2 == 0 else None


def ahead(nxt, p, k):
    out = []
    for _ in range(k):
        r = nxt(p)
        if r is None:
            break
        p = r[0]
        out.append(p)
    return out


def commutes(p):
    """Some phase among A's next three, mapped by phi, is among B's next four phases from phi(p)."""
    imgs = {phi(x) for x in ahead(A.nxt, p, 3)} - {None}
    return bool(imgs & set(ahead(B.nxt, phi(p), 4)))


def check(n):
    bad = {}
    total = 0
    for kind, ar in (('e', 2), ('r', 2), ('q', 3)):
        for args in itertools.product(range(n), repeat=ar):
            p = (kind,) + args
            if phi(p) is None:
                continue
            ra = A.nxt(p)
            if ra is None:
                continue
            total += 1
            if not commutes(p):
                key = (kind, 'x=0' if kind == 'r' and args[0] == 0 else
                       'm=0,t=0' if kind == 'q' and args[0] == 0 and args[2] == 0 else 'other')
                bad.setdefault(key, []).append(p)
    print(f"{total} phases with parameters < {n}; phi commutes except:")
    for k, v in sorted(bad.items()):
        print(f"  {k}: {len(v)} phases, e.g. {v[:4]}")


def orbits(k):
    pa, pb = A.INIT, B.INIT
    sa, sb = [], []
    for _ in range(k):
        sa.append(pa)
        sb.append(pb)
        pa, pb = A.nxt(pa)[0], B.nxt(pb)[0]
    where = {}
    for j, p in enumerate(sb):
        where.setdefault(p, j)
    prev = 'start'
    shared = 0
    for i, p in enumerate(sa):
        q = phi(p)
        j = where.get(q) if q is not None else None
        lag = None if j is None else j - i
        shared += j is not None and p[0] == 'e'
        if lag != prev:
            print(f"phase {i:8d} of A {str(p):34s} " + ("not on B's orbit" if lag is None else f"= phase {i + lag} of B"))
            prev = lag
    ones_a = [(i, p[2]) for i, p in enumerate(sa) if A.ones(p)]
    ones_b = [(i, p[2]) for i, p in enumerate(sb) if B.ones(p)]
    print(f"{shared} e-phases of A's first {k} are on B's orbit")
    print("all-ones lengths, A:", [n for _, n in ones_a])
    print("all-ones lengths, B:", [n for _, n in ones_b])


def fatal(n):
    fa = [m for m in range(1, n) if A.fate(('r', 0, m))]
    fb = [m for m in range(n) if B.fate(('a', 0, m))]
    print("FA:", fa)
    print("FB:", fb)
    print("n in FA with n - 1 in FB:", [m for m in fa if m - 1 in fb])


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'orbits'
    arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    {'check': lambda: check(arg or 12), 'orbits': lambda: orbits(arg or 200000),
     'fatal': lambda: fatal(arg or 3000)}[cmd]()
