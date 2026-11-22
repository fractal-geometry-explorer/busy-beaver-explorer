"""Right-end events of 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA: which wall visits halt, and what an event does.

Words are digit lists (run lengths of Y between X's, X = 10, Y = 11). The recursion G (gmodel.py, geng.py) is exact
except at an *event*: a hit that reaches the last digit, after which the head runs into the blank right end in D.
Everything here is direct simulation of the machine (c/visit.c), nothing is assumed about events.

  python3 events.py classify N        every word of at most N pairs: one wall visit each (N = 18: 524,287 words,
                                      about 7 minutes); counts, the halting words, and checks that halting depends
                                      only on the hit (the word after the first digit); writes halting_hits_N.txt
  python3 events.py anatomy           the event visit of the two-digit words (a, b) with plenty of blank pairs to
                                      the left: where the next wall visit is, its word, and which b halt
  python3 events.py hits FILE         the wall visit of 0 T for every hit word T in FILE (one per line)
  python3 events.py rule11 [SEED]     4,000 random words whose events all have a last digit b >= 11: the machine
                                      agrees with the recursion extended by h(b) = g(b) (b != 13) and h(13) = halt
  python3 events.py innermost N       for every event word of at most N pairs (from classify's run): the innermost
                                      event word is two digits (a, b), and halting is not decided by (a, b) and the
                                      remaining sub-visits of the innermost frames alone
"""
import os, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
VISIT = os.environ.get("VISIT", "/tmp/visit_34090")


def visit_bin():
    if not os.path.exists(VISIT):
        subprocess.check_call(["gcc", "-O2", "-o", VISIT, os.path.join(HERE, "../c/visit.c")])
    return VISIT


def cells(d):
    return "10".join("11" * x for x in d)


def to_digits(c):
    """cells right of a wall as a digit word, or None if they are not pairs 10 / 11"""
    if len(c) % 2:
        c += "0"
    d = [0]
    for i in range(0, len(c), 2):
        p = c[i:i + 2]
        if p == "11":
            d[-1] += 1
        elif p == "10":
            d.append(0)
        else:
            return None
    return d


def run_visits(words, cap=10 ** 9):
    p = subprocess.run([visit_bin(), str(cap)], input="".join(cells(w) + "\n" for w in words),
                       capture_output=True, text=True, check=True)
    return p.stdout.split("\n")[:len(words)]


def all_words(n):
    out = []

    def rec(pref, rem):
        out.append(tuple(pref))
        for x in range(rem):
            rec(pref + [x], rem - 1 - x)
    for d0 in range(n + 1):
        rec([d0], n - d0)
    return out


def plen(w):
    return sum(w) + len(w) - 1


def Gctx(d):
    """the recursion on pairs; at an event returns ('EVENT', innermost word, frames [(prefix pairs, remaining)])"""
    S = "X".join("Y" * x for x in d)
    stack = []
    cur = S
    while True:
        a = 0
        while a < len(cur) and cur[a] == "Y":
            a += 1
        if a == len(cur):
            val = "X" * a + "YY"
        else:
            k = 0
            while a + 1 + k < len(cur) and cur[a + 1 + k] == "Y":
                k += 1
            if a + 1 + k == len(cur):
                return "EVENT", to_digits("".join("11" if c == "Y" else "10" for c in cur)), stack
            U = cur[a + k + 2:]
            if k == 0:
                val = "X" * a + "YYY" + U
            else:
                stack.append([a, k - 1])
                cur = "YY" + U
                continue
        while stack and stack[-1][1] == 0:
            p = stack.pop()
            val = "X" * p[0] + "Y" + val
        if not stack:
            return "OK", val, None
        stack[-1][1] -= 1
        cur = val


def classify(n):
    words = all_words(n)
    outs = run_visits(words, 10 ** 7)
    kinds = collections.Counter()
    halting = []
    for w, o in zip(words, outs):
        f = o.split()
        ev = Gctx(list(w))[0] == "EVENT"
        kinds[(f[0], "the recursion G reaches an event" if ev else "no event: G applies")] += 1
        if f[0] == "H":
            halting.append(w)
        elif f[0] == "V" and not ev:
            assert f[2] == "-2" and to_digits(f[3] if len(f) == 6 else "") == to_digits(
                "".join("11" if c == "Y" else "10" for c in Gctx(list(w))[1])), (w, o)
    print("words of at most %d pairs: %d" % (n, len(words)))
    for k, v in sorted(kinds.items()):
        print("  %-16s %-34s %d" % ({"H": "halt", "V": "next wall visit", "T": "TIMEOUT"}[k[0]], k[1], v))
    print("  (every visit without an event is an ordinary visit with the word G(S), checked)")
    H = set(halting)
    hits = sorted({w[1:] for w in halting if w[0] == 0}, key=lambda T: (plen((0,) + T), T))
    bad = [w for w in words if (w in H) != ((0,) + w[1:] in H) and plen((0,) + w[1:]) <= n]
    print("halting words: %d; halting depends only on the hit (the word after the first digit): %s" % (
        len(halting), "yes, for every word" if not bad else "NO: %s" % bad[:5]))
    prim = [T for T in hits if not (len(T) > 2 and T[2:] in set(hits))]
    print("halting hits (word T with Y^a X T halting for every a): %d; not inherited from the first sub-visit: %d"
          % (len(hits), len(prim)))
    print("  the shortest:", ", ".join(" ".join(map(str, T)) for T in prim[:12]))
    fn = os.path.join(HERE, "halting_hits_%d.txt" % n)
    with open(fn, "w") as f:
        f.write("".join(" ".join(map(str, T)) + "\n" for T in hits))
    print("wrote", os.path.relpath(fn))
    return words, outs


def innermost(n):
    words, outs = all_words(n), None
    outs = run_visits(words, 10 ** 7)
    two = True
    stats = {D: collections.defaultdict(lambda: [0, 0]) for D in (1, 2, 3, 4)}
    for w, o in zip(words, outs):
        f = o.split()
        if f[-2] != "ED":
            continue
        r = Gctx(list(w))
        assert r[0] == "EVENT", w
        if len(r[1]) != 2:
            two = False
        for D in stats:
            fr = tuple(rem for _, rem in r[2][::-1][:D]) + (("top",) if len(r[2]) < D else ())
            stats[D][(tuple(r[1]), fr)][f[0] == "H"] += 1
    print("every innermost event word has two digits:", two)
    for D, st in stats.items():
        mixed = sum(1 for v in st.values() if v[0] and v[1])
        print("  signature (a, b) + remaining sub-visits of the %d innermost frames: %d signatures, %d of them "
              "both halting and not" % (D, len(st), mixed))


def anatomy():
    sys.path.insert(0, HERE)
    from gmodel import M
    sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
    from bbtools.machine import Machine
    m = Machine.parse(M)

    def event_visit(a, b, gap=60, cap=10 ** 8):
        """X O^gap, then the wall, then the word (a, b): run to the first wall visit left of the wall"""
        c = cells([a, b])
        t = {i + 1: int(ch) for i, ch in enumerate(c)}
        t[-2 * gap - 1] = 1
        p, s, k = 0, 5, 0
        while k < cap:
            tr = m.table[s][t.get(p, 0)]
            if tr is None:
                return "halt", k, None
            t[p] = tr[0]; p += tr[1]; s = tr[2]; k += 1
            if s == 5 and p < 0 and t.get(p, 0) == 0 and t.get(p - 1, 0) == 0:
                hi = max(q for q, v in t.items() if v)
                return p, k, to_digits("".join(str(t.get(q, 0)) for q in range(p + 1, hi + 1)))
        return "cap", k, None

    print("event visit of the word (a, b) at a wall with 60 blank pairs to its left: the next wall visit")
    print("(offset in cells from the wall; -2 is an ordinary visit, -7 is 3.5 pairs on, in the other pair alignment)")
    for b in range(0, 21):
        row = []
        for a in range(0, 4):
            off, k, w = event_visit(a, b)
            row.append("%s %s" % (off, " ".join(map(str, w)) if w else ""))
        print("  b=%2d  " % b + "  |  ".join(row))
    offs = collections.Counter()
    halts = []
    for b in range(0, 61):
        for a in range(0, 4):
            off, k, w = event_visit(a, b)
            offs[(b <= 10, off)] += 1
            if off == "halt":
                halts.append((a, b))
    print("a <= 3, b <= 60: offsets by (b <= 10, offset):", dict(offs), "; halting:", halts)
    outs = run_visits([(0, b) for b in range(401)])
    print("the wall visit of X Y^b (the hit of a last digit b) halts for b <= 400 exactly at b =",
          [b for b, o in enumerate(outs) if o.startswith("H")])


class _Ev(Exception):
    pass


class _Halt(Exception):
    pass


GB = {}


def gword(b):
    """g(b): the word the event of a last digit b >= 11 leaves (the next wall visit of X Y^b, an ordinary visit)"""
    if b not in GB:
        f = run_visits([(0, b)])[0].split()
        assert f[0] == "V" and f[2] == "-2", (b, f)
        GB[b] = to_digits(f[3])
    return GB[b]


def Gx(ds):
    """the recursion G on digit lists, extended by the events with b >= 11: h(b) = g(b), h(13) halts"""
    def h(T):
        if len(T) == 1:
            if T[0] == 13:
                raise _Halt()
            if T[0] >= 11:
                return list(gword(T[0]))
            raise _Ev()
        k, U = T[0], T[1:]
        if k == 0:
            return [3 + U[0]] + U[1:]
        W = [2 + U[0]] + U[1:]
        for _ in range(k):
            W = G(W)
        return [1 + W[0]] + W[1:]

    def G(d):
        return [0] * d[0] + [2] if len(d) == 1 else [0] * d[0] + h(d[1:])
    return G(ds)


def rule11(seed):
    import random
    random.seed(seed)
    ws = []
    while len(ws) < 4000:
        w = [random.choice([0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 8, 9]) for _ in range(random.randint(1, 8))]
        w.append(random.randint(11, 45))
        try:
            Gx(w)
            ws.append(tuple(w))
        except _Halt:
            ws.append(tuple(w))
        except (_Ev, RecursionError):
            pass
    outs = run_visits(ws)
    c = collections.Counter()
    for w, o in zip(ws, outs):
        f = o.split()
        try:
            pred = ("V", "-2", tuple(Gx(list(w))))
        except _Halt:
            pred = ("H",)
        act = ("H",) if f[0] == "H" else (("V", f[2], tuple(to_digits(f[3]) or ())) if f[0] == "V" else ("?",))
        c["agree" if act == pred else "DISAGREE"] += 1
        if act != pred:
            print("disagree:", w, pred, act)
    print("4,000 random words whose events all have b >= 11 (%d of them halt): %s" % (
        sum(1 for o in outs if o.startswith("H")), dict(c)))


def hits(fn):
    T = [tuple(map(int, l.split())) for l in open(fn) if l.strip()]
    outs = run_visits([(0,) + t for t in T])
    for t, o in zip(T, outs):
        f = o.split()
        if f[0] == "V":
            w = to_digits(f[3]) if len(f) == 6 else []
            res = "next wall visit at cell %s (%s) after %s steps: %s" % (
                f[2], "ordinary" if f[2] == "-2" else "NOT ordinary", f[1],
                " ".join(map(str, w)) if w is not None else "not a word of pairs: " + f[3])
        else:
            res = "HALTS" if f[0] == "H" else "no result"
        print("%s : %s" % (" ".join(map(str, t)), res))
    print("%d hit words, %d halt" % (len(T), sum(o.startswith("H") for o in outs)))


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "classify":
        classify(int(sys.argv[2]))
    elif cmd == "anatomy":
        anatomy()
    elif cmd == "hits":
        hits(sys.argv[2])
    elif cmd == "rule11":
        rule11(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    elif cmd == "innermost":
        innermost(int(sys.argv[2]))
