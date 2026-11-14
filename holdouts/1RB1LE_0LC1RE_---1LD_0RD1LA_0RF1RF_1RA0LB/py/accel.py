"""An exact accelerated simulator of this machine: the regular levels of the ladder are stripped ("peeled") and only
the front and the tail are simulated.  It finds that the machine HALTS, and the exact step.

Words of pairs and digits are as in words.py.  At every second visit the word is

    front  4^n1 s1  4^n2 s2  ...  4^nk sk  tail

where the front is `2 1` (the next visit will make an *H-hit* on the rest) or `5` (a *V-hit*), `4^n s` is a *level*
(a rung of n >= 1 blocks `4` = Y Y Y Y X and a separator s, one of 8 words) and the tail is whatever is left, down to
the left edge of the tape.  A hit on a level does one of two things, by the table CYC below (16 positions = separator
and kind of hit; the level steps through them in order):

  * it is absorbed: the separator changes, at 4 of the positions the rung gains a block, the rest is not touched;
  * it is passed on (6 positions, PASS): the same, and the rest gets a hit, of the kind given in PASS.

A hit on the rest is a fixed list of calls: the head crosses the boundary into the rest in a state and comes back
in a state (SIG: `<C>E` for a V-hit, `<C>E<E>F<B>E<C>A<D>E` for an H-hit).  Everything a level does depends on the
rest only through the states in which these calls return.  So the rest of a level lives exactly as it would with
the front put directly in front of it, only more slowly, and this holds level after level.  The simulator therefore
keeps the levels as a list of (position, n) with exact arithmetic, and runs the machine itself only on the *reduced
word* front + tail (cell by cell, words.visit).  When the calls on the tail come back in other states (an
*irregular* hit), the deepest level is put back into the reduced word and the hit is tried again.

Step counts: a hit on a level at position p with n blocks takes LA[p] * n + LB[p] steps inside the level, the front
takes FC steps per hit (the bounce visit included), and the tail's steps are counted in the reduced run.

    python3 accel.py [--defer J]      the run from blank tape to the halt (J deepest levels kept in the reduced word)
    python3 accel.py levels           the level table, the call lists and all step constants, against the machine
    python3 accel.py check FILE       visit numbers and step counts against a direct run (output of ../c/visits.c)
    python3 accel.py tails N          the first N tails after the reset (visit 3,006)
    python3 accel.py last             the last visit on small tapes with the same levels: direct run against formula
"""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from words import visit, fmt, d2w, FIRST

CYC = [("0 1 0 1", "H"), ("0 3 1", "V"), ("7 1", "H"), ("5 3", "V"), ("0 6", "H"), ("0 1 0 1", "V"), ("5 0 1", "H"),
       ("7 1", "V"), ("0 1 3", "H"), ("0 6", "V"), ("10", "H"), ("5 0 1", "V"), ("0 3 1", "H"), ("0 1 3", "V"),
       ("5 3", "H"), ("10", "V")]
PASS = {2: "H", 4: "V", 7: "H", 10: "V", 12: "H", 15: "V"}     # passing position -> kind of hit passed on
INC = {3, 7, 11, 15}                                           # a hit at these positions adds a block to the rung
POS = {c: i for i, c in enumerate(CYC)}
SEPW = {s: d2w([int(x) for x in s.split()]) + "X" for s, _ in CYC}
FRONT = {"H": "YYXYX", "V": "YYYYYX"}                          # `2 1` and `5`
OTHER = {"H": "V", "V": "H"}
SIG = {"H": "<C>E<E>F<B>E<C>A<D>E", "V": "<C>E"}
BLOCK = "YYYYX"
# steps inside a level per hit: LA[p] * n + LB[p]; steps of the front per hit (with the bounce visit)
LA = {p: (112 if CYC[p][1] == "H" else 56) for p in range(16)}
LB = {0: 21, 1: 5, 2: 168, 3: 45, 4: 88, 5: 5, 6: 77, 7: 136, 8: 21, 9: 5, 10: 144, 11: 45, 12: 112, 13: 5, 14: 77,
      15: 112}
FC = {"H": 107, "V": 83}
# a visit that never comes back: steps inside a passing level before its k-th call on the rest, (a, b) for a n + b,
# and the number of the call from above during which that happens; steps of the front before its k-th call
PART = {(2, 1): (24, 48, 1), (2, 2): (24, 91, 1), (2, 3): (24, 92, 1), (2, 4): (24, 95, 1), (2, 5): (24, 98, 1),
        (4, 1): (80, 49, 4), (7, 1): (24, 48, 1), (7, 2): (24, 91, 1), (7, 3): (24, 92, 1), (7, 4): (24, 95, 1),
        (7, 5): (24, 98, 1), (10, 1): (24, 60, 1), (12, 1): (80, 37, 4), (12, 2): (80, 80, 4), (12, 3): (80, 81, 4),
        (12, 4): (80, 84, 4), (12, 5): (80, 87, 4), (15, 1): (24, 60, 1)}
FP = {"H": (23, 66, 67, 70, 73), "V": (35,)}


def adv(pos, n, y):
    """a level at (pos, n) after y hits"""
    q, r = divmod(y, 16)
    n += 4 * q
    for _ in range(r):
        if pos in INC:
            n += 1
        pos = (pos + 1) % 16
    return pos, n


def need(pos, x):
    """the number of hits a level at pos must get until it has passed on x of them"""
    if x == 0:
        return 0
    q, r = divmod(x - 1, 6)
    y = 16 * q
    r += 1
    while r:
        if pos in PASS:
            r -= 1
        pos = (pos + 1) % 16
        y += 1
    return y


def lcost(pos, n, y):
    """steps made inside a level at (pos, n) during its next y hits"""
    q, r = divmod(y, 16)
    tot = 0
    if q:
        d = inc = 0
        p = pos
        for _ in range(16):
            d += LA[p] * inc + LB[p]
            if p in INC:
                inc += 1
            p = (p + 1) % 16
        tot = q * (1344 * n + d) + 1344 * 4 * (q * (q - 1) // 2)
        n += 4 * q
    p = pos
    for _ in range(r):
        tot += LA[p] * n + LB[p]
        if p in INC:
            n += 1
        p = (p + 1) % 16
    return tot


def ftype(w):
    if w.startswith(FRONT["H"]):
        return "H", w[5:]
    if w.startswith(FRONT["V"]):
        return "V", w[6:]
    return None, None


def next_pass(pos):
    while pos not in PASS:
        pos = (pos + 1) % 16
    return pos


def try_peel(rest):
    m = re.match(r"^((?:YYYYX)+)", rest)
    if not m:
        return None
    n = len(m.group(1)) // 5
    rest = rest[5 * n:]
    for s, w in SEPW.items():
        if rest.startswith(w):
            return n, s, rest[len(w):]
    return None


class Halt(Exception):
    pass


class Accel:
    def __init__(self, word, visits, steps, defer=0):
        self.levels = []                # peeled levels [pos, n], outermost first
        self.R = word                   # the reduced word: front + what is not peeled
        self.visits, self.steps, self.hits, self.unpeels, self.defer = visits, steps, 0, 0, defer

    def parse(self):
        """the levels readable at the front of the reduced word, the kind of hit the tail gets next, the tail"""
        t, rest = ftype(self.R)
        out = []
        while t:
            pr = try_peel(rest)
            if not pr:
                break
            n, s, rest = pr
            pos = POS[(s, t)]
            out.append((pos, n))
            t = PASS[next_pass(pos)]
        return out, t, rest

    def all_levels(self):
        lv, t, tail = self.parse()
        return [tuple(x) for x in self.levels] + lv, tail

    def peel(self):
        lv, t, tail = self.parse()
        k = len(lv) - self.defer
        if k <= 0:
            return
        self.levels += [list(x) for x in lv[:k]]
        rest = "".join(BLOCK * n + SEPW[CYC[p][0]] for p, n in lv[k:]) + tail
        self.R = FRONT[PASS[next_pass(lv[k - 1][0])]] + rest

    def ready(self):
        """the visits until every peeled level stands at a passing position (so that the next hit reaches the
        reduced word); deepest level first, each level's hits are the hits the level above must pass on"""
        e = 0
        for k in range(len(self.levels) - 1, -1, -1):
            p0, n0 = self.levels[k]
            y = need(p0, e)
            pos, n = adv(p0, n0, y)
            d = next_pass(pos) - pos
            d += 16 if d < 0 else 0
            self.levels[k] = list(adv(pos, n, d))
            e = y + d
            self.steps += lcost(p0, n0, e)
            if k == 0:
                nh = (e + 1) // 2 if CYC[p0][1] == "H" else e // 2
                self.steps += FC["H"] * nh + FC["V"] * (e - nh)
        self.visits += 2 * e

    def hit(self):
        """one hit on the reduced word; None, or ("irregular", ...) with the state just before the visit"""
        self.ready()
        t, rest = ftype(self.R)
        bnd = -2 * len(FRONT[t])
        w1, n1, info = visit(self.R, bnd)
        if w1 is None:
            self.fatal = (t, info)
            raise Halt()
        if info["sig"] != SIG[t]:
            return ("irregular", t, info["sig"])
        w2, n2, info2 = visit(w1)
        assert n2 == 8 and ftype(w2)[0] == OTHER[t] and n1 - info["left"] + n2 == FC[t]
        self.steps += info["left"] + FC[CYC[self.levels[0][0]][1] if self.levels else t]
        for lev in self.levels:
            self.steps += LA[lev[0]] * lev[1] + LB[lev[0]]
            lev[0], lev[1] = adv(lev[0], lev[1], 1)
        self.visits += 2
        self.hits += 1
        self.R = w2
        return None

    def unpeel(self):
        pos, n = self.levels.pop()
        self.unpeels += 1
        t, rest = ftype(self.R)
        assert pos in PASS and PASS[pos] == t and n < 10 ** 7
        self.R = FRONT[CYC[pos][1]] + BLOCK * n + SEPW[CYC[pos][0]] + rest

    def step(self):
        """to the state after the next hit on the reduced word"""
        self.peel()
        while True:
            r = self.hit()
            if r is None:
                return
            if not self.levels:
                raise RuntimeError("irregular hit with nothing peeled: %r at visit %d" % (r, self.visits))
            self.unpeel()

    def halting_step(self):
        """after Halt: the step of the halt (the halting transition counted, as bbchallenge does)"""
        t, info = self.fatal
        k = info["sig"].count("<")           # the call on the reduced rest that does not come back
        tot = info["left"]                   # steps in the reduced rest before the halting transition
        for pos, n in reversed(self.levels):
            a, b, kin = PART[(pos, k)]
            tot += a * n + b
            k = kin
        tot += FP[CYC[self.levels[0][0]][1] if self.levels else t][k - 1]
        return self.steps + tot + 1


def start(v0, defer=0):
    """the direct run from blank tape to visit v0"""
    w, st = FIRST
    for v in range(2, v0 + 1):
        w, n, info = visit(w)
        st += n
    return Accel(w, v0, st, defer)


START = 3040      # after the reset at visit 3,006 (step 27,167,343); before it the direct run is used


def run(defer=0, quiet=False):
    a = start(START, defer)
    try:
        while True:
            a.step()
    except Halt:
        pass
    return a


def cmd_run(argv):
    defer = int(argv[argv.index("--defer") + 1]) if "--defer" in argv else 0
    a = run(defer)
    lv, tail = a.all_levels()
    t, info = a.fatal
    h = a.halting_step()
    print("direct run to visit %d; then %d hits on the reduced word (%d levels put back after an irregular hit)"
          % (START, a.hits, a.unpeels))
    print("at the last visit: %d levels, tail %s (down to the blank left end)" % (len(lv), fmt(tail)))
    print("outermost level: position %d (separator %s), n = %d" % (lv[0][0], CYC[lv[0][0]][0], lv[0][1]))
    print("the visit after visit number\n  %d\ndoes not come back: the machine halts in state %s, %d cells left of "
          "the leftmost 1" % (a.visits, info["halt"], info["edge"] - info["pos"]))
    print("HALT at step (bbchallenge count)\n  %d" % h)
    print("(%d digits; the visit number has %d digits)" % (len(str(h)), len(str(a.visits))))
    return a


# ------------------------------------------------------------------ tests against the machine
def dv(w, b):
    """a hit and the bounce: word, steps, steps left of b during the hit, crossings of b, their times"""
    w1, n1, i1 = visit(w, b)
    assert w1 is not None
    w2, n2, i2 = visit(w1)
    assert n2 == 8
    return w2, n1 + n2, i1["left"], i1["sig"], i1["times"]


def sample_rests(count, lo=300, hi=6000):
    import random
    out = []
    w = FIRST[0]
    for v in range(2, hi):
        w = visit(w)[0]
        t, rest = ftype(w)
        if v > lo and t and v % 97 in (0, 1):
            out.append(rest)
    random.seed(5)
    return random.sample(out, count)


def left_before(ct, tau):
    """steps made left of a boundary before time tau, from the crossing times ct"""
    left = 0
    for i in range(0, len(ct) - 1, 2):
        if ct[i] > tau:
            break
        left += min(ct[i + 1], tau) - ct[i]
    return left


def cmd_levels(argv):
    rests = sample_rests(12)
    ns = list(range(1, 25)) + [40, 77, 200, 1000]
    cost, front, part, fpart = {}, {}, {}, {}
    cases = 0
    for pos, (s, t) in enumerate(CYC):
        for n in ns:
            for u in rests + [""]:
                if u == "" and pos in PASS:
                    continue               # the blank rest stands for "never entered"
                w = FRONT[t] + BLOCK * n + SEPW[s] + u
                b1 = -2 * len(FRONT[t])
                b2 = b1 - 2 * (5 * n + len(SEPW[s]))
                w2, tot, l1, sig1, c1 = dv(w, b1)
                _, _, l2, sig2, c2 = dv(w, b2)
                assert sig1 == SIG[t]
                n2, s2 = n + (pos in INC), CYC[(pos + 1) % 16][0]
                if pos in PASS:
                    t2 = PASS[pos]
                    assert sig2 == SIG[t2]
                    r2 = dv(FRONT[t2] + u, -2 * len(FRONT[t2]))
                    assert r2[3] == SIG[t2] and r2[2] == l2
                    uexp = r2[0][len(FRONT[OTHER[t2]]):]
                    for k in range(len(c2) // 2):                 # before the (k+1)-th call on the rest
                        tau = c2[2 * k]
                        inside = left_before(c1 + [tau], tau) - left_before(c2, tau - 1)
                        kin = sum(1 for i in range(0, len(c1), 2) if c1[i] <= tau)
                        part.setdefault((pos, k + 1, n), set()).add((inside, kin))
                    fpart.setdefault(t, set()).add(tuple(c1[2 * k] - left_before(c1, c1[2 * k] - 1)
                                                         for k in range(len(c1) // 2)))
                else:
                    assert sig2 == ""
                    uexp = u
                assert w2 == FRONT[OTHER[t]] + BLOCK * n2 + SEPW[s2] + uexp, (pos, n)
                cost.setdefault((pos, n), set()).add(l1 - l2)
                front.setdefault(t, set()).add(tot - l1)
                cases += 1
    for pos in range(16):
        for n in ns:
            assert cost[(pos, n)] == {LA[pos] * n + LB[pos]}
    assert front == {"H": {FC["H"]}, "V": {FC["V"]}} and fpart == {"H": {FP["H"]}, "V": {FP["V"]}}
    for (pos, k, n), v in part.items():
        a, b, kin = PART[(pos, k)]
        assert v == {(a * n + b, kin)}
    assert {(p, k) for p, k, n in part} == set(PART)
    print("the level table (CYC, PASS, INC), the call lists (SIG) and the step constants (LA, LB, FC, PART, FP) hold "
          "on %d cases:\n16 positions, n = 1..24, 40, 77, 200, 1000, 12 rests taken from the run (and the blank rest "
          "at the positions that do not pass)" % cases)


def cmd_check(argv):
    real = dict(tuple(map(int, line.split())) for line in open(argv[0]) if line[0].isdigit())
    for defer, v0 in ((0, START), (2, START), (1, 600)):
        a = start(v0, defer)
        ok = 0
        try:
            while a.visits <= max(real):
                a.step()
                if a.visits in real:
                    assert real[a.visits] == a.steps, (defer, a.visits)
                    ok += 1
        except RuntimeError as e:            # the reset: an irregular hit that reaches the front
            print("  (from visit %d: %s)" % (v0, e))
        print("from visit %d with %d levels kept: the step counts at %d visits (up to visit %d, step %d) equal the "
              "direct run's" % (v0, defer, ok, a.visits, a.steps))


def cmd_tails(argv):
    a = start(START)
    for i in range(int(argv[0])):
        a.step()
        lv, tail = a.all_levels()
        print("%4d  visit %d  levels %d  tail %s" % (a.hits, a.visits, len(lv), fmt(tail)[:110]))


def cmd_last(argv):
    a = run(0)
    lv, tail = a.all_levels()
    t, info = a.fatal
    for trial in range(8):
        small = [[pos, 1 + (i * 7 + trial * 3) % (2 + trial)] for i, (pos, n) in enumerate(lv)]
        w = FRONT[CYC[small[0][0]][1]] + "".join(BLOCK * n + SEPW[CYC[pos][0]] for pos, n in small) + tail
        res = visit(w)
        b = Accel(FRONT[t] + tail, 0, 0)
        b.levels, b.fatal = small, a.fatal
        assert res[0] is None and res[2]["halt"] == "C" and res[2]["pos"] == res[2]["edge"] - 2
        assert res[1] + 1 == b.halting_step(), trial
    print("8 tapes with the %d levels at their final positions, block counts 1..9, and the final tail: the direct "
          "run halts in C at the left edge after exactly the steps of the formula" % len(lv))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] in ("levels", "check", "tails", "last"):
        globals()["cmd_" + sys.argv[1]](sys.argv[2:])
    else:
        cmd_run(sys.argv[1:])
