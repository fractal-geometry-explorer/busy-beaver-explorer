"""Exact round engine and counter jumps for 1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF (21 November 2026).

Sample points ("round starts"): state B on the leftmost visited cell, the tape from the head reading 0 1^7 0 ...
(the prefix form P_b; c/pbvis.c prints them from a direct run).  At a round start the tape is

    P  (w1)^n1 L1  (w2)^n2 L2  ...  (wK)^nK LK  0^inf

with P a fixed literal, w_i a 6-cell wall word (110101 or a rotation), n_i large, and L_i a literal (the digit of
unit i, the frozen stretch behind it; LK holds the young end of the chain and runs to the blank tape).

A *round* is the run from one round start to the next.  It is computed by symbolic execution
(tools/py/bbtools/symtm.py) on the window P (w1)^(x1+T) L1 ... (wd)^(xd+T) Ld CTX, every wall count a variable,
the rest of the tape an opaque context; if the run touches the context the window grows by one unit (d+1), and a
round that reaches the blank end is run on the whole tape (tail round).  The result (new literals, new counts as
x_i + const, steps as an affine function of the x_i) holds for every value of the variables, so it is cached by the
window's literals and words.  Every number below is a machine run; nothing is fitted.

The counter jump.  A round of depth d changes units 1..d only.  From the rounds run so far the engine keeps, for
each unit i, literal L and lower context (P and the states of the units below), the hit record: L -> L', n_i +=
delta, the coefficient of n_i in the step count, and whether the hit stops at unit i (the round's constant step
count is charged to this hit) or carries on.  With complete cycles of records for units 1..j the engine computes E,
the number of rounds before the next round of depth > j (base-4 arithmetic).  Before it applies those E-1 rounds in
closed form (arithmetic series) it runs every kind of round the jump uses (depth d, the units below at their carry
inputs, unit d at each stop position of its cycle) by symbolic execution and compares the result with the records
(words, literals, count changes, step coefficients); a kind that does not match cuts the jump down to the depths
below it.  Counts stay >= T in every hit of a jump (otherwise the jump is shortened).

Resets (drun).  At step 1,368,863,940,823,250 the first counter overflows: its young walls are rebuilt as blocks
of 1s, F erases them into blank stretches, and a new counter with the same prefix grows leftwards in front of a
blank stretch (an inner round start: B, at least ZMIN zeros on its left, then 0 1^7 0).  The Driver runs such a
counter with the stretch as its left end, never letting it grow over the stretch, and runs whole-tape rounds
(symbolic, with the part right of the deepest symbolic wall run cell by cell by c/tailsim.c) when a round leaves
the counter.  Walls of 8-cell words (10101110 and rotations) and blocks of >= ONES 1s are units too.

usage:
  python3 units.py test                          check against direct simulation (c/pbvis.c)
  python3 units.py test START NROUND NROUND2     e.g. test 3e8 300 13000
  python3 units.py drun START SECONDS MAXDIG CKPT  the run with resets, checkpoints in CKPT (pickle)
  python3 units.py run START_STEP SECONDS [MAXDIG]   from the round start after START_STEP (direct run), jump on
"""
import os, sys, time, subprocess, json, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
from bbtools import symtm
from bbtools.symtm import Rep, Lin, Blank, Ctx, Config
from bbtools.machine import Machine

M = '1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF'
MACH = Machine.parse(M)
QB = 1
T0 = 12          # a wall is a run of >= T0 copies; its count is written x + T0 in the symbolic window
PB = (0, 1, 1, 1, 1, 1, 1, 1, 0)
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def primitive(w):
    n = len(w)
    return all(w != w[k:] + w[:k] for k in range(1, n) if n % k == 0)


ONES = 1000      # a block of at least ONES 1s is a wall of the word 1
WL = (6, 8)      # word lengths of walls (6: the walls of the first counter; 8: (10101110)^n, after the first reset)


def find_walls(cells, minrep=T0):
    """cells: tuple of 0/1.  Returns list of (start, word, count) of maximal runs of a primitive word of WL cells with
    at least minrep copies, leftmost start first."""
    out = []
    i, n = 0, len(cells)
    while i + 6 * minrep <= n:
        if cells[i] == 1 and cells[i:i + ONES] == (1,) * ONES:
            # a long block of 1s (a crushed wall) is a wall of the word 1
            k = ONES
            while i + k < n and cells[i + k] == 1:
                k += 1
            out.append((i, (1,), k))
            i += k
            continue
        for L in WL:
            w = cells[i:i + L]
            if len(w) == L and primitive(w) and cells[i:i + L * minrep] == w * minrep:
                k = minrep
                while cells[i + L * k:i + L * k + L] == w:
                    k += 1
                out.append((i, w, k))
                i += L * k
                break
        else:
            i += 1
    return out


class State:
    """P (literal), units: list of [word, n, lit]; lit of the last unit runs to the blank end."""
    def __init__(self, P, units, steps):
        self.P, self.units, self.steps = tuple(P), [list(u) for u in units], steps

    @staticmethod
    def from_cells(cells, steps, minrep=T0):
        cells = tuple(int(c) for c in cells)
        ws = find_walls(cells, minrep)
        if not ws:
            raise ValueError('no wall')
        P = cells[:ws[0][0]]
        units = []
        for j, (s, w, k) in enumerate(ws):
            e = ws[j + 1][0] if j + 1 < len(ws) else len(cells)
            units.append([w, k, cells[s + len(w) * k:e]])
        st = State(P, units, steps)
        st.normalize()
        return st

    def normalize(self):
        """canonical form: each wall starts as far left as possible (as symtm.canon), full copies absorbed;
        trailing zeros of the last literal dropped."""
        toks = list(self.P)
        for i, (w, n, lit) in enumerate(self.units):
            toks.append(Rep(tuple(w), Lin('x%d' % i)))
            toks.extend(lit)
        toks.append(Blank())
        cn = absorb(symtm.canon(toks))
        P, units = split_units(cn)
        assert len(units) == len(self.units)
        new = []
        for i, ((w, cnt, lit), (_, n, _)) in enumerate(zip(units, self.units)):
            assert cnt.c == {'x%d' % i: 1}, cnt
            new.append([w, n + cnt.k, lit])
        self.P, self.units = P, new

    def cells(self):
        out = list(self.P)
        for w, n, lit in self.units:
            out += list(w) * n + list(lit)
        while out and out[-1] == 0:
            out.pop()
        return tuple(out)

    def show(self, full=False):
        s = []
        for w, n, lit in self.units:
            s.append('(%s)^%s [%d]' % (''.join(map(str, w)), fmt(n), len(lit)))
        return ' '.join(s)


def fmt(n):
    s = str(n)
    return s if len(s) < 16 else '%s..e%d' % (s[:6], len(s) - 1)


def absorb(toks):
    """merge literal copies of w right after Rep(w, x) into the count (canon expands constant parts)"""
    out = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if isinstance(t, Rep) and not t.n.is_const():
            w = t.word; L = len(w); n = t.n; i += 1
            while i + L <= len(toks) and all(isinstance(x, int) for x in toks[i:i + L]) and tuple(toks[i:i + L]) == w:
                n = n + 1; i += L
            out.append(Rep(w, n))
        else:
            out.append(t); i += 1
    return out


def split_units(toks):
    """tokens (canonical, ending in Blank or Ctx) -> P, [(word, Lin, lit)], end token"""
    P = []
    i = 0
    while i < len(toks) and isinstance(toks[i], int):
        P.append(toks[i]); i += 1
    units = []
    while i < len(toks) and isinstance(toks[i], Rep):
        r = toks[i]; i += 1
        lit = []
        while i < len(toks) and isinstance(toks[i], int):
            lit.append(toks[i]); i += 1
        units.append((r.word, r.n, tuple(lit)))
    rest = toks[i:]
    if len(rest) != 1 or not isinstance(rest[0], (Blank, Ctx)):
        raise ValueError('unparsed tokens %r' % (rest[:5],))
    if isinstance(rest[0], Blank):
        while units and units[-1][2] and units[-1][2][-1] == 0:
            units[-1] = (units[-1][0], units[-1][1], units[-1][2][:-1])
    return tuple(P), units


def is_start(c):
    if c.state != QB or c.left != [Blank()]:
        return False
    r = c.right
    if len(r) < 9 or not all(isinstance(x, int) for x in r[:9]):
        return False
    return tuple(r[:9]) == PB


class NeedFull(Exception):
    pass


class Engine:
    conc_steps = 0
    driver_full = False
    def __init__(self):
        self.memo = {}
        self.nsym = 0
        self.carry = {}      # (unit, word, lit, lower context) -> hit record of a carry through the unit
        self.stop = {}       # (unit, word, lit, lower context) -> hit record of a round that stops at the unit
        self.rounds = 0      # rounds applied (explicit + jumped)
        self.explicit = 0
        self.conflicts = 0
        self.norecord = False
        self.vcache = {}

    # ------------------------------------------------------------ one round, symbolic
    def round_rule(self, st, d, full=False, conc=0):
        """symbolic round on the window of the first d units followed by an opaque context, or (full) on the whole
        tape; with conc = c > 0 the deepest c units of the window have their counts written out (concrete)."""
        key = (st.P, tuple((u[0], u[2]) for u in st.units[:d]), full, conc,
               tuple(u[1] for u in st.units[d - conc:d]) if conc else ())
        if key in self.memo:
            return self.memo[key]
        toks = list(st.P)
        for i, (w, n, lit) in enumerate(st.units[:d]):
            toks.append(Rep(tuple(w), Lin('x%d' % i) + T0 if i < d - conc else Lin(n)))
            toks.extend(lit)
        toks.append(Blank() if full else Ctx('R'))
        c = Config([Blank()], QB, toks)
        self.nsym += 1
        try:
            c = symtm.run(MACH, c, lambda c: not c.steps.is_zero() and is_start(c), max_moves=300000 if full else 1000000, rotate=True)
        except symtm.TouchContext:
            res = ('touch',)
        except symtm.Halted as e:
            res = ('halt', str(e), repr(c)[:3000])
        except symtm.NeedSplit as e:
            res = ('split', str(e))
        except RuntimeError as e:
            res = ('limit', str(e)[:200], c)
        else:
            raw = tok_len(c.right)
            cn = absorb(symtm.canon(c.right))
            P, units = split_units(cn)
            res = ('ok', P, units, c.steps, raw)
        if conc == 0 and not full:
            self.memo[key] = res
        return res

    def hybrid_rule(self, st, conc, cmax=2 * 10**11):
        """a whole-tape round in which the part right of the deepest symbolic wall is run concretely by
        c/tailsim.c (exact, cell by cell); conc deepest units written out.  Same result format as round_rule."""
        d = len(st.units)
        toks = list(st.P)
        for i, (w, n, lit) in enumerate(st.units):
            toks.append(Rep(tuple(w), Lin('x%d' % i) + T0 if i < d - conc else Lin(n)))
            toks.extend(lit)
        toks.append(Blank())
        c = Config([Blank()], QB, toks)
        self.nsym += 1
        r = hybrid_run(c, lambda c: not c.steps.is_zero() and is_start(c), cmax)
        if r[0] != 'ok':
            return r
        c = r[1]
        raw = tok_len(c.right)
        cn = absorb(symtm.canon(c.right))
        P, units = split_units(cn)
        return ('ok', P, units, c.steps, raw)

    def do_round(self, st):
        """apply one round to st exactly (in place); returns (depth, full, conc)."""
        nu = len(st.units)
        d = 1
        full = False
        conc = 0
        while True:
            r = self.round_rule(st, d, full, conc)
            if r[0] == 'touch':
                if d < nu:
                    d += 1
                    continue
                if not full:
                    if self.driver_full:
                        raise NeedFull()
                    full = True
                    continue
            if r[0] in ('split', 'limit') and full:
                # whole-tape round: concrete simulation right of the deepest symbolic wall
                for conc in range(0, d):
                    r = self.hybrid_rule(st, conc)
                    if r[0] != 'split':
                        break
                break
            if r[0] == 'split' and conc < d:
                conc += 1
                continue
            if r[0] == 'limit' and not full:
                # the window round does not end within the move limit: run the whole tape instead
                if self.driver_full:
                    raise NeedFull()
                full = True
                continue
            break
        if r[0] == 'halt':
            print('HALT in a round from step', st.steps, ':', r[1], r[2], flush=True)
            raise RuntimeError('HALT in round: %s' % (r[1],))
        if r[0] != 'ok':
            self.failed = (r, d, full, conc)
            raise RuntimeError('round failed: %r depth %d' % (r[:2], d))
        _, P, units, steps, raw = r
        env = {'x%d' % i: st.units[i][1] - T0 for i in range(d - conc)}
        before = len(st.P) + sum(len(u[0]) * u[1] + len(u[2]) for u in (st.units if full else st.units[:d]))
        self.growth = raw.subs(env) - before   # exact for a window round; an upper bound for a whole-tape round
        old = [list(u) for u in st.units]
        old_P = st.P
        st.steps += steps.subs(env)
        if conc:
            toks = list(P)
            for (w, cnt, lit) in units:
                toks.append(Rep(tuple(w), Lin(cnt.subs(env))))
                toks.extend(lit)
            for (w, n, lit) in st.units[d:]:
                toks.append(Rep(tuple(w), Lin(n)))
                toks.extend(lit)
            toks.append(Blank())
            new = state_from_tokens(toks, {}, st.steps)
            st.P, st.units = new.P, new.units
            self.rounds += 1
            self.explicit += 1
            return d, full, conc
        newunits = []
        pending = list(P)   # literal cells not yet attached to a unit
        newP = None
        for j, (w, cnt, lit) in enumerate(units):
            if cnt.is_const():
                # a written-out wall: back to literal cells
                pending += list(w) * cnt.k + list(lit)
                continue
            (v, a1), = cnt.c.items()
            assert a1 == 1
            i = int(v[1:])
            if newP is None:
                newP = tuple(pending)
            else:
                newunits[-1][2] = tuple(newunits[-1][2]) + tuple(pending)
            pending = list(lit)
            newunits.append([w, cnt.subs(env), tuple(lit), i])
            newunits[-1][2] = ()
        if newP is None:
            raise RuntimeError('no wall left after the round')
        newunits[-1][2] = tuple(pending)
        ids = [u[3] for u in newunits]
        assert ids == list(range(len(ids))), ids
        if not full:
            # the window's units only; the units beyond it are untouched
            assert len(newunits) == d - conc or conc, (len(newunits), d)
            if conc:
                # units d-conc..d-1 dissolved into the literal of the last symbolic unit
                pass
            rest = [list(u) for u in st.units[d:]]
        else:
            rest = []
        st.P = newP
        st.units = [u[:3] for u in newunits] + rest
        nbefore = len(st.units)
        self.demote(st)
        self.promote_all(st)
        self.last = (d, full, conc, steps)
        if not full and not conc and len(st.units) == nbefore and not self.norecord:
            # record hit info for units 0..d-1
            for i in range(d):
                w, n0, lit0 = old[i]
                a = steps.c.get('x%d' % i, 0)
                rec = dict(kind='stop' if i == d - 1 else 'carry', newlit=tuple(st.units[i][2]),
                           newword=tuple(st.units[i][0]), delta=st.units[i][1] - n0, a=a)
                if i == d - 1:
                    # steps = sum a_i x_i + k = sum a_i n_i + (k - T0 sum a_i)
                    rec['b'] = steps.k - T0 * sum(steps.c.values())
                    key = (i, tuple(w), tuple(lit0), (old_P, tuple((tuple(u[0]), tuple(u[2])) for u in old[:i])))
                    tab = self.stop
                else:
                    key = (i, tuple(w), tuple(lit0), (old_P, tuple((tuple(u[0]), tuple(u[2])) for u in old[:i])))
                    tab = self.carry
                o = tab.get(key)
                if o is None:
                    tab[key] = rec
                elif o != rec:
                    # the record depends on more context than its key: keep the newest one (every round a jump
                    # uses is checked by verify_depth before the jump, so a stale record only stops jumps)
                    tab[key] = rec
                    self.conflicts += 1
        self.rounds += 1
        self.explicit += 1
        return d, full, conc

    def demote(self, st):
        """a wall with fewer than T0 copies is no longer a unit: written out into the literal before it"""
        i = 1
        changed = False
        while i < len(st.units):
            w, n, lit = st.units[i]
            if n < T0:
                pw, pn, plit = st.units[i - 1]
                st.units[i - 1] = [pw, pn, tuple(plit) + tuple(w) * n + tuple(lit)]
                del st.units[i]
                changed = True
            else:
                i += 1
        assert st.units[0][1] >= T0
        if changed:
            st.normalize()

    def promote_all(self, st):
        """split walls of >= 2*T0 copies out of every literal"""
        units = []
        wp = find_walls(tuple(st.P), 2 * T0)
        if wp:
            # a wall grew inside P: it becomes unit 0 (the unit indices shift, so the hit records are dropped)
            P = tuple(st.P)
            first = [list(x) for x in st.units]
            pieces = []
            for j, (s0, w2, k) in enumerate(wp):
                e = wp[j + 1][0] if j + 1 < len(wp) else len(P)
                pieces.append([w2, k, P[s0 + len(w2) * k:e]])
            st.P = P[:wp[0][0]]
            st.units = pieces + first
            self.carry.clear(); self.stop.clear()
            st.normalize()
        for w, n, lit in st.units:
            ws = find_walls(tuple(lit), 2 * T0)
            cur = [w, n, tuple(lit[:ws[0][0]]) if ws else tuple(lit)]
            units.append(cur)
            for j, (s0, w2, k) in enumerate(ws):
                e = ws[j + 1][0] if j + 1 < len(ws) else len(lit)
                units.append([w2, k, tuple(lit[s0 + len(w2) * k:e])])
        if len(units) != len(st.units):
            st.units = units
            st.normalize()

    def promote(self, st):
        """after a tail round: split new walls out of the last literal (runs of >= T0 copies)"""
        w, n, lit = st.units[-1]
        ws = find_walls(tuple(lit), 2 * T0)
        if not ws:
            return
        units = st.units[:-1]
        cur = [w, n, lit[:ws[0][0]]]
        units.append(cur)
        for j, (s, w2, k) in enumerate(ws):
            e = ws[j + 1][0] if j + 1 < len(ws) else len(lit)
            units.append([w2, k, lit[s + len(w2) * k:e]])
        st.units = units
        st.normalize()

    # ------------------------------------------------------------ counter jumps
    def cycle(self, i, w, lit, ctx, wnext=None):
        """the hit records of unit i from literal lit around to the same literal, or None if one is unknown.
        ctx: the lower context of a round that stops at unit i (P and the carry literals of the units below)."""
        seq = []
        cur = (tuple(w), tuple(lit))
        start = cur
        for _ in range(64):
            # a carry and a stop at the same literal and lower context: the outcome depends on the units above,
            # so no cycle
            rc = self.carry.get((i, cur[0], cur[1], ctx))
            rs = self.stop.get((i, cur[0], cur[1], ctx))
            if rc is not None and rs is not None:
                return None
            rec = rc if rc is not None else rs
            if rec is None:
                return None
            seq.append(rec)
            cur = (rec['newword'], rec['newlit'])
            if cur == start:
                return seq
        return None

    def known_depth(self, st):
        """largest j such that units 0..j-1 all have complete cycles with one carry each"""
        j = 0
        cyc = []
        lower = []
        while j < len(st.units):
            w, n, lit = st.units[j]
            c = self.cycle(j, w, lit, (st.P, tuple(lower)), tuple(st.units[j + 1][0]) if j + 1 < len(st.units) else None)
            if c is None or sum(1 for r in c if r['kind'] == 'carry') < 1:
                break
            # the carry input literal of unit j, for the context of the units above
            cur = (tuple(w), tuple(lit))
            for r in c:
                if r['kind'] == 'carry':
                    break
                cur = (r['newword'], r['newlit'])
            if sum(r['delta'] for r in c) < 0:
                break
            # the carry input states (one per carry of the cycle); several different ones give the units above
            # several lower contexts, so such a unit can only be the top jumpable one
            ins = set()
            prev = (tuple(w), tuple(lit))
            for r in c:
                if r['kind'] == 'carry':
                    ins.add(prev)
                prev = (r['newword'], r['newlit'])
            lower.append(cur)
            cyc.append(c)
            j += 1
            if len(ins) > 1:
                break
        # every kind of round a jump below depth j uses, run symbolically and compared with the records
        for d in range(1, j + 1):
            if not self.verify_depth(st, d, cyc, lower):
                return d - 1, cyc[:d - 1]
        return j, cyc

    def verify_depth(self, st, d, cyc, lower):
        """the rounds of depth d in a jump: units 0..d-2 at their carry inputs, unit d-1 at any stop position of
        its cycle. Each is run (symbolic counts, so exact for every count >= T0) and must match the hit records
        used by apply_hits: words, literals, count changes and step coefficients."""
        cur = (tuple(st.units[d - 1][0]), tuple(st.units[d - 1][2]))
        ok = True
        for rec in cyc[d - 1]:
            if rec['kind'] == 'stop':
                key = (d, st.P, tuple(lower[:d - 1]), cur, tuple(st.units[d][0]) if d < len(st.units) else None,
                       tuple(sorted(rec.items())), tuple(tuple(sorted(r.items())) for c in cyc[:d - 1] for r in c if r['kind'] == 'carry'))
                v = self.vcache.get(key)
                if v is None:
                    v = self.verify_round(st, d, cyc, lower, cur, rec)
                    self.vcache[key] = v
                if not v:
                    ok = False
                    break
            cur = (rec['newword'], rec['newlit'])
        return ok

    def verify_round(self, st, d, cyc, lower, cur, srec):
        N = [5003 + 37 * i for i in range(len(st.units))]
        units = [[lower[i][0], N[i], lower[i][1]] for i in range(d - 1)] + [[cur[0], N[d - 1], cur[1]]]
        units += [[u[0], N[i + d], u[2]] for i, u in enumerate(st.units[d:])]
        tmp = State(st.P, units, 0)
        recs = [next(r for r in cyc[i] if r['kind'] == 'carry') for i in range(d - 1)] + [srec]
        if self.round_rule(tmp, d)[0] != 'ok':
            return False
        self.norecord = True
        saved = (self.rounds, self.explicit)
        try:
            self.do_round(tmp)
        except (NeedFull, RuntimeError):
            return False
        finally:
            self.norecord = False
            self.rounds, self.explicit = saved
        dd, full, conc, steps = self.last
        if (dd, full, conc) != (d, False, 0) or tmp.P != st.P or len(tmp.units) != len(units):
            return False
        for i in range(d):
            r = recs[i]
            if [tuple(tmp.units[i][0]), tmp.units[i][1], tuple(tmp.units[i][2])] != \
                    [tuple(r['newword']), N[i] + r['delta'], tuple(r['newlit'])]:
                return False
            if steps.c.get('x%d' % i, 0) != r['a']:
                return False
        if set(steps.c) - {'x%d' % i for i in range(d)}:
            return False
        if steps.k - T0 * sum(steps.c.values()) != srec['b']:
            return False
        for i in range(d, len(units)):
            if tmp.units[i] != units[i]:
                return False
        return True

    def hits_until_carry(self, cyc, k):
        """number of hits (from position 0 of cyc) that produce k carries, the k-th carry being the last hit"""
        L = len(cyc)
        carries = [p for p, r in enumerate(cyc) if r['kind'] == 'carry']
        per = len(carries)
        q, r = divmod(k - 1, per)
        return q * L + carries[r] + 1

    def jump_ok(self, st, j, cyc, m):
        hits = m
        for i in range(j):
            n = st.units[i][1]
            if n < T0:
                return False
            off = 0
            for rec in cyc[i][:min(hits, len(cyc[i]))]:
                off += rec['delta']
                if n + off < T0:
                    return False
            L = len(cyc[i]); q, r = divmod(hits, L)
            per = sum(1 for rec in cyc[i] if rec['kind'] == 'carry')
            hits = q * per + sum(1 for rec in cyc[i][:r] if rec['kind'] == 'carry')
        return True

    def apply_hits(self, st, i, cyc, m):
        """apply m hits to unit i (m >= 0), none of which may carry out of the jumpable range; returns
        number of carries passed to unit i+1 and adds the steps. Closed form."""
        if m == 0:
            return 0
        w, n, lit = st.units[i]
        L = len(cyc)

        q, r = divmod(m, L)
        steps = 0
        carries = 0
        # full cycles: hit p of cycle k sees n + k*D + off_p
        D = sum(rec['delta'] for rec in cyc)
        if q:
            off = 0
            A = 0
            B = 0
            for rec in cyc:
                A += rec['a']
                B += rec['a'] * (n + off) + rec.get('b', 0)
                off += rec['delta']
            steps += q * B + A * D * q * (q - 1) // 2
            carries += q * sum(1 for rec in cyc if rec['kind'] == 'carry')
            n += q * D
        for rec in cyc[:r]:
            steps += rec['a'] * n + rec.get('b', 0)
            n += rec['delta']
            if rec['kind'] == 'carry':
                carries += 1
        last = cyc[r - 1] if r else cyc[-1]
        st.units[i] = [tuple(last['newword']), n, tuple(last['newlit'])]
        st.steps += steps
        return carries

    def jump(self, st, maxr=None):
        """apply E-1 rounds in closed form, where the E-th round goes deeper than the jumpable units; returns E-1."""
        j, cyc = self.known_depth(st)
        if j == 0:
            return 0
        # hits needed: one carry out of unit j-1
        k = 1
        for i in range(j - 1, -1, -1):
            k = self.hits_until_carry(cyc[i], k)
        m = k - 1         # rounds to jump (all of depth <= j)
        if maxr is not None:
            m = min(m, maxr)
        if m <= 0:
            return 0
        # the counts must stay >= T0 before and after every hit (the cycles do not shrink, so the first cycle
        # holds the minimum): otherwise the jump is cut down
        while m > 0 and not self.jump_ok(st, j, cyc, m):
            m //= 2
        if m <= 0:
            return 0
        hits = m
        for i in range(j):
            nxt = self.apply_hits(st, i, cyc[i], hits)
            hits = nxt
        assert hits == 0
        self.rounds += m
        return m


# ---------------------------------------------------------------- direct runs
def pbvis():
    exe = os.path.join(os.environ.get('TMPDIR', '/tmp'), 'pbvis_m3')
    if not os.path.exists(exe):
        subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', 'c', 'pbvis.c')], check=True)
    return exe


def tok_len(toks):
    """length in cells of a token list (Lin), Blank/Ctx not counted"""
    n = Lin(0)
    for t in toks:
        if isinstance(t, Rep):
            n = n + len(t.word) * t.n
        elif isinstance(t, int):
            n = n + 1
    return n


def hybrid_run(c, stop, cmax=2 * 10**11, zmin=0):
    """run c until stop(c): symbolic (symtm, shift rules), and whenever every symbolic-count wall is left of the
    head, the part right of the last one cell by cell in c/tailsim.c.  Returns ('ok', c) or a failure tuple."""
    isvar = lambda t: isinstance(t, Rep) and not t.n.is_const()
    while True:
        try:
            c = symtm.run(MACH, c, stop, max_moves=3000, rotate=True)
            return ('ok', c)
        except symtm.Halted as e:
            return ('halt', str(e), repr(c)[:3000])
        except symtm.NeedSplit as e:
            return ('split', str(e))
        except symtm.TouchContext:
            return ('touch',)
        except RuntimeError:
            pass
        if any(isvar(t) for t in c.right):
            continue
        ks = [i for i, t in enumerate(c.left) if isvar(t)]
        k = ks[-1] if ks else 0
        lc = expand(c.left[k + 1:])
        rc = expand(c.right)
        if len(lc) + len(rc) > 60000000:
            return ('limit', 'concrete part too long: %d cells' % (len(lc) + len(rc)), None)
        inp = '%s %d %s\n' % ('ABCDEF'[c.state], len(lc), ''.join(map(str, lc + rc)) or '0')
        p = subprocess.run([tailsim(), M, str(cmax), '0', str(zmin)], input=inp, capture_output=True, text=True,
                           check=True)
        out = p.stdout.split()
        if out[0] == 'inner':
            Engine.conc_steps += int(out[1])
            h = int(out[3]); cells = [int(x) for x in out[4]]
            c.left = c.left[:k + 1] + cells[:h]
            c.right = cells[h:] + [Blank()]
            c.state = 'ABCDEF'.index(out[2])
            c.steps = c.steps + int(out[1])
            if stop(c):
                return ('ok', c)
            continue
        if out[0] == 'halt':
            print('HALT (concrete part) after', out[1], 'more steps, state', out[2], flush=True)
            return ('halt', 'concrete: %s more steps, state %s, head %s; steps before %r' % (
                out[1], out[2], out[3], c.steps), inp[:2000])
        if out[0] != 'exit':
            return ('limit', 'concrete part over %d steps' % cmax, None)
        Engine.conc_steps += int(out[1])
        c.left = c.left[:k + 1]
        c.right = ([int(x) for x in out[4]] if len(out) > 4 else []) + [Blank()]
        c.state = 'ABCDEF'.index(out[2])
        c.steps = c.steps + int(out[1])
        try:
            symtm._unroll_back(c.left)
        except symtm.NeedSplit as e:
            return ('split', str(e))
        c.right.insert(0, c.left.pop())


def expand(ts):
    out = []
    for t in ts:
        if isinstance(t, Rep):
            out += list(t.word) * t.n.k
        elif isinstance(t, int):
            out.append(t)
        else:
            assert isinstance(t, Blank), t
    return out


def tailsim():
    exe = os.path.join(os.environ.get('TMPDIR', '/tmp'), 'tailsim_m3')
    if not os.path.exists(exe):
        subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', 'c', 'tailsim.c')], check=True)
    return exe


def direct(start, count, every=1):
    p = subprocess.run([pbvis(), M, str(int(start)), str(count), str(every)], capture_output=True, text=True,
                       check=True)
    out = []
    for line in p.stdout.split('\n'):
        if line.startswith('HALT'):
            raise RuntimeError(line)
        if line:
            a, b = line.split()
            out.append((int(a), b))
    return out


def test(start=3e8, nround=3000, nround2=40000):
    """1) round by round from a direct round start, compare every round start with the direct run;
       2) jumps: from the same start, run with jumps to a later direct sample and compare."""
    vis = direct(start, nround + 1)
    st = State.from_cells(vis[0][1], vis[0][0])
    E = Engine()
    bad = 0
    for k in range(1, len(vis)):
        E.do_round(st)
        if st.steps != vis[k][0] or st.cells() != tuple(int(c) for c in vis[k][1].rstrip('0')):
            bad += 1
            print('MISMATCH at round', k, st.steps, vis[k][0])
            break
    print('round by round: %d rounds from step %d to %d, %d mismatches, %d symbolic rounds' % (
        len(vis) - 1, vis[0][0], vis[-1][0], bad, E.nsym))
    # jumps: to the round R2 after the start, and compare with the direct run there
    R2 = int(nround2)
    v2 = direct(start, R2 + 1, R2)
    st = State.from_cells(v2[0][1], v2[0][0])
    E = Engine()
    njump = 0
    while E.rounds < R2:
        m = E.jump(st, R2 - E.rounds)
        njump += m > 0
        if E.rounds < R2:
            E.do_round(st)
    target = v2[1]
    ok = st.steps == target[0] and st.cells() == tuple(int(c) for c in target[1].rstrip('0'))
    print('with jumps: %d rounds from step %d to step %d (%d explicit rounds, %d jumps): %s' % (
        E.rounds, v2[0][0], st.steps, E.explicit, njump, 'AGREES with the direct run, tape and step' if ok else
        'MISMATCH (direct %d)' % target[0]))
    return bad == 0 and ok


if __name__ == '__main__':
    if sys.argv[1] == 'test':
        sys.exit(0 if test(*(float(x) for x in sys.argv[2:])) else 1)


def run(start, seconds, maxdig=10**9, ckpt=None, log_every=20.0):
    if ckpt and os.path.exists(ckpt):
        with open(ckpt, 'rb') as f:
            st, E = pickle.load(f)
        print('resumed from', ckpt, 'step 1e%d' % (len(str(st.steps)) - 1))
    else:
        v = direct(start, 1)
        st = State.from_cells(v[0][1], v[0][0])
        E = Engine()
    t0 = time.time(); tl = 0; tails = 0
    while time.time() - t0 < seconds and len(str(st.steps)) <= maxdig:
        E.jump(st)
        nu = len(st.units)
        try:
            d, full, conc = E.do_round(st)
        except RuntimeError:
            with open(os.path.join(os.environ.get('TMPDIR', '/tmp'), 'm3_fail.pkl'), 'wb') as f:
                pickle.dump((st, E.failed[1:]), f)
            raise
        if full or conc:
            tails += 1
            print('event %d: depth %d of %d units, full %s, concrete %d, step %s (%d digits), rounds %s; units now %d: %s' % (
                tails, d, nu, full, conc, fmt(st.steps), len(str(st.steps)), fmt(E.rounds), len(st.units), st.show()[:400]), flush=True)
        if time.time() - tl > log_every:
            tl = time.time()
            print('t=%.0fs step ~1e%d rounds ~1e%d units %d explicit %d symbolic %d' % (
                tl - t0, len(str(st.steps)) - 1, len(str(E.rounds)) - 1, len(st.units), E.explicit, E.nsym), flush=True)
            if ckpt:
                with open(ckpt + '.tmp', 'wb') as f:
                    pickle.dump((st, E), f)
                os.replace(ckpt + '.tmp', ckpt)
    print('END step', fmt(st.steps), 'digits', len(str(st.steps)), 'rounds', fmt(E.rounds), 'units', len(st.units))
    print(st.show()[:2000])
    if ckpt:
        with open(ckpt, 'wb') as f:
            pickle.dump((st, E), f)
    return st, E


if __name__ == '__main__' and sys.argv[1] == 'run':
    sys.setrecursionlimit(100000)
    run(float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 10**9,
        sys.argv[5] if len(sys.argv) > 5 else None)


# ---------------------------------------------------------------- resets: a new counter in front of a blank stretch
ZMIN = 2000      # a blank stretch of at least ZMIN cells left of a round start makes an inner counter
KCUT = 3000     # cells of a blank stretch (beyond ZMIN) given to a whole-tape round, in front of an opaque context
MARGIN = 64


def zeros_at_end(left):
    z = 0
    for t in reversed(left):
        if isinstance(t, int):
            if t:
                break
            z += 1
        elif isinstance(t, Rep) and t.n.is_const() and not any(t.word):
            z += len(t.word) * t.n.k
        else:
            break
    return z


def is_inner_start(c):
    if c.state != QB or len(c.left) < 2:
        return False
    r = c.right
    if len(r) < 9 or not all(isinstance(x, int) for x in r[:9]) or tuple(r[:9]) != PB:
        return False
    return zeros_at_end(c.left) >= ZMIN


def strip_zeros(left):
    left = list(left)
    while left and (left[-1] == 0 or (isinstance(left[-1], Rep) and left[-1].n.is_const() and not any(left[-1].word))):
        left.pop()
    return left


def state_from_tokens(toks, env, steps):
    """a round-start tape (head on the first token, ends with Blank) -> State; walls of >= 2*T0 copies are units"""
    flat = []
    for t in toks:
        if isinstance(t, Rep):
            n = t.n.subs(env) if not t.n.is_const() else t.n.k
            if (len(t.word) in WL and primitive(t.word) and n >= 2 * T0) or (tuple(t.word) == (1,) and n >= ONES):
                flat.append(('R', tuple(t.word), n))
            else:
                flat.extend(list(t.word) * n)
        elif isinstance(t, int):
            flat.append(t)
    # split literal stretches at walls of >= 2*T0 copies too
    flat2 = []
    lit = []
    def flush():
        cells = tuple(lit)
        ws = find_walls(cells, 2 * T0)
        pos = 0
        for s0, w, k in ws:
            flat2.extend(cells[pos:s0]); flat2.append(('R', w, k)); pos = s0 + len(w) * k
        flat2.extend(cells[pos:])
        lit.clear()
    for x in flat:
        if isinstance(x, tuple):
            flush(); flat2.append(x)
        else:
            lit.append(x)
    flush()
    P = []
    units = []
    for x in flat2:
        if isinstance(x, tuple):
            units.append([x[1], x[2], []])
        elif units:
            units[-1][2].append(x)
        else:
            P.append(x)
    if not units:
        return State.from_cells(''.join(map(str, P)), steps)
    st = State(P, [[w, n, tuple(l)] for w, n, l in units], steps)
    st.normalize()
    return st



class Driver:
    """outer (frozen tokens left of a blank stretch, starting with Blank) + Z blank cells + an inner counter st,
    or (outer None) a plain counter at the left end of the tape."""
    def __init__(self, st):
        self.st, self.outer, self.Z = st, None, None
        self.E = Engine()
        self.E.driver_full = True
        self.events = []

    def tlen(self):
        st = self.st
        return len(st.P) + sum(len(u[0]) * u[1] + len(u[2]) for u in st.units)

    def copy_state(self):
        st = self.st
        return State.__new__(State), (st.P, [list(u) for u in st.units], st.steps)

    def restore(self, saved):
        st = self.st
        st.P, st.units, st.steps = saved[1][0], [list(u) for u in saved[1][1]], saved[1][2]

    def step(self):
        E, st = self.E, self.st
        if self.outer is None:
            E.jump(st)
            try:
                E.do_round(st)
            except NeedFull:
                self.full_round()
            return
        # inner mode: never let the counter grow over the blank stretch
        saved = self.copy_state(); r0 = E.rounds
        L0 = self.tlen()
        m = E.jump(st)
        g = self.tlen() - L0
        while m and g > self.Z - MARGIN:
            self.restore(saved); E.rounds = r0
            m = E.jump(st, max(m // 2, 0) or 0) if m // 2 else 0
            g = self.tlen() - L0 if m else 0
        self.Z -= g
        saved = self.copy_state(); r0 = E.rounds
        try:
            E.do_round(st)
        except NeedFull:
            self.full_round()
            return
        if E.growth > self.Z - MARGIN:
            self.restore(saved); E.rounds = r0
            self.full_round()
        else:
            self.Z -= E.growth

    def full_round(self):
        """run the whole tape (outer, blank stretch, counter) from the counter's round start, symbolic with concrete
        tails, until a round start at the left end of the tape or in front of a blank stretch of >= ZMIN cells"""
        st = self.st
        stop = lambda c: not c.steps.is_zero() and (is_start(c) or is_inner_start(c))
        d = len(st.units)
        # the blank stretch is cut to its last K cells, behind an opaque context: a round that reaches the
        # context (TouchContext) is run again with the whole left part
        cut = self.outer is not None and self.Z > ZMIN + KCUT
        for attempt in (0, 1):
            K = ZMIN + KCUT if cut else self.Z
            # the number of units written out: first the one that worked last time, then from 0 up
            lc = getattr(self, 'last_conc', 0)
            order = ([lc] if 0 < lc < d else []) + [k for k in range(0, d) if k != lc or not 0 < lc < d]
            for conc in order:
                toks = list(st.P)
                for i, (w, n, lit) in enumerate(st.units):
                    toks.append(Rep(tuple(w), Lin('x%d' % i) + T0 if i < d - conc else Lin(n)))
                    toks.extend(lit)
                toks.append(Blank())
                if self.outer is None:
                    left = [Blank()]
                elif cut:
                    left = [Ctx('L')] + [0] * K
                else:
                    left = list(self.outer) + [0] * self.Z
                c = Config(left, QB, toks)
                r = hybrid_run(c, stop, zmin=ZMIN)
                if r[0] != 'split':
                    break
            if r[0] == 'touch' and cut:
                cut = False
                continue
            break
        if r[0] == 'halt':
            print('HALT in a whole-tape round from step', st.steps, ':', r[1], r[2], flush=True)
            raise RuntimeError('HALT: %s' % (r[1],))
        if r[0] != 'ok':
            raise RuntimeError('whole-tape round failed: %r' % (r[:2],))
        c = r[1]
        self.last_conc = conc
        env = {'x%d' % i: st.units[i][1] - T0 for i in range(d - conc)}
        steps = st.steps + c.steps.subs(env)
        if is_start(c):
            self.outer, self.Z = None, None
            kind = 'left end'
        else:
            z = zeros_at_end(c.left)
            out = strip_zeros(c.left)
            if cut and len(out) == 1 and isinstance(out[0], Ctx):
                # only zeros right of the context: the outer part is as it was
                self.Z = self.Z - K + z
            else:
                if cut:
                    out = list(self.outer) + [0] * (self.Z - K) + out[1:]
                    z = zeros_at_end(out + [0] * z)
                    out = strip_zeros(out)
                self.Z = z
                self.outer = [Rep(t.word, Lin(t.n.subs(env))) if isinstance(t, Rep) and not t.n.is_const() else t
                              for t in out]
            kind = 'blank stretch of %d cells' % self.Z
        self.st = state_from_tokens(c.right, env, steps)
        self.E.rounds += 1
        self.E.explicit += 1
        ev = (steps, kind, len(self.st.units), conc)
        self.events.append(ev)
        return ev


def drun(start, seconds, maxdig=10**9, ckpt=None, log_every=30.0):
    if ckpt and os.path.exists(ckpt):
        with open(ckpt, 'rb') as f:
            D = pickle.load(f)
        print('resumed from', ckpt, 'step 1e%d' % (len(str(D.st.steps)) - 1))
        D.E.promote_all(D.st)
    else:
        v = direct(start, 1)
        D = Driver(State.from_cells(v[0][1], v[0][0]))
    t0 = time.time(); tl = 0; ne = len(D.events)
    while time.time() - t0 < seconds and len(str(D.st.steps)) <= maxdig:
        try:
            D.step()
        except Exception:
            with open(os.path.join(os.environ.get('TMPDIR', '/tmp'), 'm3_dfail.pkl'), 'wb') as f:
                pickle.dump(D, f)
            raise
        if len(D.events) > ne:
            for ev in D.events[ne:]:
                print('event: step %s (%d digits), round start at the %s; %d units, %d written out: %s' % (
                    fmt(ev[0]), len(str(ev[0])), ev[1], ev[2], ev[3], D.st.show()[:300]), flush=True)
            ne = len(D.events)
        if time.time() - tl > log_every:
            tl = time.time()
            print('t=%.0fs step ~1e%d rounds ~1e%d units %d explicit %d symbolic %d %s' % (
                tl - t0, len(str(D.st.steps)) - 1, len(str(D.E.rounds)) - 1, len(D.st.units), D.E.explicit,
                D.E.nsym, '' if D.outer is None else 'inner, blank %d' % D.Z), flush=True)
            if ckpt:
                with open(ckpt + '.tmp', 'wb') as f:
                    pickle.dump(D, f)
                os.replace(ckpt + '.tmp', ckpt)
    print('END step', fmt(D.st.steps), 'digits', len(str(D.st.steps)), 'rounds', fmt(D.E.rounds), 'units',
          len(D.st.units), '' if D.outer is None else 'inner, blank %d' % D.Z)
    print(D.st.show()[:3000])
    if ckpt:
        with open(ckpt, 'wb') as f:
            pickle.dump(D, f)
    return D


if __name__ == '__main__' and sys.argv[1] == 'drun':
    sys.setrecursionlimit(100000)
    drun(float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 10**9,
         sys.argv[5] if len(sys.argv) > 5 else None)
