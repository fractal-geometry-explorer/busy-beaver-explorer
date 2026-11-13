"""Closed-set search with FREE big counts (after the method of the proof of bbchallenge id 31480).

Node = the shape of the tape at a checkpoint (state, side, literal cells, block words) plus, for each block, either a
small constant count or "free: any count >= t".  Nothing else about a free count is tracked (no residues).

A branch is a symbolic configuration (accel.py's moves; block counts are linear forms in variables >= 0).
* Lemma A (period): when a shape recurs with a constant change d of the counts, the period is re-run from the
  generalised configuration (every changing or free block: fresh variable + threshold t_i, the thresholds raised
  until the run needs no further copy).  It then holds for all counts >= t_i.  That configuration is the node.
* If the node is covered by an earlier node (same shape, constants equal, thresholds >=), the branch ends.
* Lemma B (conversion): the period is applied while every shrinking block has >= t_i copies.  Cases: which
  shrinking block i gets below t_i first, and its count then (t_i - r_i .. t_i - 1, r_i its loss per period); the
  other shrinking blocks keep a free count >= t_j - r_j, growing blocks a free count >= t_j.  Each case is a new
  branch, run symbolically to its next node.
* Every assumption is a split, never a guess: a free count that must supply a copy when its constant part is used
  up splits into v = 0 (a constant) and v >= 1; a free count below a node's threshold splits into the constants
  below and the rest.  So the union of the cases is everything.
If the queue empties and no branch reached the halting transition, no configuration reachable from the start halts
(level: this code) - with all counts free.  That search does not close for this machine (see README).

Size assumptions (START mode).  A count can carry the tag "huge" (variable H..): such a block is ASSUMED to have at
least HMIN copies.  For a huge block no zero case and no small cases are followed (STATS huge_zero, huge_small); a
block that grows in a phase ended by a huge block becomes huge (huge_grown, switch GROWN); the other huge shrinking
blocks stay huge (huge_kept); and with RATIO only the huge shrinking block that ran out first in the real run
(witness.py) may run out first (ratio_first).  With these the result is conditional on the assumptions.

environment:
  START=step   start from the exact run at the first jump after this step (blocks >= 1000 copies become huge)
  RATIO=file   witness json with the ratio rules
  GROWN=0      switch assumption huge_grown off
  TMAX=sec     time limit (default 540);  CKPT=file  checkpoint every 60 s, and continue from it if it exists

usage (from the repo root):
  python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/closure2/search.py MACHINE [MAXNODES] [OUT.json]
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import accel  # noqa: E402
from accel import Rep, Lin, BL, NeedSplit, Halted, shape, reps  # noqa: E402

_fresh = [0]
BIG = 24            # a constant block this long becomes free (count >= its value)
MAXT = 160          # largest threshold tried for a block
DEFECT = [None]     # mutation tests set this


HMIN = 1000         # a block tagged huge (variable H..) is assumed to have at least this many copies
STATS = {'huge_small': 0, 'huge_zero': 0, 'huge_grown': 0, 'huge_kept': 0}


def fresh(huge=False):
    _fresh[0] += 1
    return ('H%d' if huge else 'v%d') % _fresh[0]


def is_huge(n):
    return not isinstance(n, int) and any(v[0] == 'H' and a > 0 for v, a in n.c.items())


def is_var(n):
    return not isinstance(n, int) and not n.is_const()


def cval(n):
    return n if isinstance(n, int) else n.k


def map_counts(c, f):
    rs = reps(c)
    idx = {id(z): i for i, z in enumerate(rs)}

    def g(z):
        if isinstance(z, Rep):
            return Rep(z.w, f(idx[id(z)], z.n))
        return z
    d = accel.Cfg(c.m, [g(z) for z in c.L], c.st, [g(z) for z in c.R], 0)
    d.ev = c.ev
    return d


def subst_lin(n, v, k):
    """v := v + k (k int), or v := 0 (k None)"""
    if isinstance(n, int) or v not in n.c:
        return n
    if k is None:
        return Lin(n.k, {u: a for u, a in n.c.items() if u != v})
    return n + n.c[v] * k


def normalise(c):
    """A count a1*v1 + ... + k whose variables occur in no other block is replaced by v + k with v fresh (a superset
    of configurations when some a_i > 1, the same set otherwise).  Returns the new configuration, or None if nothing
    changed."""
    rs = reps(c)
    occ = {}
    for z in rs:
        if is_var(z.n):
            for v in z.n.c:
                occ[v] = occ.get(v, 0) + 1
    todo = set()
    for i, z in enumerate(rs):
        n = z.n
        if not is_var(n) and cval(n) >= BIG:
            todo.add(i)        # a long block with a known count: forget the count, keep "at least this many"
        if is_var(n) and (len(n.c) > 1 or list(n.c.values())[0] != 1) and all(occ[v] == 1 and a > 0 for v, a in n.c.items()):
            todo.add(i)
    if not todo:
        return None
    return map_counts(c, lambda i, n: Lin(fresh(is_huge(n))) + cval(n) if i in todo else n)


def spec(c):
    return tuple((('H' if is_huge(n) else 'v'), n.k) if is_var(n) else ('c', cval(n)) for n in (z.n for z in reps(c)))


def covers(t, s):
    for (a, x), (b, y) in zip(t, s):
        if a == 'c':
            if b != 'c' or x != y:
                return False
        elif b == 'c' or y < x or (a == 'H' and b != 'H'):
            return False
    return True


def show(c):
    return accel.symtm_str(c)


accel.CROSS_MIN[0] = 10 ** 9       # ... but only a block with a free count, so that the events do not depend on values
accel.CROSS_EVENTS[0] = True     # crossing a long block is an event too (phases that never reach the tape end)
GROWN = [os.environ.get('GROWN', '1') == '1']    # assumption A2 on/off
RATIO = {}          # delta signature -> witness entry (which shrinking block runs out first); empty = no ratio rule
USED_RATIO = set()
_pcache = {}
_pfail = set()
DRIFT = 3
MULT = 3


def period(c, nev, delta):
    """Lemma A.  Returns (Ts, node, nodeTs, nodedelta) or None.
    Ts: thresholds on the blocks of c (block i of c must have >= Ts[i] copies; other blocks keep their constants).
    node: a configuration with free counts (fresh variable + threshold nodeTs[i]) such that
      * every configuration of the shape of c with counts >= Ts reaches, after k*nev events (k = 0..DRIFT), a
        configuration covered by node, and
      * nev events from node lead back to the shape of node with the counts changed by nodedelta, for all values of
        the variables.
    (k > 0 happens when the same tape is first parsed into blocks in another way.)"""
    rs = reps(c)
    free = tuple(i for i, z in enumerate(rs) if is_var(z.n) or delta[i] != 0)
    fixed = {i: not is_var(rs[i].n) for i in free}    # a constant block can be generalised only up to its value
    key = (shape(c), nev, tuple(delta), free, tuple(cval(z.n) for i, z in enumerate(rs) if i not in free))
    fkey = (key, tuple(sorted(fixed.items())))      # one attempt per shape and set of free blocks (a growing constant block becomes free at BIG)
    if fkey in _pfail:
        return None
    Ts = _pcache.get(key)
    if Ts is not None and all(not fixed[i] or Ts[i] <= cval(rs[i].n) for i in free):
        Ts = dict(Ts)
    else:
        Ts = {i: min(cval(rs[i].n), max(0, -delta[i])) for i in free}
    for _ in range(600):
        r = _chain(c, nev, Ts)
        if isinstance(r, int):          # block r of c needs one more copy
            Ts[r] += 1
            if Ts[r] > MAXT or (fixed[r] and Ts[r] > cval(rs[r].n)):
                break
            continue
        if r is None:
            break
        _pcache[key] = dict(Ts)
        return (Ts,) + r
    _pfail.add(fkey)
    return None


def _run(g, nev):
    s = map_counts(g, lambda i, n: n)
    k = mv = 0
    while k < nev:
        mv += 1
        if accel.advance(s):
            k += 1
        if mv > 10 ** 6:
            raise RuntimeError('period too long')
    return s


def _chain(c, nev, Ts):
    origin = {}          # variable of the current stage -> block index of c

    def gen(i, n):
        if i in Ts:
            v = fresh(is_huge(n))
            origin[v] = i
            return Lin(v) + Ts[i]
        return Lin(cval(n))
    g = map_counts(c, gen)
    for depth in range(DRIFT + 1):
        start = [z.n for z in reps(g)]
        e1 = None
        try:
            # run until the shape of g comes back.  The number of events is not fixed in advance: whether a
            # crossing counts as an event depends on the block having a free count, and the parse may come back
            # only after 2 or 3 periods.
            e = map_counts(g, lambda i, n: n)
            sg = shape(g)
            k = mv = 0
            while k < MULT * nev + 40:
                mv += 1
                if mv > 10 ** 6:
                    raise RuntimeError('period too long')
                if accel.advance(e):
                    k += 1
                    if k == nev:
                        e1 = map_counts(e, lambda i, n: n)
                    if shape(e) == sg:
                        break
        except NeedSplit as x:
            vs = [v for v, a in x.args[0].n.c.items() if a > 0 and v in origin]
            return origin[vs[0]] if vs else None
        except (RuntimeError, Halted):
            return None
        if shape(e) == shape(g):
            end = [z.n for z in reps(e)]
            d = []
            for a, b in zip(start, end):
                x = Lin(b) - Lin(a)
                if not x.is_const():
                    return None
                d.append(x.k)
            if not any(d):
                return None
            nodeTs = {i: n.k for i, n in enumerate(start) if is_var(n)}
            return g, nodeTs, d
        e = e1
        # another parse: start again from e, its counts made independent
        org2 = {}

        def regen(i, n):
            if not is_var(n):
                return Lin(cval(n))
            v = fresh(is_huge(n))
            if len(n.c) == 1 and list(n.c.values())[0] == 1 and list(n.c)[0] in origin:
                org2[v] = origin[list(n.c)[0]]
            return Lin(v) + n.k
        g = map_counts(e, regen)
        origin = org2
    return None


class Search:
    def __init__(s, M, maxn=20000, log=None, start=None):
        s.m = accel.Machine(M)
        s.nodes = {}        # shape -> list of (spec, id)
        s.info = []         # id -> dict
        s.queue = [(start or accel.Cfg(s.m, [BL], 0, [BL], Lin(0)), {}, 0, -1, 'start', 0)]
        s.maxn = maxn
        s.branches = 0
        s.forever = 0
        s.halts = []
        s.log = log
        s.edges = []
        s.stuck = []        # branches the search could not follow (source node, label, reason)

    def find(s, g):
        sp = spec(g)
        for t, i in s.nodes.get(shape(g), []):
            if covers(t, sp):
                return i
        return None

    def add(s, g, Ts, delta):
        i = len(s.info)
        s.nodes.setdefault(shape(g), []).append((spec(g), i))
        s.info.append({'id': i, 'cfg': show(g), 'delta': list(delta), 'thresholds': {str(k): v for k, v in Ts.items()}})
        return i

    def cases(s, g, Ts, delta):
        """Lemma B start points: (configuration, label)"""
        rs = reps(g)
        huge = [is_huge(z.n) for z in rs]
        shrink = [i for i, d in enumerate(delta) if d < 0]
        if not shrink:
            return 'forever'
        out = []
        hs = [i for i in shrink if huge[i]]
        sig = ','.join(str(x) for x in delta if x)
        allowed = None
        if len(hs) >= 2 and RATIO:
            # ASSUMPTION (ratio type): of the huge shrinking blocks, only the one that ran out first in the real
            # run (closure2/witness.py) can run out first.  Free (non-huge) blocks may always run out first.
            w = RATIO.get(sig)
            if w is None:
                STATS['ratio_unknown'] = STATS.get('ratio_unknown', 0) + 1
            else:
                allowed = set(shrink[int(t)] for t in w['first'])
                STATS['ratio_first'] = STATS.get('ratio_first', 0) + 1
                USED_RATIO.add(sig)
        for i in shrink:
            if allowed is not None and huge[i] and i not in allowed:
                continue
            r = -delta[i]
            lo = Ts[i] - r
            if DEFECT[0] == 'drop_remainder' and r > 1:
                lo += 1
            for val in range(max(lo, 0), Ts[i]):
                def f(j, n, i=i, val=val):
                    if j == i:
                        return Lin(val)
                    if j in shrink:
                        # ASSUMPTION (ratio type): a huge block that is not the one that runs out stays huge
                        if huge[j]:
                            STATS['huge_kept'] += 1
                        return Lin(fresh(huge[j])) + max(Ts[j] + delta[j], 0)
                    if delta[j] > 0:
                        # ASSUMPTION: a phase that uses up a huge block has so many periods that every block
                        # growing in it ends huge
                        if huge[i] and not huge[j] and GROWN[0]:
                            STATS['huge_grown'] += 1
                        return Lin(fresh(huge[j] or (huge[i] and GROWN[0]))) + (Ts[j] + (delta[j] if DEFECT[0] == 'grow_threshold' else 0))
                    return n
                out.append((map_counts(g, f), 'block %d ends with %d' % (i, val)))
            if DEFECT[0] == 'first_shrink_only':
                break
        return out

    def branch(s, item, maxmoves=3 * 10 ** 6):
        s.branches += 1
        c, hist, evn, src, label, peel = item
        mv = 0
        skip = 0
        while True:
            try:
                isev = accel.advance(c)
            except NeedSplit as e:
                n = e.args[0].n
                v = next(u for u, a in n.c.items() if a > 0)
                c0 = map_counts(c, lambda i, n: subst_lin(n, v, None))
                if v[0] == 'H':
                    # ASSUMPTION: a huge block has >= HMIN copies; at most HMIN - MAXT of them may be taken this way
                    STATS['huge_zero'] += 1
                    peel = peel + 1
                    if peel > HMIN - MAXT:
                        raise RuntimeError('a huge block is eaten copy by copy: %s' % show(c))
                elif DEFECT[0] != 'no_zero_case':
                    s.queue.append((c0, {}, 0, src, label + '; a free count is 0', 0))
                c1 = map_counts(c, lambda i, n: subst_lin(n, v, 1))
                h1 = {sh: ([subst_lin(x, v, 1) for x in cn], e) for sh, (cn, e) in hist.items()}
                s.queue.append((c1, h1, evn, src, label, peel))
                return
            except Halted as e:
                s.halts.append((src, label, show(c)))
                s.edges.append((src, 'HALT', label))
                return
            mv += 1
            if mv > maxmoves:
                raise RuntimeError('branch too long: %s' % show(c))
            if not isev:
                continue
            evn += 1
            c2 = normalise(c)
            if c2 is not None:
                c2.quiet = 0
                c = c2
                hist = {}
            sh = shape(c)
            cn = [z.n for z in reps(c)]
            h = hist.get(sh)
            hist[sh] = (cn, evn)
            if h is None:
                continue
            d = []
            for a, b in zip(cn, h[0]):
                x = Lin(a) - Lin(b)
                if not x.is_const():
                    d = None
                    break
                d.append(x.k)
            if not d or not any(d):
                continue
            if evn < skip:
                continue
            res = period(c, evn - h[1], d)
            if not res:
                skip = evn + (evn - h[1])      # the other phases of the same cycle would fail in the same way
                continue
            Ts, g, gTs, gd = res
            # the branch may have fewer copies than the lemma needs: split those cases off
            rs = reps(c)
            ok = True
            subs = []
            for i, t in Ts.items():
                n = rs[i].n
                if cval(n) >= t:
                    continue
                if not is_var(n) or len(n.c) != 1 or list(n.c.values())[0] != 1:
                    ok = False
                    break
                subs.append((list(n.c)[0], t - cval(n)))
            if not ok:
                continue
            cur = c
            for v, need in subs:
                if v[0] == 'H':
                    STATS['huge_small'] += 1       # ASSUMPTION: huge blocks have >= HMIN > MAXT copies
                elif DEFECT[0] != 'no_small_cases':
                    for j in range(need):
                        cj = map_counts(cur, lambda i, n, j=j: subst_lin(subst_lin(n, v, j), v, None))
                        s.queue.append((cj, {}, 0, src, label + '; a free count is small', 0))
                cur = map_counts(cur, lambda i, n: subst_lin(n, v, need))
            i = s.find(g)
            if i is not None:
                s.edges.append((src, i, label))
                return
            i = s.add(g, gTs, gd)
            s.edges.append((src, i, label))
            if len(s.info) > s.maxn:
                raise RuntimeError('too many nodes')
            Ts, d = gTs, gd
            cs = s.cases(g, Ts, d)
            if cs == 'forever':
                s.forever += 1
                s.info[i]['forever'] = True
                return
            s.queue.extend((x, {}, 0, i, lab, 0) for x, lab in cs)
            return

    def save(s, path):
        """checkpoint: everything needed to continue after a restart"""
        import pickle
        st = {'search': s, 'pcache': _pcache, 'pfail': _pfail, 'fresh': _fresh, 'stats': STATS, 'used': s.used}
        with open(path + '.tmp', 'wb') as f:
            pickle.dump(st, f)
        os.replace(path + '.tmp', path)

    @staticmethod
    def load(path):
        import pickle
        st = pickle.load(open(path, 'rb'))
        _pcache.update(st['pcache'])
        _pfail.update(st['pfail'])
        _fresh[0] = st['fresh'][0]
        STATS.update(st['stats'])
        return st['search']

    used = 0.0

    def run(s, tmax=None, progress=None, ckpt=None, every=60):
        t0 = time.time()
        last = t0
        base = s.used
        while s.queue:
            item = s.queue.pop()
            try:
                s.branch(item)
            except RuntimeError as e:
                s.stuck.append((item[3], item[4], str(e)[:600]))
            s.used = base + time.time() - t0
            if ckpt and time.time() - last > every:
                s.save(ckpt)
                last = time.time()
            if tmax and time.time() - t0 > tmax:
                break
        if ckpt:
            s.save(ckpt)
        return not s.queue

    def run_old(s, tmax=None, progress=None):
        t0 = time.time()
        while s.queue:
            s.branch(s.queue.pop())
            if progress and s.branches % 200 == 0:
                progress('branches %d nodes %d shapes %d queue %d forever %d halts %d %.0fs' %
                         (s.branches, len(s.info), len(s.nodes), len(s.queue), s.forever, len(s.halts), time.time() - t0))
            if tmax and time.time() - t0 > tmax:
                return False
        return True


def start_from_run(M, minstep, hmin=1000):
    """The exact accelerated run from blank tape, stopped at the first jump after step minstep; blocks with at
    least hmin copies become huge free counts.  Returns (configuration, step, text of the exact configuration)."""
    S = accel.Sim(M)

    class Stop(Exception):
        pass

    def oj(rule, k):
        if S.c.steps >= minstep:
            raise Stop
    S.on_jump = oj
    accel.CROSS_EVENTS[0] = False        # the exact run uses the plain events
    try:
        S.run(10 ** 400)
    except Stop:
        pass
    accel.CROSS_EVENTS[0] = True
    c = S.c
    txt = str(c)
    g = map_counts(c, lambda i, n: Lin(fresh(True)) + HMIN if n >= hmin else Lin(n))
    g.ev = c.ev
    g.quiet = 0
    g.steps = Lin(0)
    return g, c.steps, txt


def main():
    M = sys.argv[1]
    mx = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    start = None
    ck0 = os.environ.get('CKPT')
    if os.environ.get('START') and not (ck0 and os.path.exists(ck0)):
        start, step, txt = start_from_run(M, float(os.environ['START']))
        print('start: exact run at step %d' % step)
        print('  ', txt[:400])
        print('  ', show(start)[:400])
    if os.environ.get('RATIO'):
        RATIO.update(json.load(open(os.environ['RATIO']))['signatures'])
    ck = os.environ.get('CKPT')
    if ck and os.path.exists(ck):
        S = Search.load(ck)
        print('continued from checkpoint: branches %d nodes %d queue %d' % (S.branches, len(S.info), len(S.queue)))
    else:
        S = Search(M, mx, start=start)
    done = S.run(tmax=float(os.environ.get('TMAX', 540)), ckpt=ck)
    print('CLOSED' if done and not S.stuck else 'QUEUE EMPTY, BUT STUCK BRANCHES' if done else 'NOT FINISHED',
          'branches', S.branches, 'nodes', len(S.info), 'shapes', len(S.nodes), 'queue', len(S.queue),
          'halting branches', len(S.halts), 'forever', S.forever, 'stuck', len(S.stuck),
          'assumptions used', STATS, 'ratio rules used', sorted(USED_RATIO), 'seconds %.0f' % S.used)
    for x in S.stuck[:10]:
        print('STUCK from node', x[0], x[1], x[2][:300])
    for h in S.halts[:10]:
        print('HALT from node', h[0], h[1], h[2][:300])
    if len(sys.argv) > 3:
        json.dump({'machine': M, 'closed': done, 'nodes': S.info, 'edges': S.edges, 'halts': S.halts, 'stuck': S.stuck, 'stats': STATS, 'ratio_rules_used': sorted(USED_RATIO)},
                  open(sys.argv[3], 'w'))


if __name__ == '__main__':
    main()
