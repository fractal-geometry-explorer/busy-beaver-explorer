"""Closed set of round classes for 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA (the method of the proof of id 31480).

A *node* is the tape at the end of a round, when state A arrives at the left end and the left block is used up:

    <A> 01001000 (01)^B T        (T: the tail, a short word; B: the size of the big block)

A *class* is (T, r, m): all such tapes with B = r mod m and B >= THR.  For a class the symbolic engine of accel.py
runs one round with B = r0 + m x, x >= 0 free (r0 the smallest value of the class).  The engine refuses every step
whose outcome depends on x; the cycle rules it uses are each proved for all values of their own variables; a rule
that eats d words of the left block per application is applied N(x) = N0 + (m / d) x times, which needs d | m.  When
d does not divide m the class is split (modulus lcm(m, d)).  A run ends
  * at the next node: tail T', big block B' = k' + c' x.  Every such B' must again lie in a class of the set
    (all residues k' + c' j mod m' are added: nothing about x is remembered), and k' >= THR;
  * in the halting transition: then every tape of the class halts;
  * undecided (reported; the set is then not closed).
The search starts from the node the real run (from blank tape) is at when B first exceeds THR.

usage (from the repo root; D = holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/py/closure):
  python3 D/closure.py bfs [OUT.json [SECONDS]]   search for the closed set (writes the certificate; keeps a
                                          checkpoint OUT.json.ckpt and continues from it when run again)
  python3 D/closure.py check CERT.json    re-run every class of a certificate and check closure (independent of bfs)
  python3 D/closure.py rounds SECONDS     print the nodes of the real run
"""
import json
import os
import sys
import time
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
from accel import Driver, Lin, NeedSplit, Pol, Sim, Undecided, compress  # noqa: E402

PREFIX = (0, 1, 0, 0, 1, 0, 0, 0)
WORD = (0, 1)
THR = 20000          # every class is the set of B >= THR in a residue class
ENVX = 10 ** 9 + 7   # value of x used only to *look for* cycles (rules found are proved for all values)
MAX_MOVES = 3000000


def canon(toks, need_lin=True):
    """Split an event's token list (after the head marker) into (prefix, word, count, tail) around its one big
    repeat: the repeat with a variable (need_lin) or the first repeat with count >= THR.  The repeat is made as
    long as possible and rotated as far left as it goes.  None if there is no such repeat or several."""
    toks = [t for t in toks if t != 'H']
    idx = [i for i, t in enumerate(toks) if isinstance(t, list) and isinstance(t[1], Lin)]
    if need_lin:
        if len(idx) != 1:
            return None
        i = idx[0]
    else:
        if idx:
            return None
        big = [i for i, t in enumerate(toks) if isinstance(t, list) and t[1] >= THR // 2]
        if len(big) != 1:
            return None
        i = big[0]

    def cells(ts):
        out = []
        for t in ts:
            if isinstance(t, list):
                out.extend(t[0] * t[1])
            else:
                out.append(t)
        return out
    pre, w, n, post = cells(toks[:i]), tuple(toks[i][0]), toks[i][1], cells(toks[i + 1:])
    L = len(w)
    changed = True
    while changed:
        changed = False
        while len(pre) >= L and tuple(pre[-L:]) == w:
            del pre[-L:]
            n = n + 1
            changed = True
        while pre and pre[-1] == w[-1]:
            x = pre.pop()
            w = (x,) + w[:-1]
            post.insert(0, x)
            changed = True
        while len(post) >= L and tuple(post[:L]) == w:
            del post[:L]
            n = n + 1
            changed = True
    while post and post[-1] == 0:
        post.pop()
    return tuple(pre), w, n, ''.join(map(str, post))


def is_node(toks, need_lin=True):
    c = canon(toks, need_lin)
    if c is None or c[0] != PREFIX or c[1] != WORD:
        return None
    return c[3], c[2]


def start(tail, count):
    """The node with tail `tail` and big count `count` (a number or a Lin)."""
    s = Sim()
    s.st = accel.EVSTATE
    toks = list(PREFIX) + [[WORD, count]] + [int(c) for c in tail]
    s.L = []
    s.R = list(reversed(toks))
    s.steps = Lin(0) if isinstance(count, Lin) else 0
    s.recompress()
    return s


def run_class(tail, r, m, rules, thr=None, max_moves=None):
    """One symbolic round from the class (tail, r mod m), B >= thr.  Returns a dict with 'kind' in
    node / halt / split / undecided."""
    thr = THR if thr is None else thr
    r0 = thr + (r - thr) % m
    s = start(tail, Lin(r0, {0: m}))
    d = Driver(s, True)
    d.rules = rules
    d.env = {0: ENVX}
    out = {}

    def on_event(d, toks):
        nd = is_node(toks)
        if nd is None:
            return False
        out["tail"], out["count"] = nd
        return True

    try:
        d.run(None, on_event, max_moves=max_moves or MAX_MOVES)
    except NeedSplit as e:
        return dict(kind="split", d=e.d, r0=r0, why=str(e))
    except Undecided as e:
        return dict(kind="undecided", r0=r0, why=str(e))
    if d.s.halt:
        return dict(kind="halt", r0=r0, steps=repr(d.s.steps))
    if not out:
        return dict(kind="undecided", r0=r0, why="no node within %d moves" % d.moves)
    n = out["count"]
    st = Pol.of(d.s.steps)
    return dict(kind="node", r0=r0, to=out["tail"], k=n.k, c=n.c[0], steps=[str(a) for a in st.a], moves=d.moves,
                jumps=d.jumps)


def lcm(a, b):
    return a * b // gcd(a, b)


def real_nodes(seconds=None, until_B=None):
    """Nodes of the run from blank tape: yields (event, steps, tail, B)."""
    d = Driver()
    t0 = time.time()
    res = []

    def on_event(d, toks):
        nd = is_node(toks, need_lin=False)
        if nd is not None:
            res.append((d.ev, d.s.steps, nd[0], nd[1]))
            if until_B is not None and nd[1] >= until_B:
                return True
        return seconds is not None and time.time() - t0 > seconds

    d.run(None, on_event)
    return res


def bfs(log=print, out=None, start_node=None, limit=None, ckpt=None, budget=None):
    rules = {}
    if start_node is None:
        ev, steps, tail, B = real_nodes(until_B=THR)[-1]
        log("real run: node with B = %d >= %d at step %d (event %d), tail %s" % (B, THR, steps, ev, tail))
    else:
        tail, B = start_node
        ev = steps = None
    classes = {}            # (tail, r, m) -> result
    mod = {}                # tail -> modulus its classes are kept at
    todo = [(tail, B, 0)]   # families: tail, k, c  (all B = k + c j, j >= 0)
    halts, undec = [], []
    nrun = 0
    t0 = time.time()
    if ckpt and os.path.exists(ckpt):
        # continue an interrupted search (the cycle rules are simply proved again when needed)
        st = json.load(open(ckpt))
        classes = {(t, r, m): res for t, r, m, res in st["classes"]}
        mod = st["mod"]
        todo = [tuple(f) for f in st["todo"]]
        halts = [k for k, res in classes.items() if res["kind"] == "halt"]
        undec = [k for k, res in classes.items() if res["kind"] == "undecided"]
        log("continuing from %s: %d classes, %d tails, queue %d" % (ckpt, len(classes), len(mod), len(todo)))
    saved = [time.time()]

    def save(cur=None):
        if not ckpt:
            return
        st = dict(classes=[[t, r, m, res] for (t, r, m), res in classes.items()], mod=mod,
                  todo=todo + ([cur] if cur else []))
        json.dump(st, open(ckpt + ".tmp", "w"))
        os.replace(ckpt + ".tmp", ckpt)
        saved[0] = time.time()

    def explore(tail, r, m):
        """Prove the class or split it; returns nothing, fills classes/todo."""
        nonlocal nrun
        stack = [(r % m, m)]
        while stack:
            r, m = stack.pop()
            if (tail, r, m) in classes:
                continue
            t1 = time.time()
            res = run_class(tail, r, m, rules)
            nrun += 1
            if time.time() - t1 > 5:
                log("  slow run (%.0f s): tail %s B = %d mod %d: %s" % (time.time() - t1, tail, r, m, res))
            if res["kind"] == "split":
                m2 = lcm(m, res["d"])
                if tail not in mod or mod[tail] % m2:
                    mod[tail] = lcm(mod.get(tail, 1), m2)
                for j in range(m2 // m):
                    stack.append(((r + m * j) % m2, m2))
                continue
            classes[(tail, r, m)] = res
            if time.time() - saved[0] > 30:
                save(cur[0])
            if res["kind"] == "node":
                todo.append((res["to"], res["k"], res["c"]))
            elif res["kind"] == "halt":
                halts.append((tail, r, m))
                log("HALT class: tail %s B = %d mod %d: %s" % (tail, r, m, res))
            else:
                undec.append((tail, r, m))
                log("undecided class: tail %s B = %d mod %d: %s" % (tail, r, m, res["why"]))

    cur = [None]
    lastlog = [0]
    stopped = False
    while todo:
        if budget and time.time() - t0 > budget:
            stopped = True
            break
        tail, k, c = cur[0] = todo.pop()
        m = mod.get(tail)
        if m is None:
            # first visit of this tail: probe with modulus 3 (a visit eats three words) to learn its modulus
            m0 = 3
            explore(tail, k % m0, m0)
            if tail not in mod:
                mod[tail] = m0
            m = mod[tail]
        g = gcd(m, c) if c else m
        for j in range(m // g if c else 1):
            r = (k + c * j) % m
            if not any((tail, r % mm, mm) in classes for mm in set([m, c] if c else [m]) if mm and m % mm == 0
                       and (c % mm == 0 if c else True)):
                explore(tail, r, m)
        if limit and nrun > limit:
            stopped = True
            break
        if nrun // 200 != lastlog[0]:
            lastlog[0] = nrun // 200
            log("  ... %d runs, %d classes, %d tails, queue %d, %.0f s" % (nrun, len(classes), len(mod), len(todo),
                                                                         time.time() - t0))
    log("runs %d, classes %d, tails %d, halting classes %d, undecided %d, cycle rules %d, %.0f s"
        % (nrun, len(classes), len(mod), len(halts), len(undec), sum(len(v) for v in rules.values()),
           time.time() - t0))
    save()
    if stopped:
        log("stopped before the queue was empty (%d families left); run again to continue" % len(todo))
        return None, halts, undec
    cert = dict(machine=accel.MACHINE, thr=THR, prefix=''.join(map(str, PREFIX)), word=''.join(map(str, WORD)),
                classes=[dict(tail=t, r=r, m=m, **res) for (t, r, m), res in sorted(classes.items())])
    if start_node is None:
        ev, steps, tail, B = real_nodes(until_B=THR)[-1]
        cert["start"] = dict(tail=tail, B=B, steps=steps, event=ev)
    else:
        cert["start"] = dict(tail=start_node[0], B=start_node[1])
    if out:
        json.dump(cert, open(out, "w"), indent=0)
    return cert, halts, undec


def covered(index, tail, k, c, thr):
    """Is every B = k + c j (j >= 0) in a class of the certificate?  index: tail -> list of (r, m)."""
    if k < thr:
        return False
    cl = index.get(tail, [])
    if c == 0:
        return any(k % m == r for r, m in cl)
    M = 1
    for r, m in cl:
        M = lcm(M, m)
    period = M // gcd(M, c)
    return all(any((k + c * j) % m == r for r, m in cl) for j in range(period))


def check(cert, log=print, rerun=True, reach=True, max_moves=None):
    """Check a certificate from scratch: every class (or, for the mutation tests, the classes whose indices are in
    `rerun`) is re-run symbolically (fresh rule cache), its result compared,
    every result must be a node (no halt, nothing undecided) whose family is covered, with k >= THR; the real run
    must arrive in a class.  Returns (ok, list of problems)."""
    bad = []
    thr = cert["thr"]
    index = {}
    for c in cert["classes"]:
        index.setdefault(c["tail"], []).append((c["r"], c["m"]))
    rules = {}
    for ci, c in enumerate(cert["classes"]):
        rerun_c = rerun if isinstance(rerun, bool) else ci in rerun
        if not (0 <= c["r"] < c["m"]):
            bad.append("class %s %d mod %d: bad residue" % (c["tail"], c["r"], c["m"]))
            continue
        res = run_class(c["tail"], c["r"], c["m"], rules, thr, max_moves) if rerun_c else c
        if res["kind"] != "node":
            bad.append("class %s %d mod %d: %s %s" % (c["tail"], c["r"], c["m"], res["kind"], res.get("why", "")))
            continue
        if rerun_c and any(res[f] != c.get(f) for f in ("to", "k", "c", "steps", "r0")):
            bad.append("class %s %d mod %d: result differs from the certificate" % (c["tail"], c["r"], c["m"]))
        if res["c"] <= 0 or Pol([__import__("fractions").Fraction(a) for a in res["steps"]]).at(0) <= 0:
            bad.append("class %s %d mod %d: degenerate round" % (c["tail"], c["r"], c["m"]))
        if not covered(index, res["to"], res["k"], res["c"], thr):
            bad.append("class %s %d mod %d: successor family %s, %d + %d j not covered"
                       % (c["tail"], c["r"], c["m"], res["to"], res["k"], res["c"]))
    st = cert["start"]
    if reach:
        nodes = real_nodes(until_B=thr)
        ev, steps, tail, B = nodes[-1]
        if (tail, B) != (st["tail"], st["B"]) or steps != st.get("steps"):
            bad.append("the real run arrives at another node than the certificate says")
    if not covered(index, st["tail"], st["B"], 0, thr):
        bad.append("the start node is in no class")
    if log:
        log("classes %d, tails %d, cycle rules proved %d, problems %d" % (len(cert["classes"]), len(index),
                                                                        sum(len(v) for v in rules.values()), len(bad)))
    return not bad, bad


def main(argv):
    cmd = argv[1] if len(argv) > 1 else ""
    if cmd == "bfs":
        out = argv[2] if len(argv) > 2 else None
        cert, halts, undec = bfs(out=out, ckpt=(out + ".ckpt") if out else None,
                                 budget=float(argv[3]) if len(argv) > 3 else None)
        if cert is None:
            return 2
        print("CLOSED, no halting class" if not halts and not undec else "NOT CLOSED")
        return 0 if not halts and not undec else 1
    if cmd == "check":
        ok, bad = check(json.load(open(argv[2])))
        for b in bad[:40]:
            print("  " + b)
        print("certificate:", "CHECKED" if ok else "FAILED")
        return 0 if ok else 1
    if cmd == "rounds":
        for ev, steps, tail, B in real_nodes(seconds=float(argv[2])):
            print(len(str(steps)), B if B < 10 ** 30 else "%d digits" % len(str(B)), B % 3, tail)
        return 0
    print(__doc__)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
