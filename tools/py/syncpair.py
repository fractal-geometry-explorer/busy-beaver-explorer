#!/usr/bin/env python3
"""Two machines that part and rejoin: find a re-sync certificate and write it as a Lean proof (`TM.Sync`).

A *pair* (p, q) means: the two machines X and Y have the same tape and head cell, X is in p, Y in q, and the
configuration is on X's run from blank tape.  X's run is covered by a closed tape language (two automata and a set
S of abstract configurations): windows of W cells (`bbtools.ctl.search`), or with `--sat` two small DFAs found by
SAT (satctl's encoding without its no-halt clauses) in a loop that forbids every tape context where the search
below failed.  For each pair and each abstract configuration of X in state p, the cells near the head are expanded
along the automata, one cell at a time as a machine reads past what is known, until X after n >= 1 steps and Y after
m >= 1 steps have the same tape and head again (a new pair), or both halt.  If every pair reachable from (A, A)
closes, `TM.Sync.halts_iff` proves that X halts from blank tape iff Y does.

usage: python3 tools/py/syncpair.py find X Y OUT.json [--window W | --sat]
       python3 tools/py/syncpair.py lean OUT.json NAMESPACE > File.lean
       python3 tools/py/syncpair.py resync X Y N      run both N steps from blank tape, re-syncing at every
                                                       break, and count the breaks by (pair, symbol, n, m)
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bbtools import ctl  # noqa: E402

S_ = "ABCDEF"
DEEP = 24


def parse(m, mirror=False):
    t = {}
    for i, row in enumerate(m.split("_")):
        for x in range(2):
            p = row[3 * x:3 * x + 3]
            if p[0] == "-":
                t[(i, x)] = None
            else:
                d = 1 if p[1] == "R" else -1
                if mirror:
                    d = -d
                t[(i, x)] = (int(p[0]), d, S_.index(p[2]))
    return t


def mirror_text(m):
    return "_".join("".join("---" if row[3*x] == "-" else row[3*x] + ("L" if row[3*x+1] == "R" else "R") + row[3*x+2]
                            for x in range(2)) for row in m.split("_"))


class Need(Exception):
    def __init__(self, side):
        self.side = side


def wrun(t, s, wl, wr, n):
    """n steps on the window (wl nearest first, wr head first). ('ok', wl, wr, s) / ('halt', k) / raises Need."""
    wl, wr = list(wl), list(wr)
    for k in range(n):
        if not wr:
            raise Need("R")
        a = wr[0]
        tr = t[(s, a)]
        if tr is None:
            return ("halt", k)
        w, d, s2 = tr
        if d == 1:
            wl = [w] + wl
            wr = wr[1:]
        else:
            if not wl:
                raise Need("L")
            wr = [wl[0], w] + wr[1:]
            wl = wl[1:]
        s = s2
    return ("ok", wl, wr, s)


def halts_in(t, s, wl, wr, K):
    """Number of steps to a halting configuration within K, or None. Raises Need."""
    wl, wr = list(wl), list(wr)
    for k in range(K + 1):
        if not wr:
            raise Need("R")
        tr = t[(s, wr[0])]
        if tr is None:
            return k
        if k == K:
            return None
        w, d, s2 = tr
        if d == 1:
            wl, wr = [w] + wl, wr[1:]
        else:
            if not wl:
                raise Need("L")
            wr, wl = [wl[0], w] + wr[1:], wl[1:]
        s = s2
    return None


def solve(tx, ty, p, q, wl, wr, K):
    """('sync', n, m, p2, q2) | ('halt', n, m) | ('fail',). Raises Need when more cells are needed."""
    # trajectories, computed lazily by prefix
    for s in range(2, 2 * K + 1):
        for n in range(max(1, s - K), min(K, s - 1) + 1):
            m = s - n
            rx = wrun(tx, p, wl, wr, n)
            if rx[0] == "halt":
                continue
            ry = wrun(ty, q, wl, wr, m)
            if ry[0] == "halt":
                continue
            if rx[1] == ry[1] and rx[2] == ry[2]:
                return ("sync", n, m, rx[3], ry[3])
    hx = halts_in(tx, p, wl, wr, K)
    hy = halts_in(ty, q, wl, wr, K)
    if hx is not None and hy is not None:
        return ("halt", hx, hy)
    return ("fail",)


class Fail(Exception):
    pass


def build(tx, ty, AL, AR, p, q, wl, ql, wr, qr, K, budget, depth=0):
    """Certificate tree: ('sync', n, m, p2, q2) | ('halt', n, m) | ('L', [children]) | ('R', [children])."""
    budget[0] -= 1
    if budget[0] < 0:
        raise Fail("budget")
    try:
        r = solve(tx, ty, p, q, wl, wr, K)
    except Need as e:
        if depth > DEEP:
            raise Fail(("deep", S_[p] + S_[q], wl[::-1], wr))
        if e.side == "R":
            return ("R", [build(tx, ty, AL, AR, p, q, wl, ql, wr + [x], q1, K, budget, depth + 1)
                          for x, q1 in AR.pops(qr)])
        return ("L", [build(tx, ty, AL, AR, p, q, wl + [x], q1, wr, qr, K, budget, depth + 1)
                      for x, q1 in AL.pops(ql)])
    if r[0] == "fail":
        raise Fail(("nosync", S_[p] + S_[q], wl[::-1], wr))
    return r


def leaves(c):
    if c[0] in ("L", "R"):
        for ch in c[1]:
            yield from leaves(ch)
    else:
        yield c


def closure(X, Y, mirror=False, W=4, K=40, budget=200000, start=(0, 0), cset=None):
    tx, ty = parse(X), parse(Y, mirror)
    AL, AR, S = cset if cset else ctl.search(X, W)
    pairs, todo, certs = {start}, [start], {}
    bud = [budget]
    while todo:
        p, q = todo.pop()
        for (s, ql, qr) in S:
            if s != p:
                continue
            c = build(tx, ty, AL, AR, p, q, [], ql, [], qr, K, bud)
            certs[(p, q, ql, qr)] = c
            for lf in leaves(c):
                if lf[0] == "sync" and (lf[3], lf[4]) not in pairs:
                    pairs.add((lf[3], lf[4]))
                    todo.append((lf[3], lf[4]))
    return (AL, AR, S), sorted(pairs), certs




# ---- SAT-found invariants (needs python-sat, imported only when used)


class OutAuto:
    """Outward automaton (nearest cell first) in TM.CTL's form, from a far-to-head DFA."""

    def __init__(self, D):
        self.n = len(D)
        self.edges = sorted({(j, c, i) for i in range(len(D)) for c in (0, 1) for j in D[i][c]})
        self.acc = [0]
        self._pops = {}
        for (a, c, b) in self.edges:
            self._pops.setdefault(a, []).append((c, b))

    def pops(self, q):
        out = list(self._pops.get(q, []))
        if q in self.acc:
            out.append((0, q))
        return out


def closure_set(m, DL, DR):
    """Least closed set from the start; halting transitions allowed (skipped)."""
    import satctl
    T = satctl.parse(m)
    nL, nR = len(DL), len(DR)
    predR = {(r, b): [rp for rp in range(nR) if r in DR[rp][b]] for r in range(nR) for b in (0, 1)}
    predL = {l: [(lp, c) for lp in range(nL) for c in (0, 1) if l in DL[lp][c]] for l in range(nL)}
    seen = {(0, 0, 0)}
    todo = [(0, 0, 0)]
    while todo:
        q, l, r = todo.pop()
        for b in (0, 1):
            for rp in predR[(r, b)]:
                tr = T[(q, b)]
                if tr is None:
                    continue
                w, d, q2 = tr
                nxt = ([(q2, l2, rp) for l2 in DL[l][w]] if d == "R" else
                       [(q2, lp, r3) for (lp, c) in predL[l] for r2 in DR[rp][w] for r3 in DR[r2][c]])
                for x in nxt:
                    if x not in seen:
                        seen.add(x)
                        todo.append(x)
    return sorted(seen)


_SAT = {}


def _sat_build(m, nL, nR, nfa):
    """satctl.build with its no-halt clauses taken out (its source, edited once and cached)."""
    if "f" not in _SAT:
        import satctl
        src = open(os.path.join(HERE, "satctl.py")).read()
        body = src[src.index("def build("):src.index("def solve(")].replace("def build(", "def _sat_build(")
        old = """        if tr is None:
            for l in range(nL):
                for rp in range(nR): cl.append([-P(l,rp)])
            continue"""
        assert old in body
        body = body.replace(old, "        if tr is None:\n            continue")
        ns = dict(satctl.__dict__)
        exec(body, ns)
        _SAT["f"] = ns["_sat_build"]
    return _SAT["f"](m, nL, nR, nfa)


def sat_build(m, nL, nR, forbid, nfa="dd"):
    """satctl's clauses minus the no-halt clauses, plus the forbidden contexts (state, left word, right word),
    words nearest first."""
    pool, cl = _sat_build(m, nL, nR, nfa)
    dL = lambda i, c, j: pool.id(("dL", i, c, j))
    dR = lambda i, c, j: pool.id(("dR", i, c, j))
    s = lambda q, l, r: pool.id(("s", q, l, r))
    for fi, (p, u, v) in enumerate(forbid):
        tvars = {}
        for side, word, n, d in (("L", u, nL, dL), ("R", v, nR, dR)):
            prev = None
            for k, c in enumerate(reversed(word), 1):     # read from the far end toward the head
                cur = {j: pool.id(("t", fi, side, k, j)) for j in range(n)}
                for j in range(n):
                    for j2 in range(n):
                        cl.append(([] if prev is None else [-prev[j]]) + [-d(j, c, j2), cur[j2]])
                prev = cur
            tvars[side] = prev
        for l in range(nL):
            for r in range(nR):
                c = [-s(p, l, r)]
                if tvars["L"] is not None:
                    c.append(-tvars["L"][l])
                if tvars["R"] is not None:
                    c.append(-tvars["R"][r])
                cl.append(c)
    return pool, cl


def sat_solve(m, nL, nR, forbid, nfa="dd"):
    from pysat.solvers import Cadical153
    pool, cl = sat_build(m, nL, nR, forbid, nfa)
    S = Cadical153(bootstrap_with=cl)
    if not S.solve():
        return None
    model = set(x for x in S.get_model() if x > 0)
    get = lambda *a: pool.id(a) in model
    DL = [[[j for j in range(nL) if get("dL", i, c, j)] for c in (0, 1)] for i in range(nL)]
    DR = [[[j for j in range(nR) if get("dR", i, c, j)] for c in (0, 1)] for i in range(nR)]
    return DL, DR


def run(X, Y, mirror=False, sizes=((2, 2), (3, 3), (4, 4), (5, 5), (6, 6)), K=40, maxit=300, log=print):
    forbid = []
    for (nL, nR) in sizes:
        for it in range(maxit):
            r = sat_solve(X, nL, nR, forbid)
            if r is None:
                log(f"  {nL}x{nR}: UNSAT with {len(forbid)} forbidden contexts")
                break
            DL, DR = r
            S = closure_set(X, DL, DR)
            AL, AR = OutAuto(DL), OutAuto(DR)
            try:
                cs, pairs, certs = closure(X, Y, mirror, cset=(AL, AR, S), K=K)
                return {"DL": DL, "DR": DR, "S": S, "pairs": pairs, "certs": certs, "forbid": forbid}
            except Fail as e:
                info = e.args[0]
                if not isinstance(info, tuple):
                    log(f"  {nL}x{nR}: bisim {info}")
                    return None
                _, pq, wl_far, wr = info
                p = "ABCDEF".index(pq[0])
                forbid.append((p, list(reversed(wl_far)), list(wr)))
    return None



# ---- the concrete product run

def trajectory(t, s, h, tape, K):
    """Up to K steps from (s, h) on `tape`, without changing it: [(state, head, cells written so far)]."""
    w, out = {}, [(s, h, {})]
    for _ in range(K):
        a = w.get(h, tape.get(h, 0))
        tr = t[(s, a)]
        if tr is None:
            break
        b, d, s = tr
        w[h] = b
        h += d
        out.append((s, h, dict(w)))
    return out


def resync(X, Y, mir, N, K=40):
    """Both machines on one tape from blank: a common step where they agree; at a break, the first (n, m) in the
    order of `solve` after which they have the same tape and head again.  Returns (kind, steps, [pair], counts)
    with kind ok, bothhalt or fail, and the breaks counted by (pair, symbol, n, m)."""
    tx, ty = parse(X), parse(Y, mir)
    tape, h, p, q, steps, used = {}, 0, 0, 0, 0, {}
    while steps < N:
        a = tape.get(h, 0)
        u, v = tx[(p, a)], ty[(q, a)]
        if u is None and v is None:
            return ("bothhalt", steps, used)
        if u is not None and v is not None and u[:2] == v[:2]:
            tape[h] = u[0]
            h += u[1]
            p, q = u[2], v[2]
            steps += 1
            continue
        ax, ay = trajectory(tx, p, h, tape, K), trajectory(ty, q, h, tape, K)
        found = None
        for s in range(2, 2 * K + 1):
            for n in range(max(1, s - K), min(K, s - 1) + 1):
                m = s - n
                if n >= len(ax) or m >= len(ay):
                    continue
                (_, hx, wx), (_, hy, wy) = ax[n], ay[m]
                if hx == hy and all(wx.get(c, tape.get(c, 0)) == wy.get(c, tape.get(c, 0)) for c in set(wx) | set(wy)):
                    found = (n, m)
                    break
            if found:
                break
        if not found:
            return ("fail", steps, S_[p] + S_[q], used)
        n, m = found
        key = (S_[p] + S_[q], a, n, m)
        used[key] = used.get(key, 0) + 1
        tape.update(ax[n][2])
        h, p, q = ax[n][1], ax[n][0], ay[m][0]
        steps += n
    return ("ok", steps, used)


# ---- the Lean file

def table(m, name, doc):
    out = [f"/-- {doc} -/", f"def {name} : St → Bool → Option (Bool × Dir × St)"]
    for i, row in enumerate(m.split("_")):
        for x in range(2):
            p = row[3 * x:3 * x + 3]
            b = "true" if x else "false"
            if p[0] == "-":
                out.append(f"  | .{S_[i]}, {b} => none")
            else:
                w = "true" if p[0] == "1" else "false"
                out.append(f"  | .{S_[i]}, {b} => some ({w}, .{p[1]}, .{p[2]})")
    return "\n".join(out)


def wrap(items, indent="  ", width=116):
    lines, cur = [], indent
    for i, it in enumerate(items):
        s = it + ("," if i < len(items) - 1 else "")
        if len(cur) + len(s) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += s + " "
    if cur.strip():
        lines.append(cur.rstrip())
    return "\n".join(lines)


def auto(A):
    e = [f"({a}, {'true' if x else 'false'}, {b})" for (a, x, b) in A["edges"]]
    return "⟨[\n" + wrap(e, "    ") + f"],\n  {A['acc']}⟩"


def tree(t):
    k = t[0]
    if k == "sync":
        return f".sync {t[1]} {t[2]}"
    if k == "halt":
        return f".halt {t[1] + 1} {t[2] + 1}"
    side = ".left" if k == "L" else ".right"
    return f"{side} [" + ", ".join(tree(c) for c in t[1]) + "]"


def depth(t):
    return 1 + (max(depth(c) for c in t[1]) if t[0] in ("L", "R") else 0)


def lean_file(C, ns):
    """The Lean file for a certificate (the JSON written by `find`)."""
    out = []
    X, Y = C["X"], C["Y"]
    S = [tuple(a) for a in C["S"]]
    pairs = [tuple(p) for p in C["pairs"]]
    certs = {tuple(map(int, k.split(","))): v for k, v in C["certs"].items()}
    lists = []
    fuel = 1
    for (p, q) in pairs:
        row = []
        for (s, ql, qr) in S:
            if s == p:
                t = certs[(p, q, ql, qr)]
                fuel = max(fuel, depth(t) + 1)
                row.append(tree(t))
        lists.append("[" + ", ".join(row) + "]")
    out.append(f"""import TM.Sync

/-!
# {X} and {Y} halt together

The two machines run on the same tape and part only for a few steps at a time: from every configuration of the run
of {X} where the two runs are together, both halt, or the first after `n ≥ 1` steps and the second after `m ≥ 1`
steps have the same tape and head again.  Which configurations the first machine's run reaches is given by a closed
tape language ({len(C['AL']['edges'])} + {len(C['AR']['edges'])} automaton edges, {len(S)} abstract configurations); the
certificate has one tree per pair of states and abstract configuration, checked by `decide` (`TM.Sync.checkAll`).
`TM.Sync.halts_iff` then gives: one machine halts from blank tape if and only if the other does.

Generated by `tools/py/syncpair.py`; do not edit by hand.
-/

namespace {ns}

open TM

inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

{table(X, "transX", "The table of " + X + ".")}

{table(Y, "transY", "The table of " + Y + ".")}

/-- The left automaton (nearest cell first). -/
def autL : TM.CTL.Auto := {auto(C['AL'])}

/-- The right automaton (head cell first). -/
def autR : TM.CTL.Auto := {auto(C['AR'])}

/-- The abstract configurations of the first machine's run (state, left automaton state, right automaton state). -/
def absS : List (St × Nat × Nat) := [
{wrap([f"(.{S_[s]}, {l}, {r})" for (s, l, r) in S])}]

/-- The pairs of states (first machine, second machine) at which the runs are together. -/
def pairs : List (St × St) := [{", ".join(f"(.{S_[p]}, .{S_[q]})" for p, q in pairs)}]

/-- One certificate tree for each pair and each abstract configuration in the pair's first state. -/
def certs : List (List TM.Sync.Cert) := [
{wrap(lists)}]

theorem closed : TM.CTL.closed transX autL autR absS = true := by decide
theorem starts : TM.CTL.starts autL autR absS .A = true := by decide
theorem checked : TM.Sync.checkAll transX transY autL autR pairs absS certs {fuel} = true := by decide

/-- {X} halts from blank tape if and only if {Y} does. -/
theorem halts_iff : TM.Halts transX (TM.blankCfg .A) ↔ TM.Halts transY (TM.blankCfg .A) :=
  TM.Sync.halts_iff closed starts checked (by decide)

end {ns}""")
    return "\n".join(out)


def dump(X, Y, mirror, AL, AR, S, pairs, certs):
    return {"X": X, "Y": Y, "mirror": mirror,
            "AL": {"edges": [list(e) for e in AL.edges], "acc": list(AL.acc)},
            "AR": {"edges": [list(e) for e in AR.edges], "acc": list(AR.acc)},
            "S": [list(a) for a in S], "pairs": [list(p) for p in pairs],
            "certs": {",".join(map(str, k)): v for k, v in certs.items()}}


def main(argv):
    if argv[0] == "find":
        X, Y, out = argv[1], argv[2], argv[3]
        if "--sat" in argv:
            res = run(X, Y)
            if res is None:
                print("OPEN")
                return 1
            AL, AR, S = OutAuto(res["DL"]), OutAuto(res["DR"]), res["S"]
            pairs, certs = res["pairs"], res["certs"]
        else:
            W = int(argv[argv.index("--window") + 1]) if "--window" in argv else 4
            try:
                (AL, AR, S), pairs, certs = closure(X, Y, False, W)
            except Fail as e:
                print("OPEN", e)
                return 1
        json.dump(dump(X, Y, False, AL, AR, S, pairs, certs), open(out, "w"))
        print("CLOSED", len(S), "abstract configurations,", len(pairs), "pairs")
        return 0
    if argv[0] == "lean":
        print(lean_file(json.load(open(argv[1])), argv[2]))
        return 0
    if argv[0] == "resync":
        r = resync(argv[1], argv[2], False, int(float(argv[3])))
        print(r[0], r[1:-1])
        for k, v in sorted(r[-1].items()):
            print(" ", k, v)
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
