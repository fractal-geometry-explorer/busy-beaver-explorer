#!/usr/bin/env python3
"""Write lean/Insert_<partner>.lean for two holdouts with one table, whose runs differ by one inserted word.

    python3 holdouts/insert_pair.py X Y SHORT NSHORT NLONG [QLO WORD]   # writes holdouts/X/lean/Insert_<Y's first 13 chars>.lean

Y is X's table started in another state (possibly mirrored); `startstate` finds which.  SHORT is the machine whose
configuration lacks the word ("X" or "Y"), NSHORT and NLONG the steps after which the short run's configuration,
with one word inserted, is the long run's (as `tools/c/inslock.c` finds them).  The Lean file proves (with
`TM.halts_iff_of_good`, tools/lean/TM/Insert.lean) that **if the followed run of the short configuration never
reaches a bad moment (`GoodPair`), X halts from blank tape if and only if Y does**.  `GoodPair` is not proved:
`tools/c/inslock.c` checks it on a finite part of the run.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
L = "ABCDEF"


def parse(text):
    m = {}
    for i, row in enumerate(text.split("_")):
        for x in range(2):
            p = row[3 * x:3 * x + 3]
            m[(i, x)] = None if p[2] == "-" else (int(p[0]), p[1], ord(p[2]) - 65)
    return m


def startstate(x, y):
    """(s, mirror, f) with Y's run = X's table from state s (mirrored if `mirror`), f: X state -> Y state."""
    a, b = parse(x), parse(y)
    for mir in (False, True):
        for s in range(6):
            f = {s: 0}
            todo = [s]
            ok = True
            while todo and ok:
                q = todo.pop()
                for sym in (0, 1):
                    ta, tb = a[(q, sym)], b[(f[q], sym)]
                    if (ta is None) != (tb is None):
                        ok = False; break
                    if ta is None:
                        continue
                    d = ta[1] if not mir else {"L": "R", "R": "L"}[ta[1]]
                    if ta[0] != tb[0] or d != tb[1]:
                        ok = False; break
                    if ta[2] in f:
                        if f[ta[2]] != tb[2]:
                            ok = False; break
                    else:
                        f[ta[2]] = tb[2]; todo.append(ta[2])
            if ok and len(f) == 6 and len(set(f.values())) == 6:
                return s, mir, f
    raise SystemExit("not the same table")


def run(m, s, n):
    """The finite configuration of `TM.fsteps` after n steps from blank tape in state s: (l, r, state)."""
    l, r, st = [], [], s
    for _ in range(n):
        y = r[0] if r else 0
        t = m[(st, y)]
        if t is None:
            raise SystemExit("halts")
        w, d, ns = t
        if d == "R":
            l = [w] + l; r = r[1:]
        else:
            r = [l[0] if l else 0, w] + r[1:]; l = l[1:]
        st = ns
    return l, r, st


def pad(a, k):
    return a + [0] * (k - len(a))


def find_ins(cs, cl):
    """(right, n, v, rest) with the longer configuration = the shorter plus v; prefers the insertion farthest from
    the head.  Lists are compared after padding with blanks."""
    (ls, rs, ss), (ll, rl, sl) = cs, cl
    assert ss == sl
    K = max(len(ls), len(ll), len(rs), len(rl)) + 1
    best = None
    if pad(ls, K) == pad(ll, K):
        for k in range(1, len(rl) + 1):
            for n in range(1, len(rl) - k + 1):
                u, v, rest = rl[:n], rl[n:n + k], rl[n + k:]
                if pad(rs, K) == pad(u + rest, K):
                    best = (True, n, v, rest)
            if best: break
    if best is None and pad(rs, K) == pad(rl, K):
        for k in range(1, len(ll) + 1):
            for n in range(0, len(ll) - k + 1):
                u, v, rest = ll[:n], ll[n:n + k], ll[n + k:]
                if pad(ls, K) == pad(u + rest, K):
                    best = (False, n, v, rest)
            if best: break
    if best is None:
        raise SystemExit("no single insertion relates the two configurations")
    return best


def from_at(cs, cl, qlo, word):
    """The insertion as `tools/c/inslock.c` prints it: boundary `qlo` cells right of the leftmost written cell (or the
    head, if further left) of the shorter tape, word left to right."""
    (ls, rs, ss), (ll, rl, sl) = cs, cl
    v = [int(ch) for ch in word]
    lo = -len(ls)                      # head at 0; ls[i] is cell -(i+1)
    while lo < 0 and ls[-lo - 1] == 0:
        lo += 1
    q = lo + qlo
    K = max(len(ls), len(ll), len(rs), len(rl)) + len(v) + 2
    if q >= 1:
        n = q
        u, rest = pad(rs, n)[:n], rs[n:]
        assert pad(rl, K) == pad(u + v + rest, K) and pad(ls, K) == pad(ll, K), "not this insertion"
        return True, n, v, rest
    n = -q
    u, rest = pad(ls, n)[:n], ls[n:]
    vl = v[::-1]
    assert pad(ll, K) == pad(u + vl + rest, K) and pad(rs, K) == pad(rl, K), "not this insertion"
    return False, n, vl, rest


def lb(x):
    return "true" if x else "false"


def ll_(w):
    return "[" + ", ".join(lb(x) for x in w) + "]"


def namespace(machine):
    src = open(os.path.join(HERE, machine, "lean", "Machine.lean")).read()
    return re.search(r"^namespace (\w+)", src, re.M).group(1)


def generate(x, y, short, nshort, nlong, at=None):
    a, b = parse(x), parse(y)
    s, mir, f = startstate(x, y)
    ns = namespace(x)
    sx = s if short == "Y" else 0
    lx = 0 if short == "Y" else s
    nsx, nlx = (nshort, nlong)
    cs = run(a, sx, nsx)
    cl = run(a, lx, nlx)
    if at is None:
        right, n, v, rest = find_ins(cs, cl)
    else:
        right, n, v, rest = from_at(cs, cl, *at)
    tag = "Y" + re.sub(r"[^A-Za-z0-9]", "", y)[:12]
    trans_y = []
    for i in range(6):
        for sym in range(2):
            t = b[(i, sym)]
            rhs = "none" if t is None else f"some ({lb(t[0])}, .{t[1]}, .{L[t[2]]})"
            trans_y.append(f"  | .{L[i]}, {lb(sym)} => {rhs}")
    fmap = " | ".join(f".{L[q]} => .{L[f[q]]}" for q in range(6))
    if mir:
        partner = f"""theorem halts_partner : Halts trans (blankCfg .{L[s]}) ↔ Halts {tag}.trans (blankCfg .A) := by
  have := halts_of_map trans {tag}.trans (mirrorCfg fP)
    (step_mirrorCfg trans {tag}.trans fP (by intro q b; cases q <;> cases b <;> rfl)) (blankCfg .{L[s]})
  rw [mirrorCfg_blank] at this; exact this"""
    else:
        partner = f"""theorem halts_partner : Halts trans (blankCfg .{L[s]}) ↔ Halts {tag}.trans (blankCfg .A) :=
  halts_of_map trans {tag}.trans (renameCfg fP)
    (step_renameCfg trans {tag}.trans fP (by intro q b; cases q <;> cases b <;> rfl)) (blankCfg .{L[s]})"""
    (lsh, rsh, ssh), (llo, rlo, slo) = cs, cl
    side = "right" if right else "left"
    eqp = "(by simp only [app_app]; exact app_blank_eq _ _ (by decide))"
    if right:
        relproof = (f"relR rfl (app_blank_eq _ _ (by decide)) (by decide) {ll_(pad(rlo, n)[:n])} (app {ll_(rest)} blank) rfl\n"
                    f"    {eqp}\n    {eqp}")
    else:
        relproof = (f"relL rfl (app_blank_eq _ _ (by decide)) {ll_(pad(llo, n)[:n])} (app {ll_(rest)} blank) rfl\n"
                    f"    {eqp}\n    {eqp}")
    # short is X's table from sx, long from lx; X from A is the one that is not the partner's start
    if short == "Y":
        chain = ("rw [halts_iff_of_steps' trans (blank_reaches trans at_long), ← halts_partner,\n"
                 "    halts_iff_of_steps' trans (blank_reaches trans at_short)]\n"
                 "  exact (halts_iff_of_good trans rel0 h).symm")
    else:
        chain = ("rw [halts_iff_of_steps' trans (blank_reaches trans at_short), ← halts_partner,\n"
                 "    halts_iff_of_steps' trans (blank_reaches trans at_long)]\n"
                 "  exact halts_iff_of_good trans rel0 h")
    word = "".join(map(str, v))
    return f"""import Machine
import TM.Insert

/-!
# {x} and {y}: one run with one word more

Generated by `holdouts/insert_pair.py`; do not edit by hand.

{y} is this machine's table started in state {L[s]}{", mirrored" if mir else ""} (`halts_partner`).  After {nshort} steps of
the {"partner's" if short == "Y" else "this machine's"} run and {nlong} steps of the {"this machine's" if short == "Y" else "partner's"} run, the second configuration is the first with the word
`{word}` inserted {"right" if right else "left"} of the head after {n} cells (`at_short`, `at_long`, `rel0`).

`TM.halts_iff_of_good` (tools/lean/TM/Insert.lean) follows the run of the shorter configuration and the place and
contents of the inserted word: the head of the longer run crosses the word in the same state it entered (a
transparent crossing), or the word moves one cell along a matching cell (a shift).  `GoodPair` says that this never
fails.  Proved here:

* **`halt_together`**: if `GoodPair` holds, {x} halts from blank tape if and only if {y} does.

`GoodPair` is not proved; `tools/c/inscheck.c` checks it on a finite part of the run.  Kernel only (no `native_decide`).
-/

namespace {ns}

open TM

namespace {tag}

inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The table of {y}. -/
def trans : St → Bool → Option (Bool × Dir × St)
{chr(10).join(trans_y)}

end {tag}

/-- The partner's states. -/
def fP : St → {tag}.St
  | {fmap}

{partner}

/-- The shorter configuration. -/
def cShort : FCfg St := ⟨{ll_(lsh)}, {ll_(rsh)}, .{L[ssh]}⟩

/-- The longer configuration. -/
def cLong : FCfg St := ⟨{ll_(llo)}, {ll_(rlo)}, .{L[slo]}⟩

theorem at_short : TM.fsteps trans {nsx} (FCfg.blank .{L[sx]}) = some cShort := by decide

theorem at_long : TM.fsteps trans {nlx} (FCfg.blank .{L[lx]}) = some cLong := by decide

/-- Where the word is: {side} of the head after {n} cells. -/
def ins0 : Ins := ⟨{lb(right)}, {n}, {ll_(v)}⟩

theorem rel0 : Rel ins0 cShort.toCfg cLong.toCfg :=
  {relproof}

/-- The condition: the followed run of the shorter configuration never reaches a bad moment (the run on the word
gets 10,000 steps of fuel per crossing). -/
def GoodPair : Prop := Good trans 10000 ins0 cShort.toCfg

/-- **One halting question for two machines**, given `GoodPair`. -/
theorem halt_together (h : GoodPair) : Halts trans (blankCfg .A) ↔ Halts {tag}.trans (blankCfg .A) := by
  {chain}

end {ns}
"""


if __name__ == "__main__":
    x, y, short, nshort, nlong = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
    at = (int(sys.argv[6]), sys.argv[7]) if len(sys.argv) > 7 else None
    out = generate(x, y, short, nshort, nlong, at)
    tag = "Insert_" + re.sub(r"[^A-Za-z0-9]", "", y)[:13]
    path = os.path.join(HERE, x, "lean", tag + ".lean")
    open(path, "w").write(out)
    print(path)
