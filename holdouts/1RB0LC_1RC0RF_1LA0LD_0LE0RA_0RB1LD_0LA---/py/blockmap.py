"""The block map of 1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---: the machine as a rewriting system on lists of blocks of 1s.

`blk [a, b, c, ...]` is the tape `1^a 0 1^b 0 1^c 0 ...` (then blank), read away from the head on either side; a
block may be empty (`0 0` holds an empty block) and the empty list is blank tape.  Every configuration is a *frame*
`(q, L, R)`: state q, the tape left of the head is `blk L`, the tape from the head cell rightwards is `blk R`.

The block map sends a frame to the configuration the machine is in when it first needs a cell beyond the first
block of each side: with `L = l0 :: l1 :: L'` and `R = r0 :: r1 :: R'` it runs on `0 1^l0 q> 1^r0 0` until the head
would leave that window.  The result depends on (q, l0, r0) through finitely many cases, each one symbolic run of
`bbtools.symtm` that holds for all block lengths in its range and all tapes around (`table`).  Where the machine
works through a long block a few cells at a time (no single shift rule crosses it), the window holds only the first
MAXS cells of that block and the head stops when it needs the next one.  Where the machine
halts inside the window the case is *critical*; these are the only frames without a next frame.

usage (from the repository root):
  python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/blockmap.py table        print the cases
  python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/blockmap.py check STEPS  compare the map with the machine, step by step, for STEPS steps
  python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/blockmap.py run K        iterate the map K times from blank tape; frames, steps, blocks
  python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/blockmap.py lean         write lean/BPieces.lean and lean/Blocks.lean
  python3 holdouts/1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---/py/blockmap.py export       the table for c/blockrun.c (fast iteration, see there)
"""
import os
import re
import sys

M = "1RB0LC_1RC0RF_1LA0LD_0LE0RA_0RB1LD_0LA---"
K = 100000000          # frames checked by native_decide in lean/Blocks.lean
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import Config, Ctx, Halted, Lin, NeedSplit, Rep, TouchContext  # noqa: E402

ST = "ABCDEF"
MAXS = 6


def side_str(kind, s, v):
    if kind in ("eq", "tr"):
        return " ".join(["1"] * s)
    return f"(1)^{v}+{s}" if s else f"(1)^{v}"


def start_str(q, rl, rr):
    """Region kinds: eq s (exactly s cells), ge s (at least s; a variable block), tr s (at least s; only the first
    s cells are in the window)."""
    return " ".join(x for x in ["L" if rl[0] == "tr" else "L 0", side_str(*rl, "a"), ST[q] + ">", side_str(*rr, "b"),
                                "R" if rr[0] == "tr" else "0 R"] if x)


def advance(m, cfg):
    x = symtm.try_cross(m, cfg)
    if x is None:
        symtm.step(m, cfg)


class Zeros:
    """n empty blocks in a row (n cells 0), n a linear expression that is surely >= 0."""
    def __init__(self, n):
        self.n = n


def blocks(toks):
    """Blocks of a token list read away from the head: (closed blocks, cells of the last, open block).  A closed
    block is a length, or `Zeros(n)` for n empty blocks."""
    out, cur = [], Lin(0)
    for t in toks:
        if isinstance(t, Rep):
            if all(c == 1 for c in t.word):
                cur = cur + len(t.word) * t.n
                continue
            if t.n.is_const():
                sub, c2 = blocks(list(t.word) * t.n.k)
                if sub:
                    out.append(cur + sub[0]); out.extend(sub[1:]); cur = c2
                else:
                    cur = cur + c2
                continue
            assert all(c == 0 for c in t.word), ("repeat of a mixed word in a result", t)
            if not t.n.surely_ge(1):
                raise NeedSplit(t)
            out.append(cur); out.append(Zeros(len(t.word) * t.n - 1)); cur = Lin(0)
        elif t == 1:
            cur = cur + 1
        else:
            out.append(cur); cur = Lin(0)
    return out, cur


class Leaf:
    pass


def make_leaf(m, q, rl, rr):
    """Run the window (q, l0 in rl, r0 in rr) until the head needs a cell outside it.  Returns a Leaf, or raises
    NeedSplit with the variable to split on."""
    lf = Leaf(); lf.q, lf.rl, lf.rr = q, rl, rr
    lf.start = start_str(q, rl, rr)
    cfg = Config.parse(lf.start); lf.halt = False
    for _ in range(20000):
        prev = cfg.copy()
        try:
            advance(m, cfg)
        except TouchContext:
            cfg = prev; break
        except Halted:
            cfg = prev; lf.halt = True; break
    else:
        raise RuntimeError("no end: " + lf.start)
    lf.end = repr(cfg); lf.steps = cfg.steps; lf.q2 = cfg.state
    assert isinstance(cfg.left[0], Ctx) and isinstance(cfg.right[-1], Ctx), lf.end
    lf.lb, lf.lc = blocks(list(reversed(cfg.left[1:])))
    lf.rb, lf.rc = blocks(cfg.right[:-1])
    return lf


def build(m):
    leaves = []

    def go(q, rl, rr):
        try:
            leaves.append(make_leaf(m, q, rl, rr))
        except NeedSplit as e:
            v = sorted(e.args[0].n.vars())[0]
            if v == "a":
                if rl[1] >= MAXS:
                    go(q, ("tr", rl[1]), rr)
                else:
                    go(q, ("eq", rl[1]), rr); go(q, ("ge", rl[1] + 1), rr)
            else:
                if rr[1] >= MAXS:
                    go(q, rl, ("tr", rr[1]))
                else:
                    go(q, rl, ("eq", rr[1])); go(q, rl, ("ge", rr[1] + 1))
    for q in range(6):
        go(q, ("ge", 0), ("ge", 0))
    return leaves


def in_region(r, x):
    return x == r[1] if r[0] == "eq" else x >= r[1]


def un(X):
    return (X[0], X[1:]) if X else (0, ())


class Map:
    def __init__(self):
        self.m = Machine.parse(M)
        self.leaves = build(self.m)
        self.by = {q: [l for l in self.leaves if l.q == q] for q in range(6)}

    def nxt(self, f):
        """(next frame, machine steps), or None at a critical frame."""
        q, L, R = f
        l0, L1 = un(L); r0, R1 = un(R)
        for lf in self.by[q]:
            if in_region(lf.rl, l0) and in_region(lf.rr, r0):
                if lf.halt:
                    return None
                env = {"a": l0 - lf.rl[1], "b": r0 - lf.rr[1]}
                l1, L2 = un(L1); r1, R2 = un(R1)
                ev = lambda x: x.subs(env).k if isinstance(x.subs(env), Lin) else x.subs(env)
                evs = lambda xs: tuple(y for x in xs for y in ((0,) * ev(x.n) if isinstance(x, Zeros) else (ev(x),)))
                nl = evs(lf.lb) + ((ev(lf.lc) + env["a"],) + L1 if lf.rl[0] == "tr" else (ev(lf.lc) + l1,) + L2)
                nr = evs(lf.rb) + ((ev(lf.rc) + env["b"],) + R1 if lf.rr[0] == "tr" else (ev(lf.rc) + r1,) + R2)
                return (lf.q2, nl, nr), ev(lf.steps)
        raise AssertionError(f)


def pat(r, v):
    return str(r[1]) if r[0] == "eq" else (f"{v} + {r[1]}" if r[1] else v)


def crit_str(lf):
    return (f"`{ST[lf.q]}` with l0 {'= ' + str(lf.rl[1]) if lf.rl[0] == 'eq' else '≥ ' + str(lf.rl[1])}, "
            f"r0 {'= ' + str(lf.rr[1]) if lf.rr[0] == 'eq' else '≥ ' + str(lf.rr[1])}  (`{lf.start}`)")


def cells(X):
    out = []
    for a in X:
        out += [1] * a + [0]
    while out and out[-1] == 0:
        out.pop()
    return out


def check(mp, steps):
    T = mp.m.table
    tape = {}; p = 0; q = 0; lo = hi = 0
    f = (0, (), ()); due = 0; nf = 0; last = 0
    for n in range(0, steps + 1):
        if n == due:
            l = [tape.get(i, 0) for i in range(p - 1, lo - 1, -1)]
            r = [tape.get(i, 0) for i in range(p, hi + 1)]
            while l and l[-1] == 0: l.pop()
            while r and r[-1] == 0: r.pop()
            assert q == f[0] and l == cells(f[1]) and r == cells(f[2]), ("mismatch at step", n, f)
            nf += 1; last = n
            g = mp.nxt(f)
            if g is None:
                print("critical frame at step", n, f); return
            f = g[0]; due = n + g[1]
        w, d, q2 = T[q][tape.get(p, 0)]
        tape[p] = w; p += d; q = q2; lo = min(lo, p); hi = max(hi, p)
    print("machine steps", steps, ": the machine is at each of the", nf, "frames of the block map at the step the map says; last at step", last)


# ------------------------------------------------------------------------------------------------ Lean
def lean_list(bl, cur, v1, rest, tr=None):
    c = cur.lean()
    if tr:
        e = f"{tr if c == '0' else '(' + c + ' + ' + tr + ')'} :: {v1} :: {rest}"
    else:
        e = f"{v1 if c == '0' else '(' + c + ' + ' + v1 + ')'} :: {rest}"
    for x in reversed(bl):
        if isinstance(x, Zeros):
            e = f"List.replicate ({x.n.lean()}) 0 ++ ({e})"
        else:
            y = x.lean()
            e = f"{'(' + y + ')' if ' ' in y else y} :: {e}"
    return e


def lean(mp):
    ns = re.search(r"namespace (\S+)", open(os.path.join(HERE, "..", "lean", "Machine.lean")).read()).group(1)
    ths = []
    for i, lf in enumerate(mp.leaves):
        lf.name = f"bp{i}"
        doc = f"{lf.start}  ->  {lf.end}" + ("  (halts)" if lf.halt else "")
        lf.vars = sorted(Config.parse(lf.start).vars())
        if lf.steps.is_zero():      # the window's first step is the halting transition
            continue
        th, _ = symtm.prove(M, lf.name, lf.start, lf.end, doc=doc, max_seg=60)
        ths.append(th)
    pieces = symtm.rules_file("Machine", ns, ths, f"Pieces of the block map of {M}, generated by `py/blockmap.py`; do not edit.")
    crit = [crit_str(lf) for lf in mp.leaves if lf.halt]
    CL = "rep l1 [true] (cons false (blk L))"; CR = "rep r1 [true] (cons false (blk R))"
    o = []
    o.append(f"""import BPieces
import TM.ListFrame

/-!
# {M}: the block map

The machine as a rewriting system on lists of blocks of 1s.  `blk [a, b, c, ...]` is the tape `1^a 0 1^b 0 1^c 0 ...`
(then blank), read away from the head; a block may be empty, and the empty list is blank tape.  A frame `BF` is a
state `q` and two block lists: the tape left of the head is `blk l`, the tape from the head cell rightwards `blk r`.
Every configuration with finitely many 1s is a frame.

`next` runs the machine from a frame until the head first needs a cell beyond the first block of each side.  It is
a finite table on (state, first left block l0, first right block r0), {len(mp.leaves)} cases; each case is one symbolic run of
`BPieces.lean`, valid for all block lengths in its range and all tapes around, and `next_sound` says every value of
`next` is a run of at least one step of the machine.  `next` is undefined exactly at the *critical* frames
(`next_none_iff`, `crit`), where the machine halts before the head leaves the window (`none_halts`):

""" + "\n".join("* " + c for c in crit) + f"""

The run from blank tape is the frame `start = ⟨A, [], []⟩` (`init_start`).  `halts_iff_critical`: the machine halts
from blank tape iff the orbit of `start` under `next` reaches a critical frame.  `frames_{K}` checks by
`native_decide` that `next` is defined on the first {K} frames, so none of them is critical (`no_halt_frames`).
Generated by `py/blockmap.py`; do not edit.
-/

set_option maxRecDepth 20000

namespace {ns}

open TM

/-- Blocks of 1s, each followed by one 0, the first block next to the head; then blank tape. -/
def blk : List Nat → Tape
  | [] => blank
  | a :: R => rep a [true] (cons false (blk R))

/-- First block (an empty block if the list is empty, which is blank tape) and the rest. -/
def hd : List Nat → Nat
  | [] => 0
  | a :: _ => a

def tl : List Nat → List Nat
  | [] => []
  | _ :: R => R

theorem blk_ht : ∀ R : List Nat, blk R = rep (hd R) [true] (cons false (blk (tl R)))
  | [] => cons_false_blank.symm
  | _ :: _ => rfl

theorem blk_rep0 (n : Nat) (X : List Nat) : blk (List.replicate n 0 ++ X) = rep n [false] (blk X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.cons_append, blk, ih]; rfl

/-- A frame: state, blocks left of the head (nearest first), blocks from the head cell rightwards. -/
structure BF where
  q : St
  l : List Nat
  r : List Nat
  deriving DecidableEq, Repr

def BF.cfg (f : BF) : Config := ⟨blk f.l, blk f.r, f.q⟩

/-- `1^l1 0 1^l0  q>  1^r0 0 1^r1 0`, between `blk L` and `blk R`. -/
def c2 (q : St) (l0 l1 : Nat) (L : List Nat) (r0 r1 : Nat) (R : List Nat) : Config :=
  ⟨rep l0 [true] (cons false (rep l1 [true] (cons false (blk L)))),
   rep r0 [true] (cons false (rep r1 [true] (cons false (blk R)))), q⟩

theorem cfg2 (f : BF) :
    f.cfg = c2 f.q (hd f.l) (hd (tl f.l)) (tl (tl f.l)) (hd f.r) (hd (tl f.r)) (tl (tl f.r)) := by
  simp only [BF.cfg, c2, ← blk_ht]

theorem steps_eq_of {{n : Nat}} {{c c' d d' : Config}} (h : steps n c = some d) (hc : c = c') (hd : d = d') :
    steps n c' = some d' := by rw [← hc, ← hd]; exact h

theorem cfg_eq {{l l' r r' : Tape}} {{q : St}} (hl : l = l') (hr : r = r') :
    (⟨l, r, q⟩ : Config) = ⟨l', r', q⟩ := by rw [hl, hr]

/-- Two tapes made of cells, blocks and context tapes: write every cell as a run, merge runs of one symbol, then
match run by run, lengths by `omega`. -/
macro "blk_eq" : tactic =>
  `(tactic| focus
    try simp only [blk, blk_rep0, rep_zero]
    try simp only [cons_rep1]
    try simp only [rep1_rep1]
    repeat' (first | rfl | apply rep_congr')
    all_goals omega)
""")
    for q in range(6):
        ls = mp.by[q]
        o.append(f"/-- State {ST[q]}: the table on (l0, r0); `l1 :: L`, `r1 :: R` are the blocks behind the window. -/")
        o.append(f"def next{ST[q]} (l1 : Nat) (L : List Nat) (r1 : Nat) (R : List Nat) : Nat → Nat → Option BF")
        for lf in ls:
            p = f"  | {pat(lf.rl, 'a')}, {pat(lf.rr, 'b')} => "
            if lf.halt:
                o.append(p + "none")
            else:
                o.append(p + f"some ⟨.{ST[lf.q2]}, {lean_list(lf.lb, lf.lc, 'l1', 'L', 'a' if lf.rl[0] == 'tr' else None)}, {lean_list(lf.rb, lf.rc, 'r1', 'R', 'b' if lf.rr[0] == 'tr' else None)}⟩")
        o.append("")
        o.append(f"def crit{ST[q]} : Nat → Nat → Bool")
        for lf in ls:
            o.append(f"  | {pat(lf.rl, '_')}, {pat(lf.rr, '_')} => {'true' if lf.halt else 'false'}")
        o.append("")
    names = ", ".join("next" + s for s in ST)
    o.append(f"""/-- The block map. -/
def next (f : BF) : Option BF :=
  match f.q with
""" + "\n".join(f"  | .{s} => next{s} (hd (tl f.l)) (tl (tl f.l)) (hd (tl f.r)) (tl (tl f.r)) (hd f.l) (hd f.r)" for s in ST) + f"""

/-- The critical frames: the machine halts before the head leaves the window. -/
def crit (f : BF) : Bool :=
  match f.q with
""" + "\n".join(f"  | .{s} => crit{s} (hd f.l) (hd f.r)" for s in ST) + f"""

macro "piece" t:term:max : tactic =>
  `(tactic| focus
    simp only [{names}, Option.some.injEq] at *
    subst_vars
    simp only [c2, BF.cfg]
    refine ⟨_, ?_, steps_eq_of ($t) (cfg_eq (by blk_eq) (by blk_eq)) (cfg_eq (by blk_eq) (by blk_eq))⟩
    omega)

macro "hpiece" t:term:max : tactic =>
  `(tactic| focus
    simp only [c2]
    exact ⟨_, _, steps_eq_of ($t) (cfg_eq (by blk_eq) (by blk_eq)) rfl, rfl⟩)
""")
    for q in range(6):
        s = ST[q]; ls = mp.by[q]
        app = lambda lf: "(" + " ".join([lf.name] + lf.vars + [
            f"(rep a [true] (cons false ({CL})))" if lf.rl[0] == "tr" else f"({CL})",
            f"(rep b [true] (cons false ({CR})))" if lf.rr[0] == "tr" else f"({CR})"]) + ")"
        o.append(f"theorem next{s}_sound (l1 : Nat) (L : List Nat) (r1 : Nat) (R : List Nat) : ∀ (l0 r0 : Nat) (p' : BF),\n"
                 f"    next{s} l1 L r1 R l0 r0 = some p' → ∃ n, 0 < n ∧ steps n (c2 .{s} l0 l1 L r0 r1 R) = some p'.cfg")
        for lf in ls:
            p = f"  | {pat(lf.rl, 'a')}, {pat(lf.rr, 'b')}, _, h => by "
            o.append(p + (f"simp [next{s}] at h" if lf.halt else f"piece {app(lf)}"))
        o.append("")
        o.append(f"theorem next{s}_halts (l1 : Nat) (L : List Nat) (r1 : Nat) (R : List Nat) : ∀ (l0 r0 : Nat),\n"
                 f"    next{s} l1 L r1 R l0 r0 = none → TM.Halts trans (c2 .{s} l0 l1 L r0 r1 R)")
        for lf in ls:
            p = f"  | {pat(lf.rl, 'a')}, {pat(lf.rr, 'b')}, h => by "
            o.append(p + (f"simp [next{s}] at h" if not lf.halt else
                          "exact ⟨0, _, rfl, rfl⟩" if lf.steps.is_zero() else f"hpiece {app(lf)}"))
        o.append("")
        o.append(f"theorem next{s}_none (l1 : Nat) (L : List Nat) (r1 : Nat) (R : List Nat) : ∀ (l0 r0 : Nat),\n"
                 f"    next{s} l1 L r1 R l0 r0 = none ↔ crit{s} l0 r0 = true")
        for lf in ls:
            o.append(f"  | {pat(lf.rl, 'a')}, {pat(lf.rr, 'b')} => by simp [next{s}, crit{s}]")
        o.append("")
    o.append(f"""/-- **Every value of the block map is a run of the machine**, for all block lists. -/
theorem next_sound (p p' : BF) (h : next p = some p') : ∃ n, 0 < n ∧ steps n p.cfg = some p'.cfg := by
  obtain ⟨q, l, r⟩ := p
  rw [cfg2]
  cases q <;> simp only [next] at h
""" + "\n".join(f"  · exact next{s}_sound _ _ _ _ _ _ p' h" for s in ST) + f"""

/-- Where the block map is undefined, the machine halts. -/
theorem none_halts (p : BF) (h : next p = none) : TM.Halts trans p.cfg := by
  obtain ⟨q, l, r⟩ := p
  rw [cfg2]
  cases q <;> simp only [next] at h
""" + "\n".join(f"  · exact next{s}_halts _ _ _ _ _ _ h" for s in ST) + f"""

/-- The block map is undefined exactly at the critical frames. -/
theorem next_none_iff (p : BF) : next p = none ↔ crit p = true := by
  obtain ⟨q, l, r⟩ := p
  cases q <;> simp only [next, crit]
""" + "\n".join(f"  · exact next{s}_none _ _ _ _ _ _" for s in ST) + f"""

/-- Blank tape, state A. -/
def start : BF := ⟨.A, [], []⟩

theorem init_start : steps 0 init = some start.cfg := rfl

/-- **The machine halts from blank tape if and only if the block map, iterated from the blank frame, reaches a
frame where it is undefined.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k p, iterF next k start = some p ∧ next p = none :=
  frames_halts_iff trans BF.cfg next (fun _ => True) (fun p => next p = none)
    (fun p p' _ h => next_sound p p' h) (fun _ _ _ _ => trivial) (fun p _ h => none_halts p h) (fun _ _ h => h)
    init_start trivial

/-- **The machine halts from blank tape if and only if the block map reaches a critical frame.** -/
theorem halts_iff_critical : HaltsFromBlank ↔ ∃ k p, iterF next k start = some p ∧ crit p = true := by
  rw [halts_iff]
  constructor
  · rintro ⟨k, p, h, hn⟩; exact ⟨k, p, h, (next_none_iff p).1 hn⟩
  · rintro ⟨k, p, h, hn⟩; exact ⟨k, p, h, (next_none_iff p).2 hn⟩

theorem frames_{K} : ∀ j, j ≤ {K} → ∃ p, iterF next j start = some p :=
  checkF_sound next {K} start (by native_decide)

/-- No critical frame among the first {K} frames of the run from blank tape. -/
theorem no_halt_frames : ∀ j, j < {K} → ∀ p, iterF next j start = some p → crit p = false := by
  intro j hj p hp
  obtain ⟨g, hg⟩ := frames_{K} (j + 1) (by omega)
  rw [iterF_succ next j start p hp] at hg
  cases hc : crit p with
  | false => rfl
  | true => rw [(next_none_iff p).2 hc] at hg; cases hg

end {ns}
""")
    d = os.path.join(HERE, "..", "lean")
    open(os.path.join(d, "BPieces.lean"), "w").write(pieces)
    open(os.path.join(d, "Blocks.lean"), "w").write("\n".join(o))
    print("wrote", len(mp.leaves), "cases,", len(crit), "critical")


def export(mp):
    tr = lambda x: f"{x.k} {x.c.get('a', 0)} {x.c.get('b', 0)}"
    it = lambda x: ("1 " + tr(x.n) + " 0 0 0") if isinstance(x, Zeros) else ("0 0 0 0 " + tr(x))
    kind = {"eq": 0, "ge": 1, "tr": 2}
    for lf in mp.leaves:
        print(lf.q, kind[lf.rl[0]], lf.rl[1], kind[lf.rr[0]], lf.rr[1], int(lf.halt), lf.q2, len(lf.lb), len(lf.rb),
              " ".join(it(x) for x in lf.lb + [lf.lc]), " ".join(it(x) for x in lf.rb + [lf.rc]), tr(lf.steps))


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ("table", "check", "run", "lean", "export"):
        sys.exit(__doc__)
    mp = Map()
    cmd = sys.argv[1]
    if cmd == "table":
        for lf in mp.leaves:
            print(f"{lf.start:34s} ->  " + ("HALT" if lf.halt else f"{lf.end}   [{lf.steps} steps]"))
    elif cmd == "check":
        check(mp, int(sys.argv[2]))
    elif cmd == "lean":
        lean(mp)
    elif cmd == "export":
        export(mp)
    else:
        f = (0, (), ()); t = 0; mx = 0
        n = int(sys.argv[2])
        for k in range(n):
            g = mp.nxt(f)
            if g is None:
                print("critical frame after", k, "iterations, step", t, ":", f); return
            f = g[0]; t += g[1]; mx = max(mx, len(f[1]) + len(f[2]))
        print(n, "iterations =", t, "machine steps, no critical frame; most blocks on the tape:", mx)


if __name__ == "__main__":
    main()
