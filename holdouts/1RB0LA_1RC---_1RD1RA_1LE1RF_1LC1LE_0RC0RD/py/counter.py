"""The clock of 1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD: a binary counter in the block, one excursion into the word
per count.  Everything is done on the mirror image M' = 1LB0RA_1LC---_1LD1LA_1RE1LF_1RC1RE_0LC0LD (the clock is at
the right end of the machine, at the left end of M').

On M' at every visit of the left end in state F the tape is `F>0 1^(5+4j) 0 W`, one step after `D> J j W` with
J j W = `1^(5+4j) 0 W`.  The tick `0^4 D> J j W` -> `D> J (j+1) W'` (4 cells to the left) is:

  sweep  `0^4 D> 1^(5+4j) 0`            -> `0 1 1 0 0 0 (0000)^j 1 1 1 1 E>`     4j + 20 steps   (rule_sweep)
  then 2^j rounds of: an excursion `1 E> W` -> `F> 1 W'` (the P-step: the head stays in the word), and, between
  two excursions, the increment of a binary counter whose digits are `1000` (one) and `0000` (zero), least
  significant digit next to the word:
         `0000 (1000)^n 1 1 1 F> 1`      -> `1000 (0000)^n 1 1 1 1 E>`           18n + 33 steps  (rule_inc)
  finish `0 1 1 0 0 0 (1000)^j 1 1 1 F> 1` -> `D> 1^(9+4j) 0`                   14j + 27 steps  (rule_fin)

So W' = P^(2^j)(W), P = one excursion, and the tick takes E + 51·2^j − 4 steps (E the cost of the excursions):
the statement of the clock theorem of the other clock machines (holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE),
with a different proof (the counter `cnt`, by induction on j).

usage (from the repository root):
  python3 holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/py/counter.py lean          write the Lean files
  python3 holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/py/counter.py tmcheck 1e10  compare with tmrun
  python3 holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/py/counter.py run 1000      phases to 10^1000 steps
  python3 holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/py/counter.py instance T0 N  lean/MirrorInstance.lean
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
CLK = os.path.join(ROOT, "holdouts", "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE", "py")
sys.path.insert(0, os.path.join(ROOT, "tools", "py"))
sys.path.insert(0, CLK)
import clock  # noqa: E402

M = "1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD"
MM = clock.mirror(M)
NS = "H44966"
B0, G, C = 5, 4, 51
BASE = 47                     # the steps of the tick at j = 0 other than its excursion (20 + 27)

# registered here (not in clock.py: gen_clock.py does not apply to this machine)
clock.PARAMS[M] = ("F", "D", B0, G, 1)
clock.MIRROR.add(M)

RULES = [
    ("rule_sweep", "L 0 0 0 0 D> 1 1 1 1 1 (1111)^n 0 R", "L 0 1 1 0 0 0 (0000)^n 1 1 1 1 E> R",
     "The sweep: `0^4 D> 1^(5+4n) 0` becomes the counter at zero, `0 1 1 0 0 0 (0000)^n 1 1 1 1 E>`."),
    ("rule_inc", "L 0 0 0 0 (1000)^n 1 1 1 F> 1 R", "L 1 0 0 0 (0000)^n 1 1 1 1 E> R",
     "The increment: back from an excursion, the head adds one to the counter (n trailing ones) and enters the "
     "word again."),
    ("rule_fin", "L 0 1 1 0 0 0 (1000)^n 1 1 1 F> 1 R", "L D> 1 1 1 1 1 1 1 1 1 (1111)^n 0 R",
     "The finish: back from the last excursion with the counter full, the head fills the block: "
     "`D> 1^(9+4n) 0`."),
]

_Clock = clock.Clock


class CounterClock(_Clock):
    """clock.Clock with the P-step of this machine: one excursion `1 E> W` -> `F> 1 W'` (cost reported as the tick
    at j = 0, the excursion plus BASE)."""

    def structure(self, A, s, Bp, ML):
        return "ABCDEF".index("E"), BASE

    def P(self, W):
        Gp = 8
        off = Gp + 1
        tp = bytearray(Gp) + bytearray([1]) + bytearray(W) + bytearray(64)
        pos, st, t = off, self.Z, self.base
        Wt, Dm, St, Ht = self.W, self.Dm, self.S, self.H
        hi = pos
        self.pcalls += 1
        F = "ABCDEF".index("F")
        while True:
            i = 2 * st + tp[pos]
            if Ht[i]:
                return ("abn", max(0, hi - off + 1))
            tp[pos] = Wt[i]
            pos += Dm[i]
            st = St[i]
            t += 1
            if pos > hi:
                hi = pos
                if hi >= len(tp) - 2:
                    tp += bytearray(len(tp))
            if pos < off:
                r = max(0, hi - off + 1)
                if st != F or tp[off - 1] != 1:
                    return ("abn", r)
                return (bytes(tp[off:off + r]), r, t)


clock.Clock = CounterClock    # the Hybrid and tmcheck of clock.py now use this P


class CounterHybrid(clock.Hybrid):
    """clock.Hybrid, but the tick at the left end of the tape is also done at once: here a tick contains no smaller
    ticks (its trips are separated by counter increments), so accelerating only inner ticks would gain nothing.  The
    visit one step after `D> J` (F on the 0 left of the block) is reported before the tick is done."""

    def visits(self, limit):
        c = self.c
        while self.t < limit:
            if (self.pos == self.lo and self.st == c.Y and self.tp[self.pos] == 1
                    and not any(self.tp[self.pos - 4:self.pos])):
                L = 0
                while self.tp[self.pos + L] == 1:
                    L += 1
                if L >= c.B0 and (L - c.B0) % c.g == 0:
                    W = bytes(self.tp[self.pos + L + 1:self.hi + 1]).rstrip(b"\0")
                    t0 = self.t
                    if self.try_macro():
                        self.lo = min(self.lo, self.pos)
                        yield t0 + 1, L, W        # F>0 1^L 0 W, one step after the tick started
                        continue
            if self.st == c.X and self.pos == self.lo and self.tp[self.pos] == 0:
                L, W = self.tape()
                yield self.t, L, W
            if self.pos - 1 > self.lo and self.try_macro():
                continue
            if not self.step():
                yield "HALT", self.t, None
                return


clock.Hybrid = CounterHybrid


def prove_rules():
    from bbtools.symtm import prove
    return [prove(MM, n, a, b, doc=d, rotate=True)[0] for n, a, b, d in RULES]


CLOCK = r'''import MirrorRules

/-!
# The clock of @MM@, the mirror image of @M@

Written by `holdouts/@M@/py/counter.py lean`.

`J j W` is the tape `1^(5+4j) 0 W` right of the head, the head in state D on its first cell.  At every visit of the
left end in state F the tape is `F>0 1^(5+4j) 0 W`, one step after `D> J j W` one cell to the right.

A *P-step* `PStep W W' e` is one excursion of the head into the word: `L 1 E> W` reaches `L F> 1 W'` in `e` steps,
for every left tape `L` (the head stays in the word until it comes back).  `PChain m W W' E`: `m` P-steps in a row.

The block is a binary counter: digits `1000` (one) and `0000` (zero), least significant next to the word.
`cnt j`: from `Lc (0000)^j 1 1 1 1 E> W` the head makes 2^j excursions, adding one to the counter between two, and
comes back from the last one with the counter full, `Lc (1000)^j 1 1 1 F> 1 W'`, in `E + IC j` steps (induction on
`j`: the low `j` digits count through twice, with one increment `rule_inc` of the digit above in between).

**Theorem `tick`.**  For every `j`, if `W` reaches `W'` by `2^j` P-steps of total cost `E`, then

    L 0 0 0 0 D> 1^(5+4j) 0 W   reaches   L D> 1^(9+4j) 0 W'   in exactly  E + 51·2^j − 4  steps,

for every `L`: the sweep (`rule_sweep`), the counter (`cnt`), the finish (`rule_fin`).  So the block grows by 4
per tick while the word goes through `2^j` applications of one map P.
-/

namespace @NS@

open TM

/-- `1^(5+4j) 0 W`, read from the head. -/
def J (j : Nat) (W : Tape) : Tape :=
  cons true (cons true (cons true (cons true (cons true (rep j [true, true, true, true] (cons false W))))))

/-- One excursion into the word: `L 1 E> W` reaches `L F> 1 W'` in `e` steps, for every `L`. -/
def PStep (W W' : Tape) (e : Nat) : Prop :=
  ∀ L : Tape, steps e ⟨cons true L, W, .E⟩ = some ⟨L, cons true W', .F⟩

/-- `m` P-steps in a row, of total cost `E`. -/
inductive PChain : Nat → Tape → Tape → Nat → Prop
  | zero (W : Tape) : PChain 0 W W 0
  | succ {m : Nat} {W W1 W2 : Tape} {e E : Nat} : PStep W W1 e → PChain m W1 W2 E → PChain (m + 1) W W2 (e + E)

theorem PChain.split : ∀ (x y : Nat) {W W2 : Tape} {E : Nat}, PChain (x + y) W W2 E →
    ∃ W1 E1 E2, PChain x W W1 E1 ∧ PChain y W1 W2 E2 ∧ E = E1 + E2 := by
  intro x
  induction x with
  | zero => intro y W W2 E h; exact ⟨W, 0, E, .zero W, by simpa using h, by omega⟩
  | succ x ih =>
    intro y W W2 E h
    rw [show x + 1 + y = (x + y) + 1 by omega] at h
    cases h with
    | succ hs hc =>
      obtain ⟨W1, E1, E2, h1, h2, he⟩ := ih y hc
      exact ⟨W1, _ + E1, E2, .succ hs h1, h2, by omega⟩

/-- The steps of the increments of a count through `j` digits. -/
def IC : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * IC j + (18 * j + 33)

theorem IC_eq (j : Nat) : IC j + 18 * j + 51 = 51 * 2 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [IC]
    rw [Nat.pow_succ]
    omega

theorem z4_cons (n : Nat) (X : Tape) :
    rep n [false, false, false, false] (cons false X) = cons false (rep n [false, false, false, false] X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

theorem o4_cons (n : Nat) (X : Tape) :
    rep n [true, true, true, true] (cons true X) = cons true (rep n [true, true, true, true] X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

/-- The statement of the counter through `j` digits. -/
def Cnt (j : Nat) : Prop :=
  ∀ (W W' : Tape) (E : Nat), PChain (2 ^ j) W W' E → ∀ Lc : Tape,
    steps (E + IC j) ⟨cons true (cons true (cons true (cons true (rep j [false, false, false, false] Lc)))), W, .E⟩ =
      some ⟨cons true (cons true (cons true (rep j [false, false, false, true] Lc))), cons true W', .F⟩

/-- **The counter**: 2^j excursions, with the increments in between, for every left context `Lc`. -/
theorem cnt (j : Nat) : Cnt j := by
  induction j with
  | zero =>
    intro W W' E h Lc
    cases h with
    | succ hs hz =>
      cases hz
      exact hs (cons true (cons true (cons true Lc)))
  | succ j ih =>
    intro W W' E h Lc
    rw [show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by rw [Nat.pow_succ]; omega] at h
    obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
    -- the low j digits count through, below a 0 digit
    have s1 := ih W W1 E1 h1 (cons false (cons false (cons false (cons false Lc))))
    -- the increment that sets the digit j
    have s2 := rule_inc j Lc W1
    rw [← z4_cons] at s2
    -- the low j digits count through again, below a 1 digit
    have s3 := ih W1 W' E2 h2 (cons false (cons false (cons false (cons true Lc))))
    have := steps_seq trans s1 (steps_seq trans s2 s3)
    have e1 : rep j [false, false, false, false] (cons false (cons false (cons false (cons false Lc)))) =
        rep (j + 1) [false, false, false, false] Lc := rep_app_comm j _ Lc
    have e2 : rep j [false, false, false, true] (cons false (cons false (cons false (cons true Lc)))) =
        rep (j + 1) [false, false, false, true] Lc := rep_app_comm j _ Lc
    rw [e1, e2] at this
    refine steps_congr trans ?_ this
    simp only [IC]
    omega

/-- The statement of tick `j`. -/
def Tick (j : Nat) : Prop :=
  ∀ (W W' : Tape) (E : Nat), PChain (2 ^ j) W W' E → ∀ L : Tape,
    steps (E + 51 * 2 ^ j - 4) ⟨cons false (cons false (cons false (cons false L))), J j W, .D⟩ =
      some ⟨L, J (j + 1) W', .D⟩

/-- **The tick**, for every level `j`: `L 0^4 D> 1^(5+4j) 0 W` reaches `L D> 1^(9+4j) 0 W'` in
`E + 51·2^j − 4` steps whenever `2^j` P-steps of total cost `E` take `W` to `W'`. -/
theorem tick (j : Nat) : Tick j := by
  intro W W' E h L
  have s0 := rule_sweep j L W
  have s1 := cnt j W W' E h (cons false (cons false (cons false (cons true (cons true (cons false L))))))
  have s2 := rule_fin j L W'
  rw [o4_cons] at s2
  have e3 : cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true
      (rep j [true, true, true, true] (cons false W')))))))))) = J (j + 1) W' := by
    unfold J; rw [rep_succ]; rfl
  rw [e3] at s2
  have := steps_seq trans s0 (steps_seq trans s1 s2)
  refine steps_congr trans ?_ this
  have q := IC_eq j
  have p5 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  generalize 2 ^ j = q at *
  omega

/-- The tick at the left end of the tape (blank to the left); the visits of the left end in state F are one step
after these configurations. -/
theorem tick_left_end (j : Nat) (W W' : Tape) (E : Nat) (h : PChain (2 ^ j) W W' E) :
    steps (E + 51 * 2 ^ j - 4) ⟨blank, J j W, .D⟩ = some ⟨blank, J (j + 1) W', .D⟩ := by
  have := tick j W W' E h blank
  rwa [cons_false_blank, cons_false_blank, cons_false_blank, cons_false_blank] at this

end @NS@
'''


def write_lean():
    from bbtools.leangen import machine_lean
    from bbtools.symtm import rules_file
    from gen_clock import BRIDGE, lchain
    d = os.path.join(ROOT, "holdouts", M, "lean")
    nsm = NS + "M"
    open(os.path.join(d, "MirrorMachine.lean"), "w").write(machine_lean(
        MM, nsm, doc=f"The mirror image of {M} (L and R swapped), whose clock is at the right end; "
                     "see `MirrorBridge.lean` for the correspondence of the runs."))
    open(os.path.join(d, "MirrorRules.lean"), "w").write(rules_file(
        "MirrorMachine", nsm, prove_rules(), "The three local rules of the tick, written by `bbtools.symtm.prove` "
        f"(from `holdouts/{M}/py/counter.py`)."))
    open(os.path.join(d, "MirrorClock.lean"), "w").write(
        CLOCK.replace("@MM@", MM).replace("@M@", M).replace("@NS@", nsm))
    bt = BRIDGE
    for k, v in [("@MO@", M), ("@NS@", NS), ("@C@", str(C)), ("@G@", str(G)), ("@Y@", "D"),
                 ("@ZGL@", lchain([0] * G, "L"))]:
        bt = bt.replace(k, v)
    open(os.path.join(d, "MirrorBridge.lean"), "w").write(bt)
    ck = os.path.join(d, "check.sh")
    s = open(ck).read()
    if "MirrorClock.lean" not in s:
        s = s.rstrip("\n") + " MirrorMachine.lean MirrorRules.lean MirrorClock.lean MirrorBridge.lean\n"
        open(ck, "w").write(s)


def lb(cells):
    return "[" + ", ".join("true" if c else "false" for c in cells) + "]"


def instance(t0, n):
    """lean/MirrorInstance.lean: the clock on the run (of M') from blank tape, from step t0 through n ticks."""
    sys.path.insert(0, os.path.join(ROOT, "holdouts", "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB", "py"))
    from instance import blank_run
    from bbtools.symtm import prove
    ck = CounterClock(M)
    ck.nested = False
    left, right, st = blank_run(ck.T, t0)
    assert not any(left) and st == ck.Y, (left, st)
    L = 0
    while L < len(right) and right[L] == 1:
        L += 1
    assert L >= B0 and (L - B0) % G == 0 and right[L:L + 1] in ([0], []), right[:L + 2]
    j0 = (L - B0) // G
    W = bytes(right[L + 1:])
    words, costs, reads = [W], [], []
    for i in range(n):
        for _ in range(2 ** (j0 + i)):
            r = ck.P(W)
            assert r[0] != "abn", ("abnormal P-step", i)
            pre_w, rr, cost = r
            W = (pre_w + W[rr:]).rstrip(b"\0")
            words.append(W)
            costs.append(cost - BASE)
            reads.append(rr)
    N = max([len(w) for w in words] + reads)
    pad = [list(w) + [0] * (N - len(w)) for w in words]
    lemmas = []
    for k in range(len(costs)):
        txt, fin = prove(MM, f"pstep{k}", f"L 1 E> {' '.join(map(str, pad[k]))} R",
                         f"L F> 1 {' '.join(map(str, pad[k + 1]))} R", max_seg=100, doc=f"Excursion {k} of the run.")
        assert int(str(fin.steps)) == costs[k], (fin.steps, costs[k])
        lemmas.append(txt)
    nsm = NS + "M"
    defs = [f"def w{k} : List Bool := {lb(pad[k])}" for k in range(len(pad))]
    body = [f"""/-- The run of the mirror image from blank tape reaches `blank, J {j0} W, D` at step {t0} (`decide`). -/
theorem at_start' : steps {t0} init = some ⟨blank, J {j0} (app {lb(right[L + 1:])} blank), .D⟩ :=
  blank_reaches trans (c := ⟨{lb(left)}, {lb(right)}, .D⟩) (by decide +kernel)

theorem at_start : steps {t0} init = some ⟨blank, J {j0} (app w0 blank), .D⟩ := by
  have e : app {lb(right[L + 1:])} blank = app w0 blank := by simp only [w0, app, cons_false_blank]
  rw [← e]; exact at_start'
"""]
    for k in range(len(costs)):
        body.append(f"theorem ps{k} : PStep (app w{k} blank) (app w{k + 1} blank) {costs[k]} := "
                    f"fun L => pstep{k} L blank\n")
    proof = ["  have h0 := at_start"]
    acc, k = t0, 0
    for i in range(n):
        j = j0 + i
        ks = list(range(k, k + 2 ** j))
        ch = "(.zero _)"
        for q in reversed(ks):
            ch = f"(.succ ps{q} {ch})"
        cnt = sum(costs[q] for q in ks) + C * 2 ** j - G
        body.append(f"""/-- Tick {i} of the run: level {j}, {2 ** j} excursions, {cnt} steps (`tick_left_end`). -/
theorem tick{i} : steps {cnt} ⟨blank, J {j} (app w{ks[0]} blank), .D⟩ =
    some ⟨blank, J {j + 1} (app w{ks[-1] + 1} blank), .D⟩ :=
  steps_congr trans (by decide) (tick_left_end {j} _ _ _ {ch})
""")
        proof.append(f"  have h{i + 1} := steps_congr trans (show {acc} + {cnt} = {acc + cnt} by decide) "
                     f"(steps_seq trans h{i} tick{i})")
        acc += cnt
        k += 2 ** j
    proof.append(f"  exact h{n}")
    body.append(f"""/-- **The clock carries the real run**: from step {t0} the run of the mirror image from blank tape goes
through {n} ticks of `tick_left_end` (levels {j0} to {j0 + n - 1}) and is at `blank, J {j0 + n} W, D` at step {acc};
mirrored (`MirrorBridge.of_mirror`), the same holds for the run of the machine. -/
theorem run_ticks : steps {acc} init = some ⟨blank, J {j0 + n} (app w{k} blank), .D⟩ := by
""" + "\n".join(proof) + "\n")
    head = f'''import MirrorClock

/-!
# The clock on the run from blank tape (mirror image)

Written by `holdouts/{M}/py/counter.py instance {t0} {n}`.  The hypothesis of `tick_left_end` (a chain of 2^j
excursions) is met by the words of the actual run: each excursion of the {n} ticks after step {t0} is proved for
every tape to the left (`pstepK`, by `bbtools.symtm.prove`), and `run_ticks` follows the run from blank tape through
those ticks with `tick_left_end`.
-/

set_option maxRecDepth 20000

namespace {nsm}

open TM

'''
    out = head + "\n".join(defs) + "\n\n" + "\n".join(lemmas) + "\n\n" + "\n".join(body) + f"\nend {nsm}\n"
    d = os.path.join(ROOT, "holdouts", M, "lean")
    open(os.path.join(d, "MirrorInstance.lean"), "w").write(out)
    cks = os.path.join(d, "check.sh")
    sh = open(cks).read()
    if "MirrorInstance.lean" not in sh:
        open(cks, "w").write(sh.rstrip("\n") + " MirrorInstance.lean\n")
    print("t0", t0, "j0", j0, "ticks", n, "end step", acc, "excursions", len(costs), "cells", N)


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "lean":
        write_lean()
    elif cmd == "tmcheck":
        print(clock.tmcheck(M, int(float(sys.argv[2]))))
    elif cmd == "run":
        clock.run(M, float(sys.argv[2]))
    elif cmd == "instance":
        instance(int(sys.argv[2]), int(sys.argv[3]))
