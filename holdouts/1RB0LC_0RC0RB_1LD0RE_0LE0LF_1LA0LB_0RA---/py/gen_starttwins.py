"""Write lean/StartTwin.lean for the F05 pairs that have one frame-A table and differ only in the start state.

The start-A machine X and the start-C machine Y run the same frame-A table.  At their fourth left-end event (frame-A
step 284 from A, 1241 from C) both tapes are blank left of the head, and Y's block list is X's with the first block
16 longer: [16] against [32].  So Y's configuration is X's with the word (10)^16 inserted inside the first block.
`TM.halts_iff_of_good` (tools/lean/TM/Insert.lean) follows the run of X and the place of that word.  The word
stays inside the first block, where every pass of the head crosses it in the state it entered (a transparent
crossing) or moves it one cell along the alternating cells (a shift).  The Lean file proves:

* `event_rel`: for every first block b, every rest X of the tape and every place n inside the first block,
  E (b + 16) X is E b X with the word inserted after n cells (the lemma about block lists);
* `good_of_lists` (from `TM.good_of_rounds`, tools/lean/TM/Rounds.lean): if every round of X's run (from one
  left-end event E(l) to the next) keeps the word inside the first block, whatever its place there, the coupling
  never fails;
* `halt_together`: under that condition (`RoundGood` at every left-end event of X's run), X and Y halt from blank
  tape together.

The condition fails exactly when a round uses up X's first block: then Y still has 16 more and the runs part.  It is
checked here on the first rounds for every place, `tools/c/inscheck.c` checks the whole coupling to 10^10 steps, and
`py/start_twins_check.py` compares the block lists at every left-end event to 10^200 steps.

usage: python3 gen_starttwins.py            # writes the files and updates the folders' check.sh
       python3 gen_starttwins.py --check    # only checks the start relation and the first rounds
       python3 gen_starttwins.py --records  # also writes the claims, explainer sections and README blocks
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frames  # noqa: E402
import gen_twins as gt  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
SHARED = "holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---"

# (start-A machine, start-C machine): the block lists agree at every left-end event to 10^200 steps (10^22 for the
# one pair run with hybrid2.py, see REACH)
PAIRS = [
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---", "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---", "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---", "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---", "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---"),
]
# how far the two runs' block lists were compared (start_twins_check.py, or data/f05_run.json for hybrid2 runs)
REACH = {"1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---": "22"}
NX, NY = 284, 1241          # frame-A steps to the fourth left-end event from A and from C
FUEL = 10000


# ------------------------------------------------------------------------------------------------ simulation

def table(fa):
    t = {}
    for i, row in enumerate(fa.split("_")):
        for y in (0, 1):
            g = row[3 * y:3 * y + 3]
            t[("ABCDEF"[i], y)] = None if g[2] == "-" else (int(g[0]), 1 if g[1] == "R" else -1, g[2])
    return t


def fsteps(t, st, n):
    """TM.fsteps on lists: (left list nearest first, right list, state)."""
    l, r = [], []
    for _ in range(n):
        x = t[(st, r[0] if r else 0)]
        assert x is not None, "halts"
        w, d, st = x
        if d == 1:
            l, r = [w] + l, r[1:]
        else:
            l, r = l[1:], [l[0] if l else 0, w] + r[1:]
    return l, r, st


def E(blocks):
    r = [0]
    for b in blocks:
        r += [1, 0] * b + [1]
    return r


def strip(w):
    while w and w[-1] == 0:
        w = w[:-1]
    return w


def ins_at(n):
    return (True, n, [0, 1] * 16 if n % 2 == 0 else [1, 0] * 16)


def zsim(t, fuel, lw, rw, s):
    """TM.zsim: run on the word alone until the head leaves it."""
    lw, rw = list(lw), list(rw)
    while True:
        if not rw:
            return ("right", lw, s)
        if fuel == 0:
            return None
        fuel -= 1
        x = t[(s, rw[0])]
        if x is None:
            return None
        w, d, s = x
        if d == 1:
            lw, rw = [w] + lw, rw[1:]
        else:
            if not lw:
                return ("left", [w] + rw[1:], s)
            lw, rw = lw[1:], [lw[0], w] + rw[1:]


def round_from(t, blocks, ins, cap=10 ** 8):
    """Follow X from E(blocks) with the insertion `ins` (TM.trk with TM.tnext) to the next left-end event:
    ('event', steps, ins, blocks') or ('halt', ...) / ('bad', ...) / ('cap',)."""
    tape = dict(enumerate(E(blocks)))
    p, s, lo = 0, "A", 0
    for n in range(cap):
        a = tape.get(p, 0)
        x = t[(s, a)]
        if x is None:
            return ("halt", n, ins)
        w, d, s2 = x
        right, k, v = ins
        if right:
            if d == -1:
                ni = (True, k + 1, v)
            elif k >= 2:
                ni = (True, k - 1, v)
            else:
                z = zsim(t, FUEL, [], v, s2)
                if z and z[0] == "right" and z[2] == s2:
                    ni = (False, 0, z[1])
                elif v and v[0] == tape.get(p + 1, 0):
                    ni = (True, 1, v[1:] + v[:1])
                else:
                    return ("bad", n, ins)
        else:
            if d == 1:
                ni = (False, k + 1, v)
            elif k >= 1:
                ni = (False, k - 1, v)
            elif not v:
                ni = (True, 1, [])
            else:
                z = zsim(t, FUEL, v[1:], [v[0]], s2)
                if z and z[0] == "left" and z[2] == s2:
                    ni = (True, 1, z[1])
                elif v[0] == tape.get(p - 1, 0):
                    ni = (False, 0, v[1:] + v[:1])
                else:
                    return ("bad", n, ins)
        tape[p] = w
        p += d
        s, ins = s2, ni
        if p < lo:
            lo = p
            if s == "A":
                hi = max(tape)
                r = [tape.get(i, 0) for i in range(p, hi + 2)]
                return ("event", n + 1, ins, alt_len(r), parse_blocks(r))
    return ("cap",)


def parse_blocks(r):
    if r[0] != 0:
        return None
    q, out = 1, []
    while True:
        c = 0
        while r[q:q + 3] == [1, 0, 1]:
            c += 1
            q += 2
        if r[q] != 1:
            return None
        out.append(c)
        q += 1
        if not any(r[q:]):
            return out


def alt_len(r):
    """the number of alternating cells 0 1 0 1 ... at the start of r"""
    m = 0
    while m < len(r) and r[m] == m % 2:
        m += 1
    return m


def in_run(ins, m):
    return ins[0] and 1 <= ins[1] <= m and ins == ins_at(ins[1])


def check_pair(x, y, rounds=3):
    fx, fax, sx = frames.info(x)
    fy, fay, sy = frames.info(y)
    assert fax == fay and sx == "A" and sy == "C", (x, y)
    t = table(fax)
    cx, cy = fsteps(t, "A", NX), fsteps(t, "C", NY)
    assert cx[2] == cy[2] == "A" and not any(cx[0]) and not any(cy[0])
    assert strip(cx[1]) == strip(E([16])) and strip(cy[1]) == strip(E([32])), "start relation"
    out, l = [], [16]
    for _ in range(rounds):
        res = [round_from(t, l, ins_at(n)) for n in range(1, 2 * l[0] + 3)]
        ok = all(z[0] == "event" and in_run(z[2], z[3]) for z in res)
        out.append((l, ok, res[0][1] if res[0][0] == "event" else None))
        if not ok:
            break
        l = res[0][4]
        if l is None:
            break
    return dict(fa=fax, start=(cx, cy), rounds=out)


# ------------------------------------------------------------------------------------------------ Lean

def lb(x):
    return "true" if x else "false"


def ll(w):
    return "[" + ", ".join(lb(b) for b in w) + "]"


def file_text(x, y):
    info = check_pair(x, y, rounds=1)
    cx, cy = info["start"]
    return f"""import TM.Fin
import TM.Rounds

/-!
# {x} and {y}: one table, two starts

Generated by `py/gen_starttwins.py` in the folder of the family's first machine
({SHARED}); do not edit by hand.

Both machines are the F05 core with the same frame-A table `FX` = {info["fa"]}; {x} runs it from state A,
{y} from state C.  A *left-end event* `E m X` is the head in state A at the left end of the tape, nothing written on
its left, and to its right `m` alternating cells `0 1 0 1 ...` and then any tape `X`.  With the block list
`[b1, ..., bk]` the tape is `0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1`, whose alternating run has `m = 2 b1 + 2` cells.
The two runs reach the list [16] (`E 34 blank`, after {NX} steps from A) and the list [32] (`E 66 blank`, after {NY}
steps from C): the second is the first with 32 alternating cells, the word `(10)^16`, inserted inside the first block
(`event_rel`, a statement for every run length, every place in the run and every tape after it).

`TM.halts_iff_of_good` (tools/lean/TM/Insert.lean) follows the run of the start-A machine together with the place of
that word.  At the left end each round crosses the word, in the state it entered, when it spreads the first block
and when it folds it back; in between the head works further right.  `RoundGood m X` says that one round from
`E m X` does this with the word anywhere inside the alternating run: the followed run never fails, or it reaches the
next left-end event `E m' X'` with the word inside its alternating run.  `good_of_lists` (with
`TM.good_of_rounds`, tools/lean/TM/Rounds.lean) puts the rounds together.  Proved here:

* **`halt_together`**: if `RoundGood` holds at every left-end event `E m X` of the start-A run,
  {x} and {y} halt from blank tape together.

So the two halting questions are one, given a condition on the block lists of one run.  It fails exactly when a
round uses up the first block of the start-A run (then the start-C run still has 16 more): on 3,000 random block
lists every failure was of that kind, and in the real runs the first block stays at 6 or more (the block lists of
the two runs agree at every left-end event to 10^{REACH.get(x, '200')} steps).  Kernel only (axioms `propext`, `Classical.choice`,
`Quot.sound`; no `native_decide`).
-/

namespace StartTwin

open TM

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr
{gt.machine_block("MX", x)}{gt.machine_block("MY", y)}
/-! ## One table -/

abbrev FX := MX.FA.trans

theorem FY_eq : MY.FA.trans = FX := by
  funext q b; cases q <;> cases b <;> rfl

/-! ## Left-end events -/

/-- `m` alternating cells `b, !b, b, ...` in front of `X`. -/
def alt (b : Bool) : Nat → Tape → Tape
  | 0, X => X
  | m + 1, X => cons b (alt (!b) m X)

/-- The same cells as a list. -/
def altL (b : Bool) : Nat → List Bool
  | 0 => []
  | m + 1 => b :: altL (!b) m

/-- The parity of `m`, as the value of cell `m` of an alternating run that starts with 0. -/
def par : Nat → Bool
  | 0 => false
  | m + 1 => !par m

theorem app_altL : ∀ (b : Bool) (m : Nat) (X : Tape), app (altL b m) X = alt b m X
  | _, 0, _ => rfl
  | b, m + 1, X => by show cons b (app (altL (!b) m) X) = cons b (alt (!b) m X); rw [app_altL]

theorem length_altL : ∀ (b : Bool) (m : Nat), (altL b m).length = m
  | _, 0 => rfl
  | b, m + 1 => by show (altL (!b) m).length + 1 = m + 1; rw [length_altL]

theorem alt_add : ∀ (b : Bool) (p q : Nat) (X : Tape), alt b (p + q) X = alt b p (alt (xor b (par p)) q X)
  | b, 0, q, X => by simp [alt, par]
  | b, p + 1, q, X => by
    rw [Nat.add_right_comm]
    show cons b (alt (!b) (p + q) X) = cons b (alt (!b) p (alt (xor b (!par p)) q X))
    rw [alt_add (!b) p q X]
    cases b <;> cases par p <;> rfl

/-- A left-end event: state A on the left end of the tape, nothing written on the left, and to the right `m`
alternating cells `0 1 0 1 ...` and then any tape `X`.  At a left-end event with the block list
`[b1, ..., bk]`, the tape `0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1` starts with `2 b1 + 2` alternating cells. -/
def E (m : Nat) (X : Tape) : Cfg St := ⟨blank, alt false m X, .A⟩

/-- The inserted word, in the phase that fits after `n` cells of the alternating run. -/
def insAt (n : Nat) : Ins := ⟨true, n, altL (par n) 32⟩

/-- **The lemma about block lists.**  For every length `m` of the alternating run at the left end (twice the first
block plus 2), every rest of the tape `X` and every place `n` inside the run, `E (m + 32) X` (the first block 16
longer) is `E m X` with 32 alternating cells, `(10)^16` in the phase that fits, inserted after `n` cells. -/
theorem event_rel (m : Nat) (X : Tape) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ m) :
    Rel (insAt n) (E m X) (E (m + 32) X) := by
  have hm : m = n + (m - n) := by omega
  have hm' : m + 32 = n + (32 + (m - n)) := by omega
  refine relR rfl rfl h1 (altL false n) (alt (par n) (m - n) X) (length_altL _ _) ?_ ?_
  · show alt false m X = _
    rw [app_altL, hm, alt_add]; simp
  · show alt false (m + 32) X = _
    rw [app_altL, app_altL, hm', alt_add, alt_add]
    have : par 32 = false := rfl
    simp [this]

/-! ## The condition, round by round -/

/-- The insertion is inside an alternating run of `m` cells at the left end. -/
def InRun (t : Ins) (m : Nat) : Prop := ∃ n, 1 ≤ n ∧ n ≤ m ∧ t = insAt n

/-- One round from `E m X`, with the word anywhere inside the alternating run, never fails or reaches the next
left-end event `E m' X'` with the word inside its alternating run again. -/
def RoundGood (m : Nat) (X : Tape) : Prop :=
  ∀ n, 1 ≤ n → n ≤ m →
    Good FX {FUEL} (insAt n) (E m X) ∨
      ∃ k t' m' X', 1 ≤ k ∧ trk FX {FUEL} k (insAt n) (E m X) = some (t', E m' X') ∧ InRun t' m'

/-- A configuration of the start-A run from its fourth left-end event (the block list [16]). -/
def Reach (c : Cfg St) : Prop := ∃ k, steps FX k (E 34 blank) = some c

/-- **The rounds put together.** -/
theorem good_of_lists (H : ∀ m X, Reach (E m X) → RoundGood m X) : Good FX {FUEL} (insAt 1) (E 34 blank) := by
  refine good_of_rounds FX (fun t c => Reach c ∧ ∃ m X, c = E m X ∧ InRun t m) ?_ _ _
    ⟨⟨0, rfl⟩, 34, blank, rfl, 1, Nat.le_refl 1, by decide, rfl⟩
  rintro t c ⟨hr, m, X, rfl, n, h1, h2, rfl⟩
  rcases H m X hr n h1 h2 with hg | ⟨k, t', m', X', hk, ht, hb⟩
  · exact Or.inl hg
  · refine Or.inr ⟨k, t', E m' X', hk, ht, ?_, m', X', rfl, hb⟩
    obtain ⟨k', -, hk'⟩ := trk_steps FX k ht
    obtain ⟨j, hj⟩ := hr
    exact ⟨j + k', steps_seq FX hj hk'⟩

/-! ## The two runs meet the block lists [16] and [32] -/

/-- The start-A run after {NX} steps. -/
def cX : FCfg St := ⟨{ll(cx[0])}, {ll(cx[1])}, .A⟩

/-- The start-C run after {NY} steps. -/
def cY : FCfg St := ⟨{ll(cy[0])}, {ll(cy[1])}, .A⟩

set_option maxRecDepth 100000 in
theorem at_X : TM.fsteps FX {NX} (FCfg.blank .A) = some cX := by decide

set_option maxRecDepth 100000 in
theorem at_Y : TM.fsteps FX {NY} (FCfg.blank .C) = some cY := by decide

theorem cX_eq : cX.toCfg = E 34 blank := by
  show (⟨app {ll(cx[0])} blank, app {ll(cx[1])} blank, .A⟩ : Cfg St) = ⟨blank, _, .A⟩
  rw [app_blank_eq {ll(cx[1])} {ll(E([16]))} (by decide)]
  rfl

theorem cY_eq : cY.toCfg = E 66 blank := by
  show (⟨app {ll(cy[0])} blank, app {ll(cy[1])} blank, .A⟩ : Cfg St) = ⟨blank, _, .A⟩
  rw [app_blank_eq {ll(cy[1])} {ll(E([32]))} (by decide)]
  rfl

/-- **One question for two machines**, given the condition on the block lists of the start-A run. -/
theorem halt_together (H : ∀ m X, Reach (E m X) → RoundGood m X) : MX.HaltsFromBlank ↔ MY.HaltsFromBlank := by
  rw [MX.halts_iff, MY.halts_iff, FY_eq]
  have hX := halts_iff_of_steps' FX (blank_reaches FX at_X)
  have hY := halts_iff_of_steps' FX (blank_reaches FX at_Y)
  rw [cX_eq] at hX
  rw [cY_eq] at hY
  exact hX.trans ((halts_iff_of_good FX (event_rel 34 blank 1 (by decide) (by decide)) (good_of_lists H)).trans hY.symm)

end StartTwin
"""


# ------------------------------------------------------------------------------------------------ records

def event_table_html(x, y):
    """The first rounds of the two runs side by side, from the frame-A simulation."""
    fa = frames.info(x)[1]
    t = table(fa)

    def events(st, k):
        tape, p, s, lo, n, out = {}, 0, st, 0, 0, []
        while len(out) < k:
            w, d, s = t[(s, tape.get(p, 0))]
            tape[p] = w
            p += d
            n += 1
            if p < lo:
                lo = p
                if s == "A":
                    hi = max(tape)
                    out.append((n, parse_blocks([tape.get(i, 0) for i in range(p, hi + 2)])))
        return out
    ex, ey = events("A", 9), events("C", 9)

    def show(lst):
        return f"<code>{lst}</code>" if lst else "(not only plain blocks)"
    rows = []
    for i, ((nx, lx), (ny, ly)) in enumerate(zip(ex, ey)):
        rel = i >= 3 and lx and ly and lx[1:] == ly[1:] and ly[0] - lx[0] == 16
        rows.append(f"<tr><td>{i + 1}</td><td>{nx:,}</td><td>{show(lx)}</td><td>{ny:,}</td>"
                    f"<td>{show(ly)}</td><td>{'+16, rest equal' if rel else ''}</td></tr>")
    return ("<div style='overflow-x:auto'><table><thead><tr><th>left-end event</th><th>step (from A)</th><th>block list</th><th>step (from C)</th>"
            "<th>block list</th><th>first block</th></tr></thead><tbody>" + "".join(rows) + "</tbody></table></div>")


def records(x, y):
    import json
    e = REACH.get(x, "200")
    lean = f"holdouts/{x}/lean/StartTwin.lean"
    for m, other in ((x, y), (y, x)):
        claim = {
            "level": "kernel", "tag": "F05-start-twin",
            "title": "One question with its start twin " + other,
            "text": (f"<code>{x}</code> and <code>{y}</code> are one frame-A table started in A and in C. At their fourth "
                     f"left-end event (step {NX} from A, {NY} from C) the block lists are [16] and [32]: the second tape "
                     f"is the first with the word (10)<sup>16</sup> inserted in the first block. <code>event_rel</code> "
                     f"proves that relation for every first block, every place in it and every tape after it. "
                     f"<code>halt_together</code>: if every round of the start-A run (from one left-end event to the "
                     f"next) keeps the word inside the first block, wherever it sits there (<code>RoundGood</code>, a "
                     f"condition on one run's left-end events), the two machines halt together. The condition fails only "
                     f"if a round uses up the start-A run's first block; the two runs' block lists agree at every "
                     f"left-end event to 10<sup>{e}</sup> steps, and the coupling holds cell by cell for 10<sup>10</sup> steps."),
            "where": f"<code>halt_together</code>, <code>event_rel</code>, <code>good_of_lists</code>, <code>{lean}</code>; "
                     f"<code>TM.good_of_rounds</code>, <code>tools/lean/TM/Rounds.lean</code>; "
                     f"<code>TM.halts_iff_of_good</code>, <code>tools/lean/TM/Insert.lean</code>; "
                     f"<code>{SHARED}/py/gen_starttwins.py</code>"}
        sec = {"id": "f05-start-twin", "eyebrow": "A start twin", "heading": "One table, two starts",
               "html": [
                   f"<p><code>{x}</code> and <code>{y}</code> are the same machine in frame A, started in two different "
                   f"states (A and C). Their first few rounds differ. From the fourth return to the left end on, the "
                   f"two block lists agree except that the start-C run's first block is 16 longer:</p>",
                   event_table_html(x, y),
                   "<p>At a left-end event nothing is written to the left of the head, so the start-C tape is just the "
                   "start-A tape with 32 more alternating cells, the word (10)<sup>16</sup>, inside the first block. "
                   "Each round crosses that word twice, both times without changing state: once when the first block is "
                   "spread out, and once when it is folded back. In between, the head works further right and does "
                   "not reach the word. So the word just rides along, and the start-C run costs exactly 80 more steps "
                   "per round.</p>",
                   f"<p>In Lean (<code>{lean}</code>): <code>event_rel</code> proves the relation for every first block, "
                   f"every place in it and every tape after it. <code>halt_together</code> says the two machines halt "
                   f"together if every round of the start-A run keeps the word inside the first block "
                   f"(<code>RoundGood</code>, checked round by round with <code>TM.good_of_rounds</code>). That fails "
                   f"only if a round uses up the start-A run's first block. In the runs the lists agree for 10<sup>{e}</sup> "
                   f"steps, and on random block lists every failure was of exactly that kind.</p>"]}
        sp = os.path.join(ROOT, m, "status.json")
        spec = json.load(open(sp))
        cl = [c for c in spec["claims"] if c.get("tag") != "F05-start-twin"]
        k = max([n + 1 for n, c in enumerate(cl) if c.get("tag") in ("F05", "F05-twin")] or [min(3, len(cl))])
        spec["claims"] = cl[:k] + [claim] + cl[k:]
        ss = [q for q in spec["explainer"]["sections"] if q.get("id") != "f05-start-twin"]
        k = max([n + 1 for n, q in enumerate(ss) if q.get("id") in ("f05", "f05-twin")] or [0])
        spec["explainer"]["sections"] = ss[:k] + [sec] + ss[k:]
        note = (f"<b>Start twin.</b> Proved in Lean to share one question with <code>{other}</code> (the same table "
                f"from another start), under a condition on the block lists of one run.")
        spec["verdict"] = [v for v in spec.get("verdict", []) if not v.startswith("<b>Start twin.</b>")] + [note]
        line = f"python3 {SHARED}/py/gen_starttwins.py --check    # the start relation and the first rounds"
        spec["check"] = [c for c in spec.get("check", []) if "gen_starttwins.py" not in c] + [line]
        with open(sp, "w") as f:
            json.dump(spec, f, indent=1, ensure_ascii=False)
            f.write("\n")
        block = "\n".join([
            "<!-- F05 start twin -->", "", "## Start twin: one question with " + other, "",
            f"[`{x}`](../{x}/README.md) and [`{y}`](../{y}/README.md) are one frame-A table started in A and in C. "
            f"From the fourth left-end event on (step {NX} from A, {NY} from C), the start-C run's block list is the "
            f"start-A run's with the first block 16 longer, so its tape is the other with the word `(10)^16` inserted "
            f"in the first block. Each round crosses the word twice in the state it entered (spreading the first block "
            f"and folding it back), so the start-C run is exactly 80 steps slower per round. "
            f"`halt_together` in [`lean/StartTwin.lean`](../{x}/lean/StartTwin.lean) (kernel; `event_rel` is the lemma "
            f"about block lists, `TM.good_of_rounds` in `tools/lean/TM/Rounds.lean` joins the rounds): if every round "
            f"of the start-A run keeps the word inside the first block (`RoundGood`), the two machines halt together. "
            f"That fails only if a round uses up the first block; the two runs' block lists agree at every left-end "
            f"event to 10^{e} steps. See also [EQUIVALENCES.md](../EQUIVALENCES.md).", "",
            "<!-- end F05 start twin -->"])
        q = os.path.join(ROOT, m, "README.md")
        text = open(q).read()
        a_, b_ = "<!-- F05 start twin -->", "<!-- end F05 start twin -->"
        if a_ in text:
            text = text[:text.index(a_)] + block + text[text.index(b_) + len(b_):]
        else:
            anchor = next((z for z in ("<!-- end F05 twin -->", "<!-- end F05 -->") if z in text), None)
            if anchor:
                e = text.index(anchor) + len(anchor)
                text = text[:e] + "\n\n" + block + text[e:]
            else:
                text = text.rstrip("\n") + "\n\n" + block + "\n"
        with open(q, "w") as f:
            f.write(text)


def write_check(x):
    p = os.path.join(ROOT, x, "lean", "check.sh")
    s = open(p).read()
    if "StartTwin.lean" not in s:
        s = s.rstrip("\n") + " StartTwin.lean\n"
        open(p, "w").write(s)


if __name__ == "__main__":
    for x, y in PAIRS:
        info = check_pair(x, y)
        print(x, y, [(l[:3], ok, n) for l, ok, n in info["rounds"]], flush=True)
        if "--check" not in sys.argv:
            with open(os.path.join(ROOT, x, "lean", "StartTwin.lean"), "w") as f:
                f.write(file_text(x, y))
            write_check(x)
        if "--records" in sys.argv:
            records(x, y)
