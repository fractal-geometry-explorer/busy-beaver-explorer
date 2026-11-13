"""Writes the Lean files of the (0001)-counter for one machine of the family

    1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF         (sample state D, arrival state B)
    1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---         (sample state A, arrival state E)
    1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---         (same)
    1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---         (same)

  Pieces.lean   the nine piece rules, proved by bbtools.symtm (shift rules, rfl, omega), for all parameters
  Counter.lean  the encoding of a sample configuration by digits and gaps, the increment `bump`, and the theorem
                `visit`: one visit of the head is one increment of the base-5 counter (hand-written template)
  Merge.lean    the merge of two adjacent e digits, the one place where the four machines differ
  Reach.lean    the run from blank tape reaches a sample configuration made of standard digits (native_decide)

usage: python3 gen_lean.py            (from this folder; writes ../lean/*.lean)
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
sys.path.insert(0, HERE)
from bbtools.symtm import prove
from fam import FAMILY, pieces, DIG, merge_rule

def lean_word(w):
    return '[' + ', '.join('true' if c == '1' else 'false' for c in w) + ']'

def piece_costs(M, S, R):
    out, costs = [], {}
    for name, a, b, doc in pieces(S, R):
        txt, fin = prove(M, name, a, b, rotate=True, doc=doc)
        out.append(txt)
        costs[name] = txt.split('steps (')[1].split(')')[0]
    return out, costs

def coef(expr, var):
    """'6 * n + 5' -> (6, 5);  '32' -> (0, 32)"""
    a, c = 0, 0
    for t in expr.replace(' ', '').split('+'):
        if '*' in t:
            a = int(t.split('*')[0])
        elif t:
            c = int(t)
    return a, c

def counter_file(M, ns, S, R, costs):
    sa, sc = coef(costs['start'], 'n')
    ca, cc = coef(costs['carry'], 'm')
    la, _ = coef(costs['left_gap'], 'k')
    bo = int(costs['bounce_a'])
    for x in 'bce':
        assert int(costs['bounce_' + x]) == bo
    ld = int(costs['left_d'])
    le = int(costs['left_end'])
    D = ca + la          # per W of a passed gap
    K = cc + ld          # per passed d
    G = sa + la          # per W of the left gap
    V = sc + le          # per visit
    return f'''import Machine
import Pieces

/-!
# The counter: one visit is one increment

At a *sample configuration* the head, in state {S}, reads the leftmost cell of the tape, and the tape is

    0 0 W^g₀ X₁ W^g₁ X₂ W^g₂ … Xₖ W^gₖ T          W = 0 0 0 1

(`sample g₀ [(X₁, g₁), …, (Xₖ, gₖ)] T`): a *left gap* of `g₀` copies of `W`, then *digits* `Xᵢ`, each followed by a gap
of `gᵢ` copies of `W`, then an arbitrary rest `T`.  The digits are the five words

    a = 0011   b = 0011001   c = 001101   d = 00111   e = 00101

with values a = 1, b = 2, c = 3, d = 4, e = 0, the first digit the least significant.  One *visit* (the head goes right
and comes back to the left end, in state {S} again) adds one to this base-5 number: every leading `d` (value 4) becomes
`e` (value 0, a carry), the first other digit `X` takes the increment, and the head turns there.  `bump` is that map on
the numbers; it also moves the gaps:

* `a → b` and `e → a` take one `W` from the gap after the digit;
* `e → a` gives one `W` to the gap before it (the left gap when the digit is the first);
* every visit adds one `W` to the left gap (the tape grows by three cells on the left).

`bump` is undefined when the carry runs into `T` or the digit that takes the increment has an empty gap after it
(`gᵢ = 0`): those are the *collisions*, which this file does not cover.  `visit` is proved for every list of digits,
every gap and every rest of the tape by Lean's kernel, from the nine piece rules of `Pieces.lean`; the step count is
exact.
-/

namespace {ns}

open TM

/-- The background word `0 0 0 1`. -/
abbrev W : List Bool := [false, false, false, true]

/-- The five digits. -/
inductive Dg where
  | a | b | c | d | e
  deriving DecidableEq, Repr

/-- The cells of a digit. -/
def Dg.word : Dg → List Bool
  | .a => {lean_word(DIG['a'])}
  | .b => {lean_word(DIG['b'])}
  | .c => {lean_word(DIG['c'])}
  | .d => {lean_word(DIG['d'])}
  | .e => {lean_word(DIG['e'])}

/-- Digits, each with the gap after it, then the rest of the tape. -/
def enc : List (Dg × Nat) → Tape → Tape
  | [], T => T
  | (x, g) :: xs, T => app x.word (rep g W (enc xs T))

/-- A sample configuration: the head on the leftmost cell, blank tape to its left. -/
def sample (g : Nat) (xs : List (Dg × Nat)) (T : Tape) : Config :=
  ⟨blank, app [false, false] (rep g W (enc xs T)), .{S}⟩

/-- The head arriving at a digit, moving right; `L` is what it has crossed. -/
def arr (L R : Tape) : Config := ⟨cons true L, app [false, false, true] R, .{R}⟩

/-- The head moving left after its turn. -/
def ret (L R : Tape) : Config := ⟨app [true, false, true] L, app [false, false] R, .{S}⟩

/-- The increment: `some (δ, xs')` with `δ` the number of `W`s added before the digits (0 or 1). -/
def bump : List (Dg × Nat) → Option (Nat × List (Dg × Nat))
  | [] => none
  | (.d, h) :: xs =>
    match bump xs with
    | some (δ, ys) => some (0, (.e, h + δ) :: ys)
    | none => none
  | (.a, h + 1) :: xs => some (0, (.b, h) :: xs)
  | (.b, h + 1) :: xs => some (0, (.c, h + 1) :: xs)
  | (.c, h + 1) :: xs => some (0, (.d, h + 1) :: xs)
  | (.e, h + 1) :: xs => some (1, (.a, h) :: xs)
  | (_, 0) :: _ => none

/-- The steps from the arrival at the first digit to the return to the left of it. -/
def cost : List (Dg × Nat) → Nat
  | (.d, h) :: xs => {D} * h + {K} + cost xs
  | _ => {bo}

/-! ## The pieces, restated on the encoding -/

/-- A re-bracketing the generated rules sometimes leave: `(1010)^n 1 = 1 (0101)^n` read from the head. -/
theorem rot1 (n : Nat) (s : Tape) :
    rep n [true, false, true, false] (cons true s) = cons true (rep n [false, true, false, true] s) :=
  (rep_rotate n [true] [false, true, false, true] [true, false, true, false] rfl s).symm

theorem p_start (n : Nat) (R : Tape) :
    steps ({sa} * n + {sc}) ⟨blank, app [false, false] (rep n W R), .{S}⟩ = some (arr (rep n [false, true, false, true] blank) R) := by
  have h := start n R
  first | exact h | (rw [rot1] at h; exact h)

theorem p_carry (m : Nat) (L R : Tape) :
    steps ({ca} * m + {cc}) (arr L (app Dg.d.word (rep m W R))) =
      some (arr (rep m [false, true, false, true] (app [true, false, true, false, true] L)) R) := by
  have h := carry m L R
  first | exact h | (rw [rot1] at h; exact h)

theorem p_left_gap (k : Nat) (L R : Tape) :
    steps ({la} * k) (ret (rep k [false, true, false, true] L) R) = some (ret L (rep k W R)) :=
  left_gap k L R

theorem p_left_d (L R : Tape) :
    steps {ld} (ret (app [true, false, true, false, true] L) R) = some (ret L (app Dg.e.word R)) :=
  left_d L R

theorem p_left_end (R : Tape) :
    steps {le} (ret blank R) = some ⟨blank, app [false, false] (app W R), .{S}⟩ :=
  left_end R

/-! ## One pass: right to the digit that takes the increment, and back -/

theorem pass : ∀ (xs : List (Dg × Nat)) (δ : Nat) (ys : List (Dg × Nat)), bump xs = some (δ, ys) →
    ∀ L T : Tape, steps (cost xs) (arr L (enc xs T)) = some (ret L (rep δ W (enc ys T)))
  | [], _, _, h => by simp [bump] at h
  | (.d, h) :: xs, δ, ys, hb => by
    intro L T
    cases e : bump xs with
    | none => simp [bump, e] at hb
    | some p =>
      obtain ⟨δ', zs⟩ := p
      simp only [bump, e, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have h1 := p_carry h L (enc xs T)
      have h2 := pass xs δ' zs e (rep h [false, true, false, true] (app [true, false, true, false, true] L)) T
      have h3 := p_left_gap h (app [true, false, true, false, true] L) (rep δ' W (enc zs T))
      have h4 := p_left_d L (rep h W (rep δ' W (enc zs T)))
      have h5 := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
      have ee : enc ((Dg.e, h + δ') :: zs) T = app Dg.e.word (rep h W (rep δ' W (enc zs T))) := by
        simp only [enc, rep_add]
      rw [rep_zero, ee]
      exact steps_congr trans (by simp only [cost]; omega) h5
  | (.a, 0) :: _, _, _, h => by simp [bump] at h
  | (.b, 0) :: _, _, _, h => by simp [bump] at h
  | (.c, 0) :: _, _, _, h => by simp [bump] at h
  | (.e, 0) :: _, _, _, h => by simp [bump] at h
  | (.a, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_a L (rep g W (enc xs T))
  | (.b, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_b L (rep g W (enc xs T))
  | (.c, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_c L (rep g W (enc xs T))
  | (.e, g + 1) :: xs, δ, ys, hb => by
    intro L T
    simp only [bump, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact bounce_e L (rep g W (enc xs T))

/-- **One visit is one increment.**  From a sample configuration whose increment `bump` is defined, the machine runs,
without halting, to the sample configuration of the incremented counter, in exactly
`{G}·g₀ + {V} + cost xs` steps. -/
theorem visit (g : Nat) (xs : List (Dg × Nat)) (T : Tape) (δ : Nat) (ys : List (Dg × Nat))
    (hb : bump xs = some (δ, ys)) :
    steps ({G} * g + {V} + cost xs) (sample g xs T) = some (sample (g + 1 + δ) ys T) := by
  have h1 := p_start g (enc xs T)
  have h2 := pass xs δ ys hb (rep g [false, true, false, true] blank) T
  have h3 := p_left_gap g blank (rep δ W (enc ys T))
  have h4 := p_left_end (rep g W (rep δ W (enc ys T)))
  have h5 := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
  have ee : rep (g + 1 + δ) W (enc ys T) = app W (rep g W (rep δ W (enc ys T))) := by
    rw [show g + 1 + δ = (g + δ) + 1 by omega, rep_succ, rep_add]
  unfold sample
  rw [ee]
  exact steps_congr trans (by omega) h5

/-- `visit` iterated: as long as `bump` stays defined, the counter keeps counting. -/
def run : Nat → Nat × List (Dg × Nat) → Option (Nat × List (Dg × Nat))
  | 0, s => some s
  | n + 1, (g, xs) =>
    match bump xs with
    | some (δ, ys) => run n (g + 1 + δ, ys)
    | none => none

theorem run_sound : ∀ (n : Nat) (g : Nat) (xs : List (Dg × Nat)) (g' : Nat) (ys : List (Dg × Nat)) (T : Tape),
    run n (g, xs) = some (g', ys) → ∃ k, steps k (sample g xs T) = some (sample g' ys T)
  | 0, g, xs, g', ys, T, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl⟩
  | n + 1, g, xs, g', ys, T, h => by
    cases e : bump xs with
    | none => simp [run, e] at h
    | some p =>
      obtain ⟨δ, zs⟩ := p
      simp only [run, e] at h
      obtain ⟨k, hk⟩ := run_sound n (g + 1 + δ) zs g' ys T h
      exact ⟨_, steps_seq trans (visit g xs T δ zs e) hk⟩

end {ns}
'''

def pieces_file(M, ns, S, R, thms):
    doc = f'''# The piece rules of the counter

Generated by `py/gen_lean.py` with `bbtools.symtm.prove`: each rule is proved from single steps (`rfl`), the shift
rules `TM.cross_r` / `TM.cross_l` and re-bracketings `TM.rep_rotate`, for every value of the counts and every tape
`L`, `R` around.  Words are written left to right in the comments; in Lean the left tape is listed nearest the head
first.  `W = 0001`.  {S} is the state at the left end, {R} the state in which the head reaches a digit.'''
    head = f"import Machine\n\n/-!\n{doc}\n-/\n\nnamespace {ns}\n\nopen TM\n\n"
    return head + "\n".join(thms) + f"\nend {ns}\n"

def merge_file(M, ns, S, thm, desc):
    desc = desc.split(': ', 1)[1]
    return f'''import Machine
import Counter

/-!
# The merge of two adjacent `e` digits

Two digits `e e` side by side (the gap between them empty) at the start of the tape.  The visit that reaches them
contains the near miss (the head reads `0 1 0` in the state where `0 1 1` would halt), so it uses the one transition
in which the four machines of the family differ; it is the commonest place where their runs part ways.  For this
machine {desc}

The rule is proved for every left gap `n`, every gap `m + 1` after the pair and every rest `R`.
-/

namespace {ns}

open TM

{thm}
end {ns}
'''

def reach_file(M, ns, S, N, g0, xs, tail, trail):
    K, g1, ys = 0, g0, list(xs)
    while True:
        r = bump(ys)
        if r is None:
            break
        d, ys = r
        g1 += 1 + d
        K += 1
    why = 'the carry runs into the end of the tape' if all(x == 'd' for x, _ in ys) else 'a digit with an empty gap after it'
    ys = '[' + ', '.join(f'(.{x}, {g})' for x, g in ys) + ']'
    xsl = ', '.join(f'(.{x}, {g})' for x, g in xs)
    return f'''import Machine
import Counter

/-!
# From blank tape to a sample configuration

After {N:,} steps from blank tape the machine is at the sample configuration

    0 0 W^{g0} {' '.join(f'{x} W^{g}' for x, g in xs)} 0 0 1

with blank tape after it, made of standard digits only.  The run is evaluated by compiled code (`native_decide`) on
the list simulator of `TM/Fin.lean`, proved to agree with `steps`; the list it ends with is then identified with
`sample` by the kernel (`encList_app`).
-/

namespace {ns}

open TM

/-- The cells of `enc`, as a list. -/
def encList : List (Dg × Nat) → List Bool → List Bool
  | [], t => t
  | (x, g) :: xs, t => x.word ++ (List.replicate g W).flatten ++ encList xs t

theorem app_flatten_rep (g : Nat) (s : Tape) : app (List.replicate g W).flatten s = rep g W s := by
  induction g with
  | zero => rfl
  | succ g ih => simp only [List.replicate_succ, List.flatten_cons, ← app_app, ih]; rfl

theorem encList_app (xs : List (Dg × Nat)) (t : List Bool) : app (encList xs t) blank = enc xs (app t blank) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨x, g⟩ := p
    simp only [encList, enc, ← app_app, app_flatten_rep, ih]

theorem app_falses (k : Nat) : app (List.replicate k false) blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, app_cons, ih, cons_false_blank]

/-- The sample configuration reached. -/
def firstDigits : List (Dg × Nat) := [{xsl}]

theorem reach_list : fsteps {N} (FCfg.blank .A) =
    some ⟨[], [false, false] ++ (List.replicate {g0} W).flatten ++ encList firstDigits {lean_word(tail)} ++ List.replicate {trail} false, .{S}⟩ := by
  native_decide

/-- **The run from blank tape reaches a sample configuration** after {N:,} steps. -/
theorem reach : steps {N} init = some (sample {g0} firstDigits (app {lean_word(tail)} blank)) := by
  have h := blank_reaches trans reach_list
  show TM.steps trans {N} (blankCfg St.A) = _
  rw [h]
  unfold sample FCfg.toCfg
  simp only [← app_app, app_falses, app_flatten_rep, encList_app]
  rfl

set_option maxRecDepth 100000 in
/-- The counter rule alone then carries the run through the next {K} visits, to the first collision
(`bump` undefined: {why}). -/
theorem counted : ∃ k, steps k init = some (sample {g1} {ys} (app {lean_word(tail)} blank)) := by
  obtain ⟨k, hk⟩ := run_sound {K} {g0} firstDigits {g1} {ys} (app {lean_word(tail)} blank) (by decide)
  exact ⟨_, steps_seq trans reach hk⟩

end {ns}
'''

def bump(xs):
    if not xs:
        return None
    x, h = xs[0]
    if x == 'd':
        r = bump(xs[1:])
        if r is None:
            return None
        d, ys = r
        return (0, [('e', h + d)] + ys)
    if h == 0:
        return None
    return {'a': (0, [('b', h - 1)]), 'b': (0, [('c', h)]), 'c': (0, [('d', h)]), 'e': (1, [('a', h - 1)])}[x][0], \
        {'a': [('b', h - 1)], 'b': [('c', h)], 'c': [('d', h)], 'e': [('a', h - 1)]}[x] + xs[1:]

def main():
    M = os.path.basename(os.path.dirname(HERE))
    fam = FAMILY[M]
    ns, S, R = fam['ns'], fam['S'], fam['R']
    lean = os.path.join(HERE, '..', 'lean')
    thms, costs = piece_costs(M, S, R)
    open(os.path.join(lean, 'Pieces.lean'), 'w').write(pieces_file(M, ns, S, R, thms))
    open(os.path.join(lean, 'Counter.lean'), 'w').write(counter_file(M, ns, S, R, costs))
    name, a, b, desc = merge_rule(M)
    txt, fin = prove(M, name, a, b, rotate=True, doc=desc)
    open(os.path.join(lean, 'Merge.lean'), 'w').write(merge_file(M, ns, S, txt, desc))
    N, g0, xs, tail, trail = fam['reach']
    open(os.path.join(lean, 'Reach.lean'), 'w').write(reach_file(M, ns, S, N, g0, xs, tail, trail))
    print(costs)

if __name__ == '__main__':
    main()
