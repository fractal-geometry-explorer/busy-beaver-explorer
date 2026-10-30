import Events

/-!
# DeepMind's high-level map is the event map

google-deepmind/cryptids (file `BusyBeaver/BB6/Accelerations/M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean`,
commit `e5f59ed`, 27 October 2026) proves in Lean with Mathlib that this machine halts iff a map `highLevelNext` on
states `C(a, L)` halts from `C(3, [0])`.  `C(a, L)` is state C on the 0 right of `1^{a+1}`, with the blocks
`1^{L_i + 1}` further left, separated by single 0s and nearest first.

Their definitions are copied here into core Lean (`bumpHead^[k]` written `bumpHeadBy k`, as in their `Stack.lean`).
The event `x :: ls` of `Events.lean` is two steps before `C(x + 1, ls - 1)` (`toHL`), and

* `highLevelNext_eq`: **`highLevelNext (toHL b) = (ev b).map toHL`** for every event `b` of the run (`GoodE b`),
  by induction along the wave (`runEpoch_wave`), with no further reference to the machine;
* `hlOrbit_eq`: so the two orbits agree from `[2, 1]` = `C(3, [0])` on, and `halts_iff_hl`: the machine halts from
  blank tape iff DeepMind's high-level orbit halts, which is their `isHalt_iff_highLevel_acceleration` again, now
  reached through `ev_sound` and the super step of `Wave.lean`.
-/

namespace BB6b

namespace DM

/-- DeepMind's `bumpHead` (`Stack.lean`): the nearest stack entry gains one; an empty stack gets the entry `0`. -/
def bumpHead : List Nat → List Nat
  | [] => [0]
  | a :: s => (a + 1) :: s

/-- DeepMind's `bumpHeadBy`, their `bumpHead^[k]`. -/
def bumpHeadBy : Nat → List Nat → List Nat
  | 0, s => s
  | k + 1, s => bumpHeadBy k (bumpHead s)

/-- DeepMind's `HighLevelState`: `C(a, L)`. -/
inductive HighLevelState where
  | C (a : Nat) (L : List Nat)
  deriving DecidableEq, Repr

/-- DeepMind's `transferBHL`: sweep all digits of `R` onto `L` and return to the section `R = []`. -/
def transferBHL : List Nat → List Nat → HighLevelState
  | [], [] => .C 0 []
  | a :: L, [] => .C (a + 1) L
  | L, d :: R => transferBHL (d :: bumpHead L) R

/-- DeepMind's `runEpoch`: an entire epoch of their base map, until it returns to `R = []` or halts. -/
def runEpoch (a : Nat) (L R : List Nat) : Option HighLevelState :=
  let r := R.headD 0
  if a = 0 then
    List.casesOn L none fun b L' =>
      if b = 0 then some (transferBHL ((r + 2) :: 0 :: L') R.tail)
      else some (transferBHL ((b - 1) :: L') ((r + 2) :: R.tail))
  else
    let k := (a - 1) / 2
    if (a - 1) % 2 = 0 then
      some (transferBHL (bumpHeadBy k L) ((r + k + 2) :: R.tail))
    else if L = [] then
      runEpoch k [] (0 :: (r + k) :: R.tail)
    else
      runEpoch (L.headD 0 + k + 1) L.tail (0 :: (r + k) :: R.tail)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  · subst_vars; simp only [List.length_nil]; exact Prod.Lex.right _ (by omega)
  · cases L with
    | nil => contradiction
    | cons _ _ => apply Prod.Lex.left; simp only [List.length_cons]; omega

/-- DeepMind's `highLevelNext`. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C a L => runEpoch a L []

/-- DeepMind's `highLevelStart`, `C(3, [0])`. -/
def highLevelStart : HighLevelState := .C 3 [0]

end DM

open DM

/-! ## The translation -/

/-- The event `x :: ls` as DeepMind's state two steps later: `C(x + 1, ls - 1)`. -/
def toHL : List Nat → HighLevelState
  | [] => .C 0 []
  | x :: ls => .C (x + 1) (ls.map (· - 1))

theorem toHL_start : toHL [2, 1] = highLevelStart := rfl

theorem map_pred_succ : ∀ (L : List Nat), (∀ p ∈ L, 0 < p) → (L.map (· - 1)).map (· + 1) = L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
    intro h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, ih h.2]
    congr 1
    omega

theorem map_succ_pred (L : List Nat) : (L.map (· + 1)).map (· - 1) = L := by
  simp [List.map_map, Function.comp_def]

theorem bumpHeadBy_cons : ∀ (k a : Nat) (L : List Nat), bumpHeadBy k (a :: L) = (a + k) :: L := by
  intro k
  induction k with
  | zero => intro a L; rfl
  | succ k ih => intro a L; simp only [bumpHeadBy, bumpHead, ih]; congr 1; omega

theorem bumpHeadBy_nil (k : Nat) : bumpHeadBy (k + 1) [] = [k] := by
  simp only [bumpHeadBy, bumpHead, bumpHeadBy_cons, Nat.zero_add]

/-- A sweep onto the left stack is the final sweep `close` of `Events.lean`. -/
theorem transferBHL_cons (L : List Nat) (d : Nat) (R : List Nat) :
    transferBHL L (d :: R) = transferBHL (d :: bumpHead L) R := by
  cases L <;> rfl

theorem transferBHL_close : ∀ (R M : List Nat) (r : Nat),
    transferBHL M (r :: R) = toHL (close ((r :: R).map (· + 1)) ((bumpHead M).map (· + 1))) := by
  intro R
  induction R with
  | nil =>
    intro M r
    rw [transferBHL_cons]
    show HighLevelState.C (r + 1) (bumpHead M) = .C (r + 1 - 1 + 1) (((bumpHead M).map (· + 1)).map (· - 1))
    rw [map_succ_pred, Nat.add_sub_cancel]
  | cons r₂ R ih =>
    intro M r
    rw [transferBHL_cons, ih]
    simp only [List.map_cons]
    rw [close_cons (r + 1) _ _ (by omega) (List.cons_ne_nil _ _)]
    rfl

/-! ## An epoch is the wave -/

theorem runEpoch_left : ∀ (f d : Nat) (R : List Nat), 3 ≤ d → d ≤ f → R ≠ [] →
    runEpoch (d - 2) [] (0 :: R) = (leftEnd f d).map (fun W => toHL (close (R.map (· + 1)) W)) := by
  intro f
  induction f with
  | zero => intro d R h₃ hf _; omega
  | succ f ih =>
    intro d R h₃ hf hR
    have hR' : R.map (· + 1) ≠ [] := by simpa using hR
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · rw [runEpoch]
      simp only [show leftEnd (f + 1) 3 = some [4, 1] from leftEnd_odd f 3 (by omega) (by decide)]
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.one_ne_zero, ite_false, ite_true, List.headD_cons,
        List.tail_cons, Option.map_some]
      rw [transferBHL_close, List.map_cons, close_cons _ _ _ (by omega) hR']
      rfl
    · rw [runEpoch]
      have h : leftEnd (f + 1) 4 = none := by rw [leftEnd_even f 4 (by omega) (by omega)]; rw [leftEnd_two]; rfl
      rw [h]
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, ite_false, Nat.one_ne_zero,
        ite_true, List.headD_cons, List.tail_cons, Option.map_none]
      rw [runEpoch]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [leftEnd_odd f _ (by omega) hd, runEpoch]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      simp only [List.headD_cons, List.tail_cons, Option.map_some]
      rw [show (2 * j + 5 - 2 - 1) / 2 = j + 1 by omega, bumpHeadBy_nil, transferBHL_close, List.map_cons,
        close_cons _ _ _ (by omega) hR']
      simp only [bumpHead, List.map_cons, List.map_nil]
      rw [show 0 + (j + 1) + 2 + 1 + 1 = (2 * j + 5 + 5) / 2 by omega, show j + 1 + 1 = (2 * j + 5 - 1) / 2 by omega]
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [leftEnd_even f _ (by omega) hd, runEpoch]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      simp only [List.headD_cons, List.tail_cons]
      rw [show (2 * j + 6 - 2 - 1) / 2 = j + 3 - 2 by omega, show 0 + (j + 3 - 2) = j + 1 by omega,
        ih (j + 3) _ (by omega) (by omega) (by simp), show (2 * j + 6) / 2 = j + 3 by omega]
      cases leftEnd f (j + 3) with
      | none => rfl
      | some W =>
        simp only [Option.map_some, List.map_cons]
        rw [close_cons _ _ _ (by omega) hR']

/-- **An epoch is the wave**: DeepMind's `runEpoch` from a carry with value `d - 2` at the blocks `L` is `wave d L`
followed by the final sweep. -/
theorem runEpoch_wave : ∀ (L : List Nat) (d : Nat) (R : List Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) → R ≠ [] →
    runEpoch (d - 2) (L.map (· - 1)) (0 :: R) = (wave d L).map (fun W => toHL (close (R.map (· + 1)) W)) := by
  intro L
  induction L with
  | nil => intro d R h₃ _ hR; exact runEpoch_left d d R h₃ (Nat.le_refl d) hR
  | cons p L ih =>
    intro d R h₃ hL hR
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    obtain ⟨hp, hL⟩ := hL
    have hR' : R.map (· + 1) ≠ [] := by simpa using hR
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · rw [wave_odd 3 p L (by decide), runEpoch]
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.one_ne_zero, ite_false, ite_true, List.headD_cons,
        List.tail_cons, Option.map_some, List.map_cons]
      rw [transferBHL_close, List.map_cons, close_cons _ _ _ (by omega) hR']
      simp only [bumpHeadBy, bumpHead, List.map_cons, map_pred_succ L hL]
      rw [show 0 + 0 + 2 + 1 + 1 = (3 + 5) / 2 by omega, show p - 1 + 1 + 1 = p + 1 by omega]
    · rw [wave_even 4 p L (by decide), runEpoch]
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, ite_false, Nat.one_ne_zero,
        List.headD_cons, List.tail_cons, List.map_cons, reduceCtorEq]
      rw [show p - 1 + 0 + 1 = p + 2 - 2 by omega, show (0 : Nat) + 0 = 0 from rfl, ih (p + 2) (0 :: R) (by omega) hL (by simp)]
      cases wave (p + 4 / 2) L with
      | none => rfl
      | some W =>
        simp only [Option.map_some, List.map_cons]
        rw [close_cons _ _ _ (by omega) hR']
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [wave_odd _ p L hd, runEpoch]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      simp only [List.headD_cons, List.tail_cons, Option.map_some, List.map_cons]
      rw [show (2 * j + 5 - 2 - 1) / 2 = j + 1 by omega, bumpHeadBy_cons, transferBHL_close, List.map_cons,
        close_cons _ _ _ (by omega) hR']
      simp only [bumpHead, List.map_cons, map_pred_succ L hL]
      rw [show 0 + (j + 1) + 2 + 1 + 1 = (2 * j + 5 + 5) / 2 by omega,
        show p - 1 + (j + 1) + 1 + 1 = p + (2 * j + 5 - 1) / 2 by omega]
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [wave_even _ p L hd, runEpoch]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by simp)]
      simp only [List.headD_cons, List.tail_cons, List.map_cons]
      rw [show (2 * j + 6 - 2 - 1) / 2 = j + 1 by omega, show 0 + (j + 1) = j + 1 by omega,
        show p - 1 + (j + 1) + 1 = p + (j + 3) - 2 by omega, ih (p + (j + 3)) _ (by omega) hL (by simp),
        show (2 * j + 6) / 2 = j + 3 by omega]
      cases wave (p + (j + 3)) L with
      | none => rfl
      | some W =>
        simp only [Option.map_some, List.map_cons]
        rw [close_cons _ _ _ (by omega) hR']

/-! ## The high-level map is the event map -/

/-- **DeepMind's high-level map is the event map**: for every event `b` of the run, `highLevelNext (toHL b)` is
`toHL` of the next event, and `none` exactly when the machine halts after `b` (`ev_sound`). -/
theorem highLevelNext_eq (b : List Nat) (hb : GoodE b) : highLevelNext (toHL b) = (ev b).map toHL := by
  match b, hb with
  | x :: k :: ls, ⟨hk, hl⟩ =>
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ x = r + 2 * q := ⟨x / 2, x % 2, Nat.mod_lt _ (by decide), by omega⟩
    show runEpoch (r + 2 * q + 1) ((k - 1) :: ls.map (· - 1)) [] = _
    rw [runEpoch, ite_eq_right (by omega)]
    simp only [List.headD_nil, List.tail_nil, ev, show (r + 2 * q) / 2 = q by omega,
      show r + 2 * q + 1 - 1 = r + 2 * q by omega, show (r + 2 * q) % 2 = r by omega]
    match r, hr with
    | 0, _ =>
      simp only [ite_true, Option.map_some]
      rw [bumpHeadBy_cons, transferBHL_close]
      simp only [bumpHead, List.map_cons, List.map_nil, map_pred_succ ls hl]
      rw [show 0 + q + 2 + 1 = (q + 2) + 1 by omega, show k - 1 + q + 1 + 1 = k + q + 1 by omega]
      rfl
    | 1, _ =>
      simp only [Nat.one_ne_zero, ite_false, reduceCtorEq, List.headD_cons, List.tail_cons]
      rw [show k - 1 + q + 1 = k + q + 2 - 2 by omega, show 0 + q = q by omega,
        runEpoch_wave ls (k + q + 2) [q] (by omega) hl (by simp)]
      cases wave (k + q + 2) ls with
      | none => rfl
      | some W => rfl

/-- `j` steps of DeepMind's high-level map. -/
def hlOrbit : Nat → HighLevelState → Option HighLevelState
  | 0, s => some s
  | j + 1, s => (highLevelNext s).bind (hlOrbit j)

theorem hlOrbit_eq : ∀ (j : Nat) (b : List Nat), GoodE b → hlOrbit j (toHL b) = (evOrbit j b).map toHL := by
  intro j
  induction j with
  | zero => intro b _; rfl
  | succ j ih =>
    intro b hb
    simp only [hlOrbit, evOrbit, highLevelNext_eq b hb]
    cases e : ev b with
    | none => rfl
    | some b' => exact ih b' (ev_good b b' hb e)

/-- **The machine halts from blank tape iff DeepMind's high-level orbit from `C(3, [0])` halts.** -/
theorem halts_iff_hl : HaltsFromBlank ↔ ∃ j, hlOrbit j highLevelStart = none := by
  rw [halts_iff_ev, ← toHL_start]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, by rw [hlOrbit_eq j [2, 1] ⟨by decide, by simp⟩, hj]; rfl⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hlOrbit_eq j [2, 1] ⟨by decide, by simp⟩] at hj
    cases e : evOrbit j [2, 1] with
    | none => rfl
    | some b => rw [e] at hj; cases hj

end BB6b
