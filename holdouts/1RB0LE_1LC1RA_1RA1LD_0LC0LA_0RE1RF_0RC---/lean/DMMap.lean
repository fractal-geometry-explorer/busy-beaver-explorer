import Blank
import DMRules
import TM.MapOrbit

/-!
# DeepMind's halts-iff map, proved here

`DM.State`, `DM.start`, `DM.next` are DeepMind's (google-deepmind/cryptids (`BusyBeaver/BB6/M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.lean`), commit 3647718), copied unchanged
but for `ℕ` written `Nat`.  Their file proves with Mathlib that the machine halts iff the orbit of `next` from `start`
stops.  Here the same statement is proved on this repository's machine semantics with core Lean (`deepmind_halts_iff`),
so it no longer needs to be cited.

`enc` gives the configuration of each state, transcribed from DeepMind's `cfg_*` templates.  Each clause of `next` is
a rule of `DMRules.lean`, found by the symbolic simulator and written by `tools/deepmind/dmproof.py`: the template of
the left side runs, in at least one step, to the template of the right side, or to a halting configuration.
`TM.halts_iff_orbit` turns that into the halts-iff statement.
-/

set_option autoImplicit false

namespace H9516

namespace DM

inductive State where
  /-- $C(m, k, b) := 0^\infty\,1^m\,(10)^k\,\mathrm{C}{>}\,1^b\,0^\infty$. -/
  | C (m k b : Nat)

def start : State := .C 0 0 2

def next : State → Option State
  | .C m k 0 => some (.C (m + 1) 0 (2 * k + 2))
  | .C 0 k 1 => some (.C (2 * k + 3) 0 2)
  | .C 0 k (b + 2) => some (.C (2 * k + 2) 1 b)
  | .C 1 0 (b + 1) => some (.C 0 0 (b + 3))
  | .C 1 (k + 1) 1 => some (.C (2 * k + 7) 0 2)
  | .C 1 (k + 1) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C 2 0 1 => some (.C 0 1 0)
  | .C 2 0 (_ + 2) => none
  | .C 2 1 (b + 1) => some (.C 0 1 (b + 1))
  | .C 2 (k + 2) 1 => some (.C (2 * k + 7) 0 2)
  | .C 2 (k + 2) (b + 2) => some (.C (2 * k + 6) 1 b)
  | .C (m + 3) k (b + 1) => some (.C m (k + 2) b)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

open TM DM

/-- The configuration of a state (DeepMind's `encode`). -/
def enc : State → Config
  | .C m k b => ⟨rep (k) [false, true] (rep (m) [true] (blank)), rep (b) [true] (blank), .C⟩

def Rel (s : State) (c : Config) : Prop := c = enc s

/-- `cfg_rfl` after unfolding `enc`. -/
macro "enc_rfl" : tactic => `(tactic| first | (simp only [enc]; done) | (simp only [enc]; cfg_rfl) | cfg_rfl | (simp only [enc, Nat.mul_succ]; cfg_rfl))

theorem land {c c' d : Config} {n : Nat} {s : State} (h : steps n c = some c') (e₁ : d = c := by enc_rfl)
    (e₂ : c' = enc s := by enc_rfl) (hn : 0 < n := by omega) : TM.Lands trans Rel d (some s) :=
  ⟨_, plus_of h e₁ e₂ hn, rfl⟩

theorem halt {c c' d : Config} {n : Nat} (h : steps n c = some c') (e₁ : d = c := by enc_rfl)
    (hd : step c' = none := by rfl) : TM.Lands trans Rel d none :=
  halts_at h e₁ hd

set_option maxHeartbeats 2000000 in
theorem c0_C (m k : Nat) : TM.Lands trans Rel (enc (.C m k 0)) (next (.C m k 0)) := by
  have e : next (.C m k 0) = some (.C (m + 1) 0 (2 * k + 2)) := by first | rfl | simp only [next]
  rw [e]
  exact land (r0_C k m)

set_option maxHeartbeats 2000000 in
theorem c1_C (k : Nat) : TM.Lands trans Rel (enc (.C 0 k 1)) (next (.C 0 k 1)) := by
  have e : next (.C 0 k 1) = some (.C (2 * k + 3) 0 2) := by first | rfl | simp only [next]
  rw [e]
  exact match k with
    | 0 => land (r1_C_0)
    | k + 1 => land (r1_C_1 k)

set_option maxHeartbeats 2000000 in
theorem c2_C (k b : Nat) : TM.Lands trans Rel (enc (.C 0 k (b + 2))) (next (.C 0 k (b + 2))) := by
  have e : next (.C 0 k (b + 2)) = some (.C (2 * k + 2) 1 b) := by first | rfl | simp only [next]
  rw [e]
  exact match k with
    | 0 => land (r2_C_0 b)
    | k + 1 => land (r2_C_1 b k)

set_option maxHeartbeats 2000000 in
theorem c3_C (b : Nat) : TM.Lands trans Rel (enc (.C 1 0 (b + 1))) (next (.C 1 0 (b + 1))) := by
  have e : next (.C 1 0 (b + 1)) = some (.C 0 0 (b + 3)) := by first | rfl | simp only [next]
  rw [e]
  exact land (r3_C b)

set_option maxHeartbeats 2000000 in
theorem c4_C (k : Nat) : TM.Lands trans Rel (enc (.C 1 (k + 1) 1)) (next (.C 1 (k + 1) 1)) := by
  have e : next (.C 1 (k + 1) 1) = some (.C (2 * k + 7) 0 2) := by first | rfl | simp only [next]
  rw [e]
  exact land (r4_C k)

set_option maxHeartbeats 2000000 in
theorem c5_C (k b : Nat) : TM.Lands trans Rel (enc (.C 1 (k + 1) (b + 2))) (next (.C 1 (k + 1) (b + 2))) := by
  have e : next (.C 1 (k + 1) (b + 2)) = some (.C (2 * k + 6) 1 b) := by first | rfl | simp only [next]
  rw [e]
  exact land (r5_C b k)

set_option maxHeartbeats 2000000 in
theorem c6_C : TM.Lands trans Rel (enc (.C 2 0 1)) (next (.C 2 0 1)) := by
  have e : next (.C 2 0 1) = some (.C 0 1 0) := by first | rfl | simp only [next]
  rw [e]
  exact land (r6_C)

set_option maxHeartbeats 2000000 in
theorem c7_C (u2 : Nat) : TM.Lands trans Rel (enc (.C 2 0 (u2 + 2))) (next (.C 2 0 (u2 + 2))) := by
  have e : next (.C 2 0 (u2 + 2)) = none := by first | rfl | simp only [next]
  rw [e]
  exact halt (r7_C u2)

set_option maxHeartbeats 2000000 in
theorem c8_C (b : Nat) : TM.Lands trans Rel (enc (.C 2 1 (b + 1))) (next (.C 2 1 (b + 1))) := by
  have e : next (.C 2 1 (b + 1)) = some (.C 0 1 (b + 1)) := by first | rfl | simp only [next]
  rw [e]
  exact land (r8_C b)

set_option maxHeartbeats 2000000 in
theorem c9_C (k : Nat) : TM.Lands trans Rel (enc (.C 2 (k + 2) 1)) (next (.C 2 (k + 2) 1)) := by
  have e : next (.C 2 (k + 2) 1) = some (.C (2 * k + 7) 0 2) := by first | rfl | simp only [next]
  rw [e]
  exact land (r9_C k)

set_option maxHeartbeats 2000000 in
theorem c10_C (k b : Nat) : TM.Lands trans Rel (enc (.C 2 (k + 2) (b + 2))) (next (.C 2 (k + 2) (b + 2))) := by
  have e : next (.C 2 (k + 2) (b + 2)) = some (.C (2 * k + 6) 1 b) := by first | rfl | simp only [next]
  rw [e]
  exact land (r10_C b k)

set_option maxHeartbeats 2000000 in
theorem c11_C (m k b : Nat) : TM.Lands trans Rel (enc (.C (m + 3) k (b + 1))) (next (.C (m + 3) k (b + 1))) := by
  have e : next (.C (m + 3) k (b + 1)) = some (.C m (k + 2) b) := by first | rfl | simp only [next]
  rw [e]
  exact match k with
    | 0 => land (r11_C_0 b m)
    | k + 1 => land (r11_C_1 b k m)

/-- Every state lands where `next` says. -/
theorem step_enc : ∀ s, TM.Lands trans Rel (enc s) (next s)
  | .C m k 0 => c0_C m k
  | .C 0 k 1 => c1_C k
  | .C 0 k (b + 2) => c2_C k b
  | .C 1 0 (b + 1) => c3_C b
  | .C 1 (k + 1) 1 => c4_C k
  | .C 1 (k + 1) (b + 2) => c5_C k b
  | .C 2 0 1 => c6_C
  | .C 2 0 (u2 + 2) => c7_C u2
  | .C 2 1 (b + 1) => c8_C b
  | .C 2 (k + 2) 1 => c9_C k
  | .C 2 (k + 2) (b + 2) => c10_C k b
  | .C (m + 3) k (b + 1) => c11_C m k b

/-- **DeepMind's halts-iff map, proved here.**  The machine halts from blank tape if and only if the orbit of
DeepMind's `next` from `start` stops. -/
theorem deepmind_halts_iff : HaltsFromBlank ↔ ∃ n, (DM.orbit n).isNone = true := by
  have h : HaltsFromBlank ↔ ∃ n, TM.orbit next start n = none :=
    halts_iff_orbit (Rel := Rel) ⟨_, _, blank_start, by simp only [Rel]; enc_rfl⟩ (fun s c h => by subst h; exact step_enc s)
  have e : ∀ n, DM.orbit n = TM.orbit next start n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp only [DM.orbit, TM.orbit, ih]
  rw [h]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [e, hn]; rfl⟩
  · rintro ⟨n, hn⟩; refine ⟨n, ?_⟩; rw [← e]; cases h' : DM.orbit n <;> simp_all

end H9516
