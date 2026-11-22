import Blank
import DMRules
import TM.MapOrbit

/-!
# DeepMind's halts-iff map, proved here

`DM.State`, `DM.start`, `DM.next` are DeepMind's (google-deepmind/cryptids (`BusyBeaver/BB6/M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean`), commit 3647718), copied unchanged
but for `ℕ` written `Nat`.  Their file proves with Mathlib that the machine halts iff the orbit of `next` from `start`
stops.  Here the same statement is proved on this repository's machine semantics with core Lean (`deepmind_halts_iff`),
so it no longer needs to be cited.

`enc` gives the configuration of each state, transcribed from DeepMind's `cfg_*` templates.  Each clause of `next` is
a rule of `DMRules.lean`, found by the symbolic simulator and written by `tools/deepmind/dmproof.py`: the template of
the left side runs, in at least one step, to the template of the right side, or to a halting configuration.
`TM.halts_iff_orbit` turns that into the halts-iff statement.
-/

set_option autoImplicit false

namespace H24009

namespace DM

inductive State where
  | D7 (a b : Nat)
  | D74 (a b : Nat)
  | D75 (a b c : Nat)
  | D76 (a b c : Nat)
  | D77 (a b c d : Nat)
  | D158 (a b c : Nat)
  | D160 (a b c : Nat)
  | D162 (a b c d : Nat)
  | D230 (a b c : Nat)
  | D231 (a b c d : Nat)
  | D294 (a b c : Nat)
  | D296 (a b c d : Nat)

def start : State := .D7 0 0

def next : State → Option State
  | .D7 0 b => some (.D77 0 0 0 (b + 1))
  | .D7 (a + 1) b => some (.D7 a (b + 1))
  | .D74 0 b => some (.D7 (b + 2) 0)
  | .D74 (a + 1) b => some (.D74 a (b + 1))
  | .D75 0 b 0 => some (.D158 (b + 1) 0 0)
  | .D75 0 b (c + 1) => some (.D160 (b + 1) 0 c)
  | .D75 (a + 1) b c => some (.D75 a (b + 1) c)
  | .D76 0 b 0 => some (.D75 0 0 (b + 2))
  | .D76 0 b (c + 1) => some (.D77 0 0 (b + 2) c)
  | .D76 (a + 1) b c => some (.D76 a (b + 1) c)
  | .D77 0 b 0 d => some (.D158 (b + 1) 0 (d + 1))
  | .D77 0 b (c + 1) d => some (.D162 (b + 1) 0 c d)
  | .D77 (a + 1) b c d => some (.D77 a (b + 1) c d)
  | .D158 0 b 0 => some (.D230 0 0 (b + 3))
  | .D158 0 b (c + 1) => some (.D231 0 0 (b + 2) c)
  | .D158 (a + 1) b c => some (.D158 a (b + 1) c)
  | .D160 0 b 0 => some (.D74 (b + 2) 0)
  | .D160 0 b (c + 1) => some (.D75 (b + 2) 0 c)
  | .D160 (a + 1) b c => some (.D160 a (b + 1) c)
  | .D162 0 b 0 d => some (.D76 (b + 2) 0 d)
  | .D162 0 b (c + 1) d => some (.D77 (b + 2) 0 c d)
  | .D162 (a + 1) b c d => some (.D162 a (b + 1) c d)
  | .D230 0 _ 0 => none
  | .D230 0 b 1 => some (.D74 (b + 1) 0)
  | .D230 0 b (c + 2) => some (.D294 (b + 1) 0 c)
  | .D230 (a + 1) b c => some (.D230 a (b + 1) c)
  | .D231 0 b 0 d => some (.D76 (b + 1) 0 d)
  | .D231 0 b (c + 1) d => some (.D296 (b + 1) 0 c d)
  | .D231 (a + 1) b c d => some (.D231 a (b + 1) c d)
  | .D294 0 b c => some (.D230 (b + 2) 0 c)
  | .D294 (a + 1) b c => some (.D294 a (b + 1) c)
  | .D296 0 b 0 d => some (.D158 (b + 2) 0 d)
  | .D296 0 b (c + 1) d => some (.D231 (b + 2) 0 c d)
  | .D296 (a + 1) b c d => some (.D296 a (b + 1) c d)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

open TM DM

/-- The configuration of a state (DeepMind's `encode`). -/
def enc : State → Config
  | .D7 a b => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons true (blank)))), .D⟩
  | .D74 a b => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons false (cons true (blank))))))), .D⟩
  | .D75 a b c => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons false (cons false (rep (c) [false, false] (cons true (cons false (cons true (blank)))))))))), .D⟩
  | .D76 a b c => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons true (cons true (rep (c) [true, true] (cons false (cons true (blank)))))))))), .D⟩
  | .D77 a b c d => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons false (cons false (rep (c) [false, false] (cons true (cons true (cons true (rep (d) [true, true] (cons false (cons true (blank))))))))))))), .D⟩
  | .D158 a b c => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons true (rep (c) [true, true] (cons false (cons true (blank))))))))), .D⟩
  | .D160 a b c => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons false (cons false (rep (c) [false, false] (cons true (cons false (cons true (blank))))))))))), .D⟩
  | .D162 a b c d => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons false (cons false (rep (c) [false, false] (cons true (cons true (cons true (rep (d) [true, true] (cons false (cons true (blank)))))))))))))), .D⟩
  | .D230 a b c => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons false (rep (c) [false, false] (cons true (blank))))))), .D⟩
  | .D231 a b c d => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons false (cons false (rep (c) [false, false] (cons true (cons true (rep (d) [true, true] (cons false (cons true (blank)))))))))))), .D⟩
  | .D294 a b c => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons false (cons false (cons false (rep (c) [false, false] (cons true (blank)))))))))), .D⟩
  | .D296 a b c d => ⟨cons true (cons true (rep (a) [true, true] (blank))), cons true (cons true (rep (b) [true, true] (cons false (cons true (cons false (cons false (rep (c) [false, false] (cons true (cons true (rep (d) [true, true] (cons false (cons true (blank))))))))))))), .D⟩

def Rel (s : State) (c : Config) : Prop := c = enc s

/-- `cfg_rfl` after unfolding `enc`. -/
macro "enc_rfl" : tactic => `(tactic| first | (simp only [enc]; done) | (simp only [enc]; cfg_rfl) | cfg_rfl)

theorem land {c c' d : Config} {n : Nat} {s : State} (h : steps n c = some c') (e₁ : d = c := by enc_rfl)
    (e₂ : c' = enc s := by enc_rfl) (hn : 0 < n := by omega) : TM.Lands trans Rel d (some s) :=
  ⟨_, plus_of h e₁ e₂ hn, rfl⟩

theorem halt {c c' d : Config} {n : Nat} (h : steps n c = some c') (e₁ : d = c := by enc_rfl)
    (hd : step c' = none := by rfl) : TM.Lands trans Rel d none :=
  halts_at h e₁ hd

set_option maxHeartbeats 2000000 in
theorem c0_D7 (b : Nat) : TM.Lands trans Rel (enc (.D7 0 b)) (next (.D7 0 b)) :=
  land (r0_D7 b)

set_option maxHeartbeats 2000000 in
theorem c1_D7 (a b : Nat) : TM.Lands trans Rel (enc (.D7 (a + 1) b)) (next (.D7 (a + 1) b)) :=
  land (r1_D7 a b)

set_option maxHeartbeats 2000000 in
theorem c2_D74 (b : Nat) : TM.Lands trans Rel (enc (.D74 0 b)) (next (.D74 0 b)) :=
  land (r2_D74 b)

set_option maxHeartbeats 2000000 in
theorem c3_D74 (a b : Nat) : TM.Lands trans Rel (enc (.D74 (a + 1) b)) (next (.D74 (a + 1) b)) :=
  land (r3_D74 a b)

set_option maxHeartbeats 2000000 in
theorem c4_D75 (b : Nat) : TM.Lands trans Rel (enc (.D75 0 b 0)) (next (.D75 0 b 0)) :=
  land (r4_D75 b)

set_option maxHeartbeats 2000000 in
theorem c5_D75 (b c : Nat) : TM.Lands trans Rel (enc (.D75 0 b (c + 1))) (next (.D75 0 b (c + 1))) :=
  land (r5_D75 b c)

set_option maxHeartbeats 2000000 in
theorem c6_D75 (a b c : Nat) : TM.Lands trans Rel (enc (.D75 (a + 1) b c)) (next (.D75 (a + 1) b c)) :=
  land (r6_D75 a b c)

set_option maxHeartbeats 2000000 in
theorem c7_D76 (b : Nat) : TM.Lands trans Rel (enc (.D76 0 b 0)) (next (.D76 0 b 0)) :=
  land (r7_D76 b)

set_option maxHeartbeats 2000000 in
theorem c8_D76 (b c : Nat) : TM.Lands trans Rel (enc (.D76 0 b (c + 1))) (next (.D76 0 b (c + 1))) :=
  land (r8_D76 b c)

set_option maxHeartbeats 2000000 in
theorem c9_D76 (a b c : Nat) : TM.Lands trans Rel (enc (.D76 (a + 1) b c)) (next (.D76 (a + 1) b c)) :=
  land (r9_D76 a b c)

set_option maxHeartbeats 2000000 in
theorem c10_D77 (b d : Nat) : TM.Lands trans Rel (enc (.D77 0 b 0 d)) (next (.D77 0 b 0 d)) :=
  land (r10_D77 b d)

set_option maxHeartbeats 2000000 in
theorem c11_D77 (b c d : Nat) : TM.Lands trans Rel (enc (.D77 0 b (c + 1) d)) (next (.D77 0 b (c + 1) d)) :=
  land (r11_D77 b c d)

set_option maxHeartbeats 2000000 in
theorem c12_D77 (a b c d : Nat) : TM.Lands trans Rel (enc (.D77 (a + 1) b c d)) (next (.D77 (a + 1) b c d)) :=
  land (r12_D77 a b c d)

set_option maxHeartbeats 2000000 in
theorem c13_D158 (b : Nat) : TM.Lands trans Rel (enc (.D158 0 b 0)) (next (.D158 0 b 0)) :=
  land (r13_D158 b)

set_option maxHeartbeats 2000000 in
theorem c14_D158 (b c : Nat) : TM.Lands trans Rel (enc (.D158 0 b (c + 1))) (next (.D158 0 b (c + 1))) :=
  land (r14_D158 b c)

set_option maxHeartbeats 2000000 in
theorem c15_D158 (a b c : Nat) : TM.Lands trans Rel (enc (.D158 (a + 1) b c)) (next (.D158 (a + 1) b c)) :=
  land (r15_D158 a b c)

set_option maxHeartbeats 2000000 in
theorem c16_D160 (b : Nat) : TM.Lands trans Rel (enc (.D160 0 b 0)) (next (.D160 0 b 0)) :=
  land (r16_D160 b)

set_option maxHeartbeats 2000000 in
theorem c17_D160 (b c : Nat) : TM.Lands trans Rel (enc (.D160 0 b (c + 1))) (next (.D160 0 b (c + 1))) :=
  land (r17_D160 b c)

set_option maxHeartbeats 2000000 in
theorem c18_D160 (a b c : Nat) : TM.Lands trans Rel (enc (.D160 (a + 1) b c)) (next (.D160 (a + 1) b c)) :=
  land (r18_D160 a b c)

set_option maxHeartbeats 2000000 in
theorem c19_D162 (b d : Nat) : TM.Lands trans Rel (enc (.D162 0 b 0 d)) (next (.D162 0 b 0 d)) :=
  land (r19_D162 b d)

set_option maxHeartbeats 2000000 in
theorem c20_D162 (b c d : Nat) : TM.Lands trans Rel (enc (.D162 0 b (c + 1) d)) (next (.D162 0 b (c + 1) d)) :=
  land (r20_D162 b c d)

set_option maxHeartbeats 2000000 in
theorem c21_D162 (a b c d : Nat) : TM.Lands trans Rel (enc (.D162 (a + 1) b c d)) (next (.D162 (a + 1) b c d)) :=
  land (r21_D162 a b c d)

set_option maxHeartbeats 2000000 in
theorem c22_D230 (u1 : Nat) : TM.Lands trans Rel (enc (.D230 0 u1 0)) (next (.D230 0 u1 0)) :=
  halt (r22_D230 u1)

set_option maxHeartbeats 2000000 in
theorem c23_D230 (b : Nat) : TM.Lands trans Rel (enc (.D230 0 b 1)) (next (.D230 0 b 1)) :=
  land (r23_D230 b)

set_option maxHeartbeats 2000000 in
theorem c24_D230 (b c : Nat) : TM.Lands trans Rel (enc (.D230 0 b (c + 2))) (next (.D230 0 b (c + 2))) :=
  land (r24_D230 b c)

set_option maxHeartbeats 2000000 in
theorem c25_D230 (a b c : Nat) : TM.Lands trans Rel (enc (.D230 (a + 1) b c)) (next (.D230 (a + 1) b c)) :=
  land (r25_D230 a b c)

set_option maxHeartbeats 2000000 in
theorem c26_D231 (b d : Nat) : TM.Lands trans Rel (enc (.D231 0 b 0 d)) (next (.D231 0 b 0 d)) :=
  land (r26_D231 b d)

set_option maxHeartbeats 2000000 in
theorem c27_D231 (b c d : Nat) : TM.Lands trans Rel (enc (.D231 0 b (c + 1) d)) (next (.D231 0 b (c + 1) d)) :=
  land (r27_D231 b c d)

set_option maxHeartbeats 2000000 in
theorem c28_D231 (a b c d : Nat) : TM.Lands trans Rel (enc (.D231 (a + 1) b c d)) (next (.D231 (a + 1) b c d)) :=
  land (r28_D231 a b c d)

set_option maxHeartbeats 2000000 in
theorem c29_D294 (b c : Nat) : TM.Lands trans Rel (enc (.D294 0 b c)) (next (.D294 0 b c)) :=
  land (r29_D294 b c)

set_option maxHeartbeats 2000000 in
theorem c30_D294 (a b c : Nat) : TM.Lands trans Rel (enc (.D294 (a + 1) b c)) (next (.D294 (a + 1) b c)) :=
  land (r30_D294 a b c)

set_option maxHeartbeats 2000000 in
theorem c31_D296 (b d : Nat) : TM.Lands trans Rel (enc (.D296 0 b 0 d)) (next (.D296 0 b 0 d)) :=
  land (r31_D296 b d)

set_option maxHeartbeats 2000000 in
theorem c32_D296 (b c d : Nat) : TM.Lands trans Rel (enc (.D296 0 b (c + 1) d)) (next (.D296 0 b (c + 1) d)) :=
  land (r32_D296 b c d)

set_option maxHeartbeats 2000000 in
theorem c33_D296 (a b c d : Nat) : TM.Lands trans Rel (enc (.D296 (a + 1) b c d)) (next (.D296 (a + 1) b c d)) :=
  land (r33_D296 a b c d)

/-- Every state lands where `next` says. -/
theorem step_enc : ∀ s, TM.Lands trans Rel (enc s) (next s)
  | .D7 0 b => c0_D7 b
  | .D7 (a + 1) b => c1_D7 a b
  | .D74 0 b => c2_D74 b
  | .D74 (a + 1) b => c3_D74 a b
  | .D75 0 b 0 => c4_D75 b
  | .D75 0 b (c + 1) => c5_D75 b c
  | .D75 (a + 1) b c => c6_D75 a b c
  | .D76 0 b 0 => c7_D76 b
  | .D76 0 b (c + 1) => c8_D76 b c
  | .D76 (a + 1) b c => c9_D76 a b c
  | .D77 0 b 0 d => c10_D77 b d
  | .D77 0 b (c + 1) d => c11_D77 b c d
  | .D77 (a + 1) b c d => c12_D77 a b c d
  | .D158 0 b 0 => c13_D158 b
  | .D158 0 b (c + 1) => c14_D158 b c
  | .D158 (a + 1) b c => c15_D158 a b c
  | .D160 0 b 0 => c16_D160 b
  | .D160 0 b (c + 1) => c17_D160 b c
  | .D160 (a + 1) b c => c18_D160 a b c
  | .D162 0 b 0 d => c19_D162 b d
  | .D162 0 b (c + 1) d => c20_D162 b c d
  | .D162 (a + 1) b c d => c21_D162 a b c d
  | .D230 0 u1 0 => c22_D230 u1
  | .D230 0 b 1 => c23_D230 b
  | .D230 0 b (c + 2) => c24_D230 b c
  | .D230 (a + 1) b c => c25_D230 a b c
  | .D231 0 b 0 d => c26_D231 b d
  | .D231 0 b (c + 1) d => c27_D231 b c d
  | .D231 (a + 1) b c d => c28_D231 a b c d
  | .D294 0 b c => c29_D294 b c
  | .D294 (a + 1) b c => c30_D294 a b c
  | .D296 0 b 0 d => c31_D296 b d
  | .D296 0 b (c + 1) d => c32_D296 b c d
  | .D296 (a + 1) b c d => c33_D296 a b c d

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

end H24009
