import Blank
import DMRules
import TM.MapOrbit

/-!
# DeepMind's halts-iff map, proved here

`DM.State`, `DM.start`, `DM.next` are DeepMind's (google-deepmind/cryptids (`BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean`), commit 3647718), copied unchanged
but for `ℕ` written `Nat`.  Their file proves with Mathlib that the machine halts iff the orbit of `next` from `start`
stops.  Here the same statement is proved on this repository's machine semantics with core Lean (`deepmind_halts_iff`),
so it no longer needs to be cited.

`enc` gives the configuration of each state, transcribed from DeepMind's `cfg_*` templates.  Each clause of `next` is
a rule of `DMRules.lean`, found by the symbolic simulator and written by `tools/deepmind/dmproof.py`: the template of
the left side runs, in at least one step, to the template of the right side, or to a halting configuration.
`TM.halts_iff_orbit` turns that into the halts-iff statement.
-/

set_option autoImplicit false

namespace H48788

namespace DM

inductive State where
  | S0z (a c : Nat)
  | S0p (a b c : Nat)
  | T1 (j m : Nat)
  | T0 (j m : Nat)
  | T11 (j m : Nat)
  | T3 (j m : Nat)
  | T10 (j m : Nat)
  | Tn (j : Nat)
  | Ea (n : Nat)
  | Eb (k t : Nat)
  | Ec (n : Nat)
  | Ed (k t : Nat)
  deriving DecidableEq, Repr

def start : State := .T1 0 1

def next : State → Option State
  | .S0z a 0 => some (.T1 0 (2 * a + 3))
  | .S0z a (c + 1) => some (.S0p 0 (2 * a + 4) c)
  | .S0p a 0 c => some (.S0p 0 (2 * a + 1) (c + 4))
  | .S0p a 1 c => some (.S0p (a + 2) 0 (c + 2))
  | .S0p a 2 c => some (.S0z (a + 2) c)
  | .S0p a (b + 3) c => some (.S0p (a + 2) b c)
  | .T1 _ 0 => some (.Tn 0)
  | .T1 j 1 => some (.T11 0 (2 * j + 7))
  | .T1 j 2 => some (.S0p 0 (2 * j + 5) 3)
  | .T1 j (m + 3) => some (.T1 (j + 2) m)
  | .T0 j 0 => some (.S0z (j + 1) 0)
  | .T0 _ 1 => none
  | .T0 j 2 => some (.S0z (j + 2) 0)
  | .T0 j (m + 3) => some (.T0 (j + 2) m)
  | .T11 j 0 => some (.T1 0 (2 * j + 6))
  | .T11 j 1 => some (.T3 0 (2 * j + 7))
  | .T11 j 2 => some (.Ea j)
  | .T11 j (m + 3) => some (.T11 (j + 2) m)
  | .T3 j 0 => some (.T1 0 (2 * j + 8))
  | .T3 j 1 => some (.T10 0 (2 * j + 7))
  | .T3 j 2 => some (.Ec j)
  | .T3 j (m + 3) => some (.T3 (j + 2) m)
  | .T10 j 0 => some (.T0 0 (2 * j + 6))
  | .T10 _ 1 => none
  | .T10 _ 2 => none
  | .T10 j (m + 3) => some (.T10 (j + 2) m)
  | .Tn j => some (.Tn (j + 2))
  | .Ea n => some (.Eb 0 (2 * n + 1))
  | .Eb k t => some (.Eb (k + 1) t)
  | .Ec n => some (.Ed 0 (2 * n + 1))
  | .Ed k t => some (.Ed (k + 1) t)

/-- `n` steps of `next` from `start`: DeepMind's `(Option.bind · next)^[n] (some start)` in `CollatzHalts`. -/
def orbit : Nat → Option State
  | 0 => some start
  | n + 1 => Option.bind (orbit n) next

end DM

open TM DM

/-- The configuration of a state (DeepMind's `encode`). -/
def enc : State → Config
  | .S0z a c => ⟨cons false (rep (c) [true, false] (cons false (cons true (blank)))), cons true (cons false (cons true (rep (a) [false, true] (cons true (blank))))), .B⟩
  | .S0p a b c => ⟨rep (b) [false] (cons true (cons false (rep (c) [true, false] (cons false (cons true (blank)))))), cons false (cons false (cons true (rep (a) [false, true] (cons true (blank))))), .B⟩
  | .T1 j m => ⟨cons false (rep (j) [true, false] (cons true (cons false (cons false (cons true (rep (m) [false] (cons true (blank)))))))), cons true (blank), .F⟩
  | .T0 j m => ⟨cons false (rep (j) [true, false] (cons true (cons false (cons false (cons true (rep (m) [false] (cons true (cons true (blank))))))))), cons true (blank), .F⟩
  | .T11 j m => ⟨cons false (rep (j) [true, false] (cons true (cons false (cons false (cons true (rep (m) [false] (cons true (cons false (cons true (blank)))))))))), cons true (blank), .F⟩
  | .T3 j m => ⟨cons false (rep (j) [true, false] (cons true (cons false (cons false (cons true (rep (m) [false] (cons true (cons false (cons false (cons false (cons true (blank)))))))))))), cons true (blank), .F⟩
  | .T10 j m => ⟨cons false (rep (j) [true, false] (cons true (cons false (cons false (cons true (rep (m) [false] (cons true (cons false (cons true (cons true (blank))))))))))), cons true (blank), .F⟩
  | .Tn j => ⟨cons false (rep (j) [true, false] (cons true (cons false (cons false (cons true (blank)))))), cons true (blank), .F⟩
  | .Ea n => ⟨cons true (cons false (cons false (cons false (cons false (cons true (cons false (rep (n) [true, false] (cons true (cons false (cons false (cons false (cons true (cons false (cons true (blank))))))))))))))), cons true (blank), .B⟩
  | .Eb k t => ⟨cons true (cons false (cons false (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (rep (k) [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true] (rep (t) [false] (cons true (cons true (cons false (cons true (blank)))))))))))))))))))))))))))))))))), cons true (blank), .B⟩
  | .Ec n => ⟨cons true (cons false (cons false (cons false (cons false (cons true (cons false (rep (n) [true, false] (cons true (blank))))))))), cons true (blank), .B⟩
  | .Ed k t => ⟨cons true (cons false (cons false (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (rep (k) [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true] (rep (t) [false] (cons true (blank))))))))))))))))))))))))))))))), cons true (blank), .B⟩

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
theorem c0_S0z (a : Nat) : TM.Lands trans Rel (enc (.S0z a 0)) (next (.S0z a 0)) :=
  land (r0_S0z a)

set_option maxHeartbeats 2000000 in
theorem c1_S0z (a c : Nat) : TM.Lands trans Rel (enc (.S0z a (c + 1))) (next (.S0z a (c + 1))) :=
  land (r1_S0z a c)

set_option maxHeartbeats 2000000 in
theorem c2_S0p (a c : Nat) : TM.Lands trans Rel (enc (.S0p a 0 c)) (next (.S0p a 0 c)) :=
  land (r2_S0p a c)

set_option maxHeartbeats 2000000 in
theorem c3_S0p (a c : Nat) : TM.Lands trans Rel (enc (.S0p a 1 c)) (next (.S0p a 1 c)) :=
  match c with
  | 0 => land (r3_S0p_0 a)
  | c + 1 => land (r3_S0p_1 a c)

set_option maxHeartbeats 2000000 in
theorem c4_S0p (a c : Nat) : TM.Lands trans Rel (enc (.S0p a 2 c)) (next (.S0p a 2 c)) :=
  land (r4_S0p a c)

set_option maxHeartbeats 2000000 in
theorem c5_S0p (a b c : Nat) : TM.Lands trans Rel (enc (.S0p a (b + 3) c)) (next (.S0p a (b + 3) c)) :=
  land (r5_S0p a b c)

set_option maxHeartbeats 2000000 in
theorem c6_T1 (u0 : Nat) : TM.Lands trans Rel (enc (.T1 u0 0)) (next (.T1 u0 0)) :=
  land (r6_T1 u0)

set_option maxHeartbeats 2000000 in
theorem c7_T1 (j : Nat) : TM.Lands trans Rel (enc (.T1 j 1)) (next (.T1 j 1)) :=
  land (r7_T1 j)

set_option maxHeartbeats 2000000 in
theorem c8_T1 (j : Nat) : TM.Lands trans Rel (enc (.T1 j 2)) (next (.T1 j 2)) :=
  land (r8_T1 j)

set_option maxHeartbeats 2000000 in
theorem c9_T1 (j m : Nat) : TM.Lands trans Rel (enc (.T1 j (m + 3))) (next (.T1 j (m + 3))) :=
  land (r9_T1 j m)

set_option maxHeartbeats 2000000 in
theorem c10_T0 (j : Nat) : TM.Lands trans Rel (enc (.T0 j 0)) (next (.T0 j 0)) :=
  land (r10_T0 j)

set_option maxHeartbeats 2000000 in
theorem c11_T0 (u0 : Nat) : TM.Lands trans Rel (enc (.T0 u0 1)) (next (.T0 u0 1)) :=
  halt (r11_T0 u0)

set_option maxHeartbeats 2000000 in
theorem c12_T0 (j : Nat) : TM.Lands trans Rel (enc (.T0 j 2)) (next (.T0 j 2)) :=
  land (r12_T0 j)

set_option maxHeartbeats 2000000 in
theorem c13_T0 (j m : Nat) : TM.Lands trans Rel (enc (.T0 j (m + 3))) (next (.T0 j (m + 3))) :=
  land (r13_T0 j m)

set_option maxHeartbeats 2000000 in
theorem c14_T11 (j : Nat) : TM.Lands trans Rel (enc (.T11 j 0)) (next (.T11 j 0)) :=
  land (r14_T11 j)

set_option maxHeartbeats 2000000 in
theorem c15_T11 (j : Nat) : TM.Lands trans Rel (enc (.T11 j 1)) (next (.T11 j 1)) :=
  land (r15_T11 j)

set_option maxHeartbeats 2000000 in
theorem c16_T11 (j : Nat) : TM.Lands trans Rel (enc (.T11 j 2)) (next (.T11 j 2)) :=
  land (r16_T11 j)

set_option maxHeartbeats 2000000 in
theorem c17_T11 (j m : Nat) : TM.Lands trans Rel (enc (.T11 j (m + 3))) (next (.T11 j (m + 3))) :=
  land (r17_T11 j m)

set_option maxHeartbeats 2000000 in
theorem c18_T3 (j : Nat) : TM.Lands trans Rel (enc (.T3 j 0)) (next (.T3 j 0)) :=
  land (r18_T3 j)

set_option maxHeartbeats 2000000 in
theorem c19_T3 (j : Nat) : TM.Lands trans Rel (enc (.T3 j 1)) (next (.T3 j 1)) :=
  land (r19_T3 j)

set_option maxHeartbeats 2000000 in
theorem c20_T3 (j : Nat) : TM.Lands trans Rel (enc (.T3 j 2)) (next (.T3 j 2)) :=
  land (r20_T3 j)

set_option maxHeartbeats 2000000 in
theorem c21_T3 (j m : Nat) : TM.Lands trans Rel (enc (.T3 j (m + 3))) (next (.T3 j (m + 3))) :=
  land (r21_T3 j m)

set_option maxHeartbeats 2000000 in
theorem c22_T10 (j : Nat) : TM.Lands trans Rel (enc (.T10 j 0)) (next (.T10 j 0)) :=
  land (r22_T10 j)

set_option maxHeartbeats 2000000 in
theorem c23_T10 (u0 : Nat) : TM.Lands trans Rel (enc (.T10 u0 1)) (next (.T10 u0 1)) :=
  halt (r23_T10 u0)

set_option maxHeartbeats 2000000 in
theorem c24_T10 (u0 : Nat) : TM.Lands trans Rel (enc (.T10 u0 2)) (next (.T10 u0 2)) :=
  halt (r24_T10 u0)

set_option maxHeartbeats 2000000 in
theorem c25_T10 (j m : Nat) : TM.Lands trans Rel (enc (.T10 j (m + 3))) (next (.T10 j (m + 3))) :=
  land (r25_T10 j m)

set_option maxHeartbeats 2000000 in
theorem c26_Tn (j : Nat) : TM.Lands trans Rel (enc (.Tn j)) (next (.Tn j)) :=
  land (r26_Tn j)

set_option maxHeartbeats 2000000 in
theorem c27_Ea (n : Nat) : TM.Lands trans Rel (enc (.Ea n)) (next (.Ea n)) :=
  land (r27_Ea n)

set_option maxHeartbeats 2000000 in
theorem c28_Eb (k t : Nat) : TM.Lands trans Rel (enc (.Eb k t)) (next (.Eb k t)) :=
  land (r28_Eb k t)

set_option maxHeartbeats 2000000 in
theorem c29_Ec (n : Nat) : TM.Lands trans Rel (enc (.Ec n)) (next (.Ec n)) :=
  land (r29_Ec n)

set_option maxHeartbeats 2000000 in
theorem c30_Ed (k t : Nat) : TM.Lands trans Rel (enc (.Ed k t)) (next (.Ed k t)) :=
  land (r30_Ed k t)

/-- Every state lands where `next` says. -/
theorem step_enc : ∀ s, TM.Lands trans Rel (enc s) (next s)
  | .S0z a 0 => c0_S0z a
  | .S0z a (c + 1) => c1_S0z a c
  | .S0p a 0 c => c2_S0p a c
  | .S0p a 1 c => c3_S0p a c
  | .S0p a 2 c => c4_S0p a c
  | .S0p a (b + 3) c => c5_S0p a b c
  | .T1 u0 0 => c6_T1 u0
  | .T1 j 1 => c7_T1 j
  | .T1 j 2 => c8_T1 j
  | .T1 j (m + 3) => c9_T1 j m
  | .T0 j 0 => c10_T0 j
  | .T0 u0 1 => c11_T0 u0
  | .T0 j 2 => c12_T0 j
  | .T0 j (m + 3) => c13_T0 j m
  | .T11 j 0 => c14_T11 j
  | .T11 j 1 => c15_T11 j
  | .T11 j 2 => c16_T11 j
  | .T11 j (m + 3) => c17_T11 j m
  | .T3 j 0 => c18_T3 j
  | .T3 j 1 => c19_T3 j
  | .T3 j 2 => c20_T3 j
  | .T3 j (m + 3) => c21_T3 j m
  | .T10 j 0 => c22_T10 j
  | .T10 u0 1 => c23_T10 u0
  | .T10 u0 2 => c24_T10 u0
  | .T10 j (m + 3) => c25_T10 j m
  | .Tn j => c26_Tn j
  | .Ea n => c27_Ea n
  | .Eb k t => c28_Eb k t
  | .Ec n => c29_Ec n
  | .Ed k t => c30_Ed k t

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

end H48788
