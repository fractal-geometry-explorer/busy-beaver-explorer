import Converse

/-!
# Where the halting family can be entered

`halts_iff_family` says the machine halts iff the orbit of `phase` meets `(m, m + 2, 2^(m+1) + 1)`.  Inside a phase
the event branch of `phase` adds `2^(d+1)` to `Y` and 1 to `d`, so it keeps `Y - 2^(d+1)` fixed.  Hence a family
point is preceded, back to the last overflow, by points `(d, M, 2^(d+1) + 1)` with `d + 2 ≤ M` (`Pre`), and:

> `halts_iff_lands`: the machine halts from blank tape **iff** some overflow phase of the orbit (one whose start
> `(d0, M0, Y0)` has `2^M0 ≤ Y0 + 2^(d0+1)`) returns a configuration `(d, M, 2^(d+1) + 1)` with `d + 2 ≤ M`.

In event terms (`X = Y - 2`, `j = d + 1`) the overflow must leave the string `1^j` (j ones) below a counter of
length j.  This is the form in which congruence invariants were searched for (`py/congruence.py`): every residue
class of the landing condition is met by the orbit for all moduli up to 1,500 and all powers of two up to `2^31`.
-/

namespace H140108

open TM

/-- A configuration from which the event chain runs into the family. -/
def Pre (d M Y : Nat) : Prop := Y = 2 ^ (d + 1) + 1 ∧ d + 2 ≤ M

/-- The phase from `(d, M, Y)` overflows. -/
def Overflows (d M Y : Nat) : Prop := 2 ^ M ≤ Y + 2 ^ (d + 1)

/-- An event step that ends in `Pre` starts in `Pre`. -/
theorem pre_of_event {d M Y d' M' Y' : Nat} (h : phase d M Y = some (d', M', Y'))
    (hev : Y + 2 ^ (d + 1) < 2 ^ M) (hp : Pre d' M' Y') : Pre d M Y := by
  unfold phase at h
  have hM : ¬ (M = 0 ∨ 2 ^ M ≤ Y) := by
    intro hc; rw [if_pos hc] at h; simp at h
  rw [if_neg hM, if_pos hev] at h
  obtain ⟨rfl, rfl, rfl⟩ : d + 1 = d' ∧ M = M' ∧ Y + 2 ^ (d + 1) = Y' := by
    simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h
  obtain ⟨h1, h2⟩ := hp
  have e1 : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ ..
  have e2 : 2 ^ (d + 1 + 1) = 2 ^ d * 2 * 2 := by rw [Nat.pow_succ, e1]
  exact ⟨by omega, by omega⟩

/-- An event step from a `Pre` point that is not in the family. -/
theorem phase_pre {d M : Nat} (hd : d + 3 ≤ M) :
    phase d M (2 ^ (d + 1) + 1) = some (d + 1, M, 2 ^ (d + 2) + 1) := by
  have e1 : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ ..
  have e2 : 2 ^ (d + 2) = 2 ^ d * 2 * 2 := by rw [Nat.pow_succ, e1]
  have e3' : 2 ^ (d + 3) = 2 ^ d * 2 * 2 * 2 := by rw [Nat.pow_succ, e2]
  have e3 : 2 ^ (d + 3) ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hd
  have e4 := Nat.two_pow_pos d
  have hev : 2 ^ (d + 1) + 1 + 2 ^ (d + 1) < 2 ^ M := by omega
  unfold phase
  rw [if_neg (by omega), if_pos hev]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- From a `Pre` point of the orbit the event chain reaches the family. -/
theorem famMet_of_pre : ∀ (i n d M : Nat), M = d + 2 + i → orbit n = some (d, M, 2 ^ (d + 1) + 1) → FamMet
  | 0, n, d, M, hM, h => ⟨n, d, by subst hM; exact h⟩
  | i + 1, n, d, M, hM, h => by
    have hs : orbit (n + 1) = some (d + 1, M, 2 ^ (d + 1 + 1) + 1) := by
      show (match orbit n with | some (d, M, Y) => phase d M Y | none => none) = _
      rw [h]; exact phase_pre (by omega)
    exact famMet_of_pre i (n + 1) (d + 1) M (by omega) hs

/-- The orbit point that enters `Pre` for the last time was produced by an overflow phase. -/
def Lands : Prop :=
  ∃ k d0 M0 Y0 d M, orbit k = some (d0, M0, Y0) ∧ Overflows d0 M0 Y0 ∧
    phase d0 M0 Y0 = some (d, M, 2 ^ (d + 1) + 1) ∧ d + 2 ≤ M

theorem lands_of_pre : ∀ (n d M Y : Nat), orbit n = some (d, M, Y) → Pre d M Y → Lands
  | 0, d, M, Y, h, hp => by
    simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have : 2 ^ (0 + 1) = 2 := rfl
    exact absurd hp.1 (by omega)
  | n + 1, d, M, Y, h, hp => by
    have hn : (match orbit n with | some (d, M, Y) => phase d M Y | none => none) = some (d, M, Y) := h
    cases ho : orbit n with
    | none => rw [ho] at hn; simp at hn
    | some p =>
      obtain ⟨d0, M0, Y0⟩ := p
      rw [ho] at hn
      by_cases hev : Y0 + 2 ^ (d0 + 1) < 2 ^ M0
      · exact lands_of_pre n d0 M0 Y0 ho (pre_of_event hn hev hp)
      · obtain ⟨rfl, h2⟩ := hp
        exact ⟨n, d0, M0, Y0, d, M, ho, by unfold Overflows; omega, hn, h2⟩

/-- **The machine halts from blank tape iff an overflow phase of the orbit lands on `(d, M, 2^(d+1) + 1)` with
`d + 2 ≤ M`.** -/
theorem halts_iff_lands : HaltsFromBlank ↔ Lands := by
  rw [halts_iff_family]
  constructor
  · rintro ⟨k, m, hk⟩
    exact lands_of_pre k m (m + 2) _ hk ⟨rfl, by omega⟩
  · rintro ⟨k, d0, M0, Y0, d, M, hk, -, hp, hdM⟩
    have hs : orbit (k + 1) = some (d, M, 2 ^ (d + 1) + 1) := by
      show (match orbit k with | some (d, M, Y) => phase d M Y | none => none) = _
      rw [hk]; exact hp
    exact famMet_of_pre (M - d - 2) (k + 1) d M (by omega) hs

end H140108
