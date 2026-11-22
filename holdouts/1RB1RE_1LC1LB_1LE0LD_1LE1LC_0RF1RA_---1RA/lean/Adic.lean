/-!
# The 3/2 counter, 2-adically: a parity word of length n is one residue class mod 2^n

An epoch of the machine goes from the visit `[6, 4, u^m, L]` to the visit `[6, 4, u^m', L']`. For `m` large the
new stack and counter are

    L' = g L p,    m' = (3m + c L p) / 2,    p = m mod 2,

with `c L p ≡ p (mod 2)` (computed by `py/adversary.py` and `py/adic.py`, checked against the machine; the epoch map
itself is not proved here). Whatever `g` and `c` are, the parities of the counter behave like the binary digits of
a 2-adic integer:

* `word_eq_iff`: two counters give the same first `n` parities from the same stack iff they agree mod `2^n`;
* `word_onto`: every word of `n` parities is the word of some counter;
* `word_class`: so the counters that follow a given word of length `n` from a given stack are exactly one residue
  class mod `2^n`.

Reaching a given depth of the stack, or emptying it (a halt), is decided by the parity word of the epochs up to that
moment. So the counters that do it are a union of residue classes, one class mod `2^|w|` for each word `w` that
does it (taken prefix-free), and the 2-adic (Haar) measure of that set is the probability of the event when fair
coin flips replace the parities. The real counter is one integer, so this decides nothing by itself. It says what
any invariant that excludes the halt must see (the counter mod `2^|w|`, for the shortest halting word `w` from the
current stack) and it makes the coin-flip model of `py/adic.py` an exact statement about 2-adic counters.

Integers and an arbitrary stack type only. Axioms: propext, Classical.choice, Quot.sound (through `omega` and `simp`).
-/

namespace H175628.Adic

/-- The parity of the counter. -/
def par (m : Int) : Bool := m % 2 == 1

theorem par_eq_iff (m m' : Int) : par m = par m' ↔ m % 2 = m' % 2 := by
  unfold par
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h2 : m' % 2 = 0 ∨ m' % 2 = 1 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

/-- 3 is a unit mod `2^n`. -/
theorem dvd_of_dvd_three_mul : ∀ (n : Nat) (e : Int), (2 : Int) ^ n ∣ 3 * e → (2 : Int) ^ n ∣ e
  | 0, e, _ => by simp
  | n + 1, e, ⟨k, hk⟩ => by
    have hk' : 3 * e = 2 * ((2 : Int) ^ n * k) := by rw [hk, Int.pow_succ]; ac_rfl
    generalize hq : (2 : Int) ^ n * k = q at hk'
    obtain ⟨f, rfl⟩ : ∃ f, e = 2 * f := ⟨e / 2, by omega⟩
    have h3 : (2 : Int) ^ n ∣ 3 * f := ⟨k, by omega⟩
    obtain ⟨j, hj⟩ := dvd_of_dvd_three_mul n f h3
    exact ⟨j, by rw [hj, Int.pow_succ]; ac_rfl⟩

/-- 3 has an inverse mod `2^n`. -/
theorem inv_three : ∀ n : Nat, ∃ v : Int, (2 : Int) ^ n ∣ 3 * v - 1
  | 0 => ⟨0, by simp⟩
  | n + 1 => by
    obtain ⟨v, k, hk⟩ := inv_three n
    have h : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h with h | h
    · refine ⟨v, k / 2, ?_⟩
      rw [hk, Int.pow_succ]
      have : k = 2 * (k / 2) := by omega
      conv => lhs; rw [this]
      ac_rfl
    · refine ⟨v + 2 ^ n, (k + 3) / 2, ?_⟩
      have e1 : 3 * (v + 2 ^ n) - 1 = (2 : Int) ^ n * (k + 3) := by
        rw [Int.mul_add, Int.mul_add]; omega
      rw [e1, Int.pow_succ]
      have : k + 3 = 2 * ((k + 3) / 2) := by omega
      conv => lhs; rw [this]
      ac_rfl

theorem step_dvd_iff (n : Nat) (m m' cc : Int) (hc : cc % 2 = m % 2) :
    (2 : Int) ^ (n + 1) ∣ m - m' ↔
      (m % 2 = m' % 2 ∧ (2 : Int) ^ n ∣ (3 * m + cc) / 2 - (3 * m' + cc) / 2) := by
  constructor
  · rintro ⟨k, hk⟩
    have hk' : m - m' = 2 * ((2 : Int) ^ n * k) := by rw [hk, Int.pow_succ]; ac_rfl
    refine ⟨by omega, ⟨3 * k, ?_⟩⟩
    have : (3 * m + cc) / 2 - (3 * m' + cc) / 2 = 3 * ((2 : Int) ^ n * k) := by omega
    rw [this]; ac_rfl
  · rintro ⟨hp, k, hk⟩
    have h3 : 3 * ((m - m') / 2) = (2 : Int) ^ n * k := by omega
    obtain ⟨j, hj⟩ := dvd_of_dvd_three_mul n ((m - m') / 2) ⟨k, h3⟩
    refine ⟨j, ?_⟩
    have : m - m' = 2 * ((m - m') / 2) := by omega
    rw [this, hj, Int.pow_succ]; ac_rfl

section
variable {S : Type} (g : S → Bool → S) (c : S → Bool → Int)

/-- The first `n` parities of the counter from the stack `L` and the counter `m`. -/
def word : Nat → S → Int → List Bool
  | 0, _, _ => []
  | n + 1, L, m => par m :: word n (g L (par m)) ((3 * m + c L (par m)) / 2)

variable (hc : ∀ L p, c L p % 2 = if p then 1 else 0)
include hc

theorem c_mod (L : S) (m : Int) : c L (par m) % 2 = m % 2 := by
  rw [hc]; unfold par
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h1 with h1 | h1 <;> simp [h1]

/-- Two counters give the same first `n` parities from the same stack iff they agree mod `2^n`. -/
theorem word_eq_iff : ∀ (n : Nat) (L : S) (m m' : Int),
    word g c n L m = word g c n L m' ↔ (2 : Int) ^ n ∣ m - m'
  | 0, L, m, m' => by simp [word]
  | n + 1, L, m, m' => by
    simp only [word, List.cons.injEq]
    rw [step_dvd_iff n m m' (c L (par m)) (c_mod c hc L m), ← par_eq_iff]
    by_cases hp : par m = par m'
    · rw [← hp, word_eq_iff n _ _ _]
    · simp [hp]

/-- Every word of parities is the word of some counter. -/
theorem word_onto : ∀ (w : List Bool) (L : S), ∃ m, word g c w.length L m = w
  | [], L => ⟨0, rfl⟩
  | b :: w, L => by
    obtain ⟨m1, hm1⟩ := word_onto w (g L b)
    obtain ⟨v, k, hk⟩ := inv_three (w.length + 1)
    have hcb := hc L b
    refine ⟨v * (2 * m1 - c L b), ?_⟩
    have key : 3 * (v * (2 * m1 - c L b)) - (2 * m1 - c L b)
        = (2 : Int) ^ (w.length + 1) * (k * (2 * m1 - c L b)) := by
      rw [← Int.mul_assoc, ← Int.mul_assoc, ← hk, Int.sub_mul, Int.one_mul]
    generalize v * (2 * m1 - c L b) = m at key
    have key2 : 3 * m - (2 * m1 - c L b) = 2 * ((2 : Int) ^ w.length * (k * (2 * m1 - c L b))) := by
      rw [key, Int.pow_succ]; ac_rfl
    have hp : par m = b := by
      unfold par; cases b <;> simp at hcb <;> simp <;> omega
    simp only [List.length_cons, word, hp, List.cons.injEq, true_and]
    have e := (word_eq_iff g c hc w.length (g L b) ((3 * m + c L b) / 2) m1).2
      ⟨k * (2 * m1 - c L b), by omega⟩
    rw [e, hm1]

/-- **The counters that follow a parity word of length `n` from a stack are exactly one residue class mod `2^n`.**
For every stack `L` and word `w` there is an `r` such that, for every counter `m`, the first `|w|` parities from
`(L, m)` are `w` iff `m ≡ r (mod 2^|w|)`. -/
theorem word_class (w : List Bool) (L : S) :
    ∃ r : Int, ∀ m : Int, word g c w.length L m = w ↔ (2 : Int) ^ w.length ∣ m - r := by
  obtain ⟨r, hr⟩ := word_onto g c hc w L
  exact ⟨r, fun m => by rw [← word_eq_iff g c hc, hr]⟩

end
end H175628.Adic

