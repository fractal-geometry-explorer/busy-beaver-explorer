import Descent

/-!
# The factory behind an eater, and where law A comes from

Below an eater sits a *factory*: the word

    (10) [rung]^n 4 0^6 (10) 4 0^4 3 [100]^M 3 4 0^3 4 3 4 0^3 (10) X

(and the ten other states of its 11-hit cycle), where `rung = 40001010431040300010`.  The engine
(`py/lsa_factory.py` in the twin's folder) runs the recursion with symbolic counts n and M from each of the
11 states and finds the same rule from all of them, for every n ≥ 1 and M ≥ 7:

    11 hits:  n ↦ n + 1,  M ↦ M − 6,  and 2 hits are passed on to the rest X.

So the factory writes one rung of the next fuel for every 11 hits, burns 6 units of its `[100]` fuel, and
passes 2 hits further down.  This file takes that rule as a hypothesis (`Rule`) and proves what follows
from it for every count:

* `iter`: after `11 q` more hits, q more rungs, `6 q` less fuel, `2 q` more hits passed down;
* `rungs_bounds`: after t hits the rung count is t / 11 up to the start, `t + 11 lo ≤ 11 n t + 10`
  and `11 n t ≤ t + 11 hi`;
* `lawA_of_factory`: an eater phase of k super-cycles passes about 21 k hits down; if they all reach the
  factory, the fuel it writes satisfies law A (`Descent.LawA`).  The offset e of law A is the factory's
  phase in its cycle, the rungs it held at the start, and the few hits of the phase's ends.
-/

namespace Factory

/-- A factory under a stream of hits: after t hits it holds `n t` rungs and `M t` units of fuel, and it has
passed `d t` hits on to the rest. -/
structure Run where
  n : Nat → Nat
  M : Nat → Nat
  d : Nat → Nat

/-- The factory rule for the first T hits (the fuel M lasts that long). -/
def Rule (f : Run) (T : Nat) : Prop :=
  ∀ t, t + 11 ≤ T → f.n (t + 11) = f.n t + 1 ∧ f.M (t + 11) + 6 = f.M t ∧ f.d (t + 11) = f.d t + 2

theorem iter (f : Run) (T : Nat) (h : Rule f T) (t : Nat) :
    ∀ q, 11 * q + t ≤ T →
      f.n (11 * q + t) = f.n t + q ∧ f.M (11 * q + t) + 6 * q = f.M t ∧ f.d (11 * q + t) = f.d t + 2 * q := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    have e : 11 * (q + 1) + t = (11 * q + t) + 11 := by omega
    have ⟨h1, h2, h3⟩ := ih (by omega)
    have ⟨g1, g2, g3⟩ := h (11 * q + t) (by omega)
    rw [e]
    omega

/-- The rung count after t hits, from its values in the first cycle. -/
theorem rungs_bounds (f : Run) (T lo hi : Nat) (h : Rule f T)
    (hb : ∀ j, j < 11 → lo ≤ f.n j ∧ f.n j ≤ hi) (t : Nat) (ht : t ≤ T) :
    t + 11 * lo ≤ 11 * f.n t + 10 ∧ 11 * f.n t ≤ t + 11 * hi := by
  have hdm : 11 * (t / 11) + t % 11 = t := Nat.div_add_mod t 11
  have hm : t % 11 < 11 := Nat.mod_lt t (by omega)
  have ⟨h1, _, _⟩ := iter f T h (t % 11) (t / 11) (by omega)
  have ⟨b1, b2⟩ := hb (t % 11) hm
  rw [hdm] at h1
  omega

/-- The fuel burnt and the hits passed down after t hits. -/
theorem fuel_and_down (f : Run) (T : Nat) (h : Rule f T) (t : Nat) (ht : t ≤ T) :
    f.M t + 6 * (t / 11) = f.M (t % 11) ∧ f.d t = f.d (t % 11) + 2 * (t / 11) := by
  have hdm : 11 * (t / 11) + t % 11 = t := Nat.div_add_mod t 11
  have ⟨_, h2, h3⟩ := iter f T h (t % 11) (t / 11) (by omega)
  rw [hdm] at h2 h3
  exact ⟨h2, h3⟩

/-- **Law A from the factory.**  A phase of k super-cycles (`4 k ≤ F ≤ 4 k + m`) passes H hits down, between
`21 k − s0` and `21 k + s1`; they all go to a factory that held between lo and hi rungs during its first cycle.
Then the fuel `f.n H` it has written obeys law A with offsets `10 + s0` below and `s1 + 11 hi` above. -/
theorem lawA_of_factory (f : Run) (T m lo hi s0 s1 F k H : Nat) (h : Rule f T)
    (hb : ∀ j, j < 11 → lo ≤ f.n j ∧ f.n j ≤ hi) (hHT : H ≤ T)
    (hk1 : 4 * k ≤ F) (hk2 : F ≤ 4 * k + m) (hH0 : 21 * k ≤ H + s0) (hH1 : H ≤ 21 * k + s1) :
    Descent.LawA m (10 + s0) (s1 + 11 * hi) F (f.n H) := by
  have ⟨r1, r2⟩ := rungs_bounds f T lo hi h hb H hHT
  exact ⟨k, hk1, hk2, by omega, by omega⟩

/-- A fresh factory (no rungs yet in its first cycle, so lo = 0 and hi = 1) fed exactly 21 k hits writes a fuel
with `21 k − 10 ≤ 11 F' ≤ 21 k + 11`. -/
example (f : Run) (T F k : Nat) (h : Rule f T) (hb : ∀ j, j < 11 → 0 ≤ f.n j ∧ f.n j ≤ 1)
    (hT : 21 * k ≤ T) (hk1 : 4 * k ≤ F) (hk2 : F ≤ 4 * k + 9) :
    Descent.LawA 9 10 11 F (f.n (21 * k)) := by
  have := lawA_of_factory f T 9 0 1 0 0 F k (21 * k) h hb hT hk1 hk2 (by omega) (by omega)
  simpa using this

end Factory
