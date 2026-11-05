import Sentinel
import Return

/-!
# The excursion of a = 1 + 2^m u replays the blank orbit, for every a

`Rel Q ys zs` (lists nearest first): `ys` is `zs` plus a multiple of `Q` in every block, and any blocks of `ys`
beyond the length of `zs` (on the far left of the tape) are multiples of `Q`.  So `ys` is at least `zs` block by
block and agrees with it modulo `Q`.

**The pass map loses one bit** (`next_rel`): if `Rel (2Q) ys zs` and the pass from `zs` gives a list, then the pass
from `ys` gives a list too, and `Rel Q` holds between the two.  The parities agree (the difference is even), so the
sweep crosses and stops at the same blocks; a block of `ys` is at least the one of `zs`, so it is not 0 or 1 where
the one of `zs` is not; and every halving halves the difference.  Iterated (`iter_rel`): `Rel (2^t Q)` survives `t`
passes as `Rel Q`.

**The replay** (`replay`): for a = 1 + 2^m u (m ≥ 1, u ≥ 1) the first pass from `[a, 2a+1]` is
`[k, 3k+5, 2k+3]` with k = 2^(m−1) u, which is `Rel (2^(m−1))` to `φ(blank) = [5, 3]` (`lean/Sentinel.lean`).  So
for t ≤ m − 1, if the blank-tape orbit is a list at pass t, the excursion is a list at pass t + 1 and is `Rel` to
`φ` of it.  With the bounds on the blank orbit (`no_one_49153`, kernel; `no_one_3e18`, `native_decide`): for every
such a, with no upper bound, **the first min(m, 49,154) passes of the excursion never halt and never stop at a
block of 1** (`replay_49153`), and min(m, 3·2^60 + 2) passes with the compiler trusted (`replay_3e18`).  This is
the computed congruence of `notes/LAB_NOTES.md` (4 November) as a theorem for every m.
-/

namespace BB6d

/-- `ys` is `zs` plus a multiple of `Q` in every block; extra blocks of `ys` are multiples of `Q`. -/
def Rel (Q : Nat) : List Nat → List Nat → Prop
  | ys, [] => ∀ y ∈ ys, ∃ b, y = Q * b
  | [], _ :: _ => False
  | y :: ys, z :: zs => (∃ b, y = z + Q * b) ∧ Rel Q ys zs

theorem rel_nil (Q : Nat) (ys : List Nat) : Rel Q ys [] ↔ ∀ y ∈ ys, ∃ b, y = Q * b := by
  cases ys <;> simp [Rel]

theorem rel_nil_cons (Q z : Nat) (zs : List Nat) : Rel Q [] (z :: zs) ↔ False := by simp [Rel]

theorem rel_cons (Q y z : Nat) (ys zs : List Nat) :
    Rel Q (y :: ys) (z :: zs) ↔ (∃ b, y = z + Q * b) ∧ Rel Q ys zs := by simp [Rel]

theorem rel_weaken (Q : Nat) : ∀ ys zs, Rel (2 * Q) ys zs → Rel Q ys zs
  | ys, [], h => by
      rw [rel_nil] at h ⊢
      intro y hy
      obtain ⟨b, hb⟩ := h y hy; exact ⟨2 * b, by rw [hb, Nat.mul_comm 2 Q, Nat.mul_assoc]⟩
  | [], _ :: _, h => by rw [rel_nil_cons] at h; exact h.elim
  | y :: ys, z :: zs, h => by
      rw [rel_cons] at h ⊢
      obtain ⟨⟨b, hb⟩, h⟩ := h
      exact ⟨⟨2 * b, by rw [hb, Nat.mul_comm 2 Q, Nat.mul_assoc]⟩, rel_weaken Q ys zs h⟩

/-- Same length, every entry plus a multiple of `Q`: for the recorded `g`s of a sweep. -/
def RelG (Q : Nat) : List Nat → List Nat → Prop
  | [], [] => True
  | g :: gs, h :: hs => (∃ c, g = h + Q * c) ∧ RelG Q gs hs
  | _, _ => False

theorem relg_cons (Q g h : Nat) (gs hs : List Nat) :
    RelG Q (g :: gs) (h :: hs) ↔ (∃ c, g = h + Q * c) ∧ RelG Q gs hs := by simp [RelG]

theorem bump_rel (Q k k' d : Nat) (hk : k = k' + Q * d) : ∀ ys zs, Rel Q ys zs →
    (∃ b, (bump k ys).1 = (bump k' zs).1 + Q * b) ∧ Rel Q (bump k ys).2 (bump k' zs).2
  | [], [], _ => by
      refine ⟨⟨d, by simp [bump, hk]⟩, ?_⟩
      simp only [bump]; rw [rel_cons]; exact ⟨⟨d, hk⟩, by rw [rel_nil]; simp⟩
  | [e], [], h => by
      rw [rel_nil] at h
      obtain ⟨b, hb⟩ := h e (by simp)
      refine ⟨⟨b + d, by simp only [bump]; rw [hb, hk, Nat.mul_add]; omega⟩, ?_⟩
      simp only [bump]; rw [rel_cons]; exact ⟨⟨d, hk⟩, by rw [rel_nil]; simp⟩
  | e :: f :: ms, [], h => by
      rw [rel_nil] at h
      obtain ⟨b, hb⟩ := h e (by simp)
      obtain ⟨c, hc⟩ := h f (by simp)
      refine ⟨⟨b + d, by simp only [bump]; rw [hb, hk, Nat.mul_add]; omega⟩, ?_⟩
      simp only [bump]; rw [rel_cons]
      refine ⟨⟨c + d, by rw [hc, hk, Nat.mul_add]; omega⟩, ?_⟩
      rw [rel_nil]; intro y hy; exact h y (by simp [hy])
  | [], _ :: _, h => by rw [rel_nil_cons] at h; exact h.elim
  | [y], [z], h => by
      rw [rel_cons] at h
      obtain ⟨⟨b, hb⟩, _⟩ := h
      refine ⟨⟨b + d, by simp only [bump]; rw [hb, hk, Nat.mul_add]; omega⟩, ?_⟩
      simp only [bump]; rw [rel_cons]; exact ⟨⟨d, hk⟩, by rw [rel_nil]; simp⟩
  | y :: f :: ms, [z], h => by
      rw [rel_cons, rel_nil] at h
      obtain ⟨⟨b, hb⟩, h⟩ := h
      obtain ⟨c, hc⟩ := h f (by simp)
      refine ⟨⟨b + d, by simp only [bump]; rw [hb, hk, Nat.mul_add]; omega⟩, ?_⟩
      simp only [bump]; rw [rel_cons]
      refine ⟨⟨c + d, by rw [hc, hk, Nat.mul_add]; omega⟩, ?_⟩
      rw [rel_nil]; intro x hx; exact h x (by simp [hx])
  | [_], _ :: _ :: _, h => by rw [rel_cons, rel_nil_cons] at h; exact h.2.elim
  | y :: v :: ys, z :: w :: zs, h => by
      rw [rel_cons, rel_cons] at h
      obtain ⟨⟨b, hb⟩, ⟨⟨c, hc⟩, h⟩⟩ := h
      refine ⟨⟨b + d, by simp only [bump]; rw [hb, hk, Nat.mul_add]; omega⟩, ?_⟩
      simp only [bump]; rw [rel_cons]
      exact ⟨⟨c + d, by rw [hc, hk, Nat.mul_add]; omega⟩, h⟩

theorem zag_rel (Q : Nat) : ∀ (gs hs : List Nat), RelG Q gs hs → ∀ (q r : Nat) (ms ns : List Nat),
    (∃ b, q = r + Q * b) → Rel Q ms ns → Rel Q (zag q ms gs) (zag r ns hs)
  | [], [], _, q, r, ms, ns, hq, h => by simp only [zag]; rw [rel_cons]; exact ⟨hq, h⟩
  | g :: gs, h :: hs, hg, q, r, ms, ns, ⟨b, hb⟩, hm => by
      rw [relg_cons] at hg
      obtain ⟨⟨c, hc⟩, hg⟩ := hg
      simp only [zag]
      apply zag_rel Q gs hs hg g h _ _ ⟨c, hc⟩
      rw [rel_cons]
      exact ⟨⟨b + c, by rw [hb, hc, Nat.mul_add]; omega⟩, hm⟩
  | [], _ :: _, h, _, _, _, _, _, _ => by simp [RelG] at h
  | _ :: _, [], h, _, _, _, _, _, _ => by simp [RelG] at h

theorem sweep_rel (Q : Nat) : ∀ (zs ys gs hs : List Nat) (z' : List Nat), RelG Q gs hs → Rel (2 * Q) ys zs →
    sweep hs zs = .ok z' → ∃ y', sweep gs ys = .ok y' ∧ Rel Q y' z'
  | [], _, _, _, _, _, _, h => by simp [sweep] at h
  | _ :: _, [], _, _, _, _, h, _ => by rw [rel_nil_cons] at h; exact h.elim
  | z :: zs, y :: ys, gs, hs, z', hg, hr, h => by
    rw [rel_cons] at hr
    obtain ⟨⟨b, hb⟩, hr⟩ := hr
    simp only [sweep] at h ⊢
    have hP : y % 2 = z % 2 := by rw [hb, Nat.mul_assoc]; omega
    by_cases he : z % 2 = 0
    · have hz : z ≠ 0 := by intro h0; simp [h0] at h
      have hy : y ≠ 0 := by omega
      simp only [he, hz, ite_true, ite_false] at h
      simp only [hP, he, hy, ite_true, ite_false]
      refine sweep_rel Q zs ys _ _ z' ((relg_cons _ _ _ _ _).2 ⟨⟨b, ?_⟩, hg⟩) hr h
      rw [hb, Nat.mul_assoc]; omega
    · have h1 : z ≠ 1 := by intro h1; simp [h1] at h
      have hy : y ≠ 1 := by rw [hb]; omega
      simp only [he, h1, ite_false] at h
      simp only [hP, he, hy, ite_false]
      refine ⟨_, rfl, ?_⟩
      injection h with h; subst h
      have hk : (y - 1) / 2 = (z - 1) / 2 + Q * b := by rw [hb, Nat.mul_assoc]; omega
      obtain ⟨h1, h2⟩ := bump_rel Q _ _ b hk ys zs (rel_weaken Q ys zs hr)
      exact zag_rel Q gs hs hg _ _ _ _ h1 h2

/-- **One pass loses one bit**: `Rel (2Q)` before, `Rel Q` after, and the pass from `ys` gives a list whenever the
pass from `zs` does. -/
theorem next_rel (Q : Nat) (ys zs z' : List Nat) (hr : Rel (2 * Q) ys zs) (h : next zs = .ok z') :
    ∃ y', next ys = .ok y' ∧ Rel Q y' z' := by
  match zs, ys, hr with
  | [], [], _ =>
    simp only [next] at h; injection h with h; subst h
    refine ⟨_, rfl, ?_⟩
    rw [rel_cons, rel_cons]; exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩, by rw [rel_nil]; simp⟩
  | [], e :: rest, hr =>
    rw [rel_nil] at hr
    obtain ⟨b, hb⟩ := hr e (by simp)
    simp only [next] at h; injection h with h; subst h
    have he : e % 2 = 0 := by rw [hb, Nat.mul_assoc]; omega
    simp only [next, he, ite_true]
    refine ⟨_, rfl, ?_⟩
    have hk : e / 2 + 2 = 2 + Q * b := by rw [hb, Nat.mul_assoc]; omega
    have hrest : Rel (2 * Q) rest [] := by rw [rel_nil]; intro y hy; exact hr y (by simp [hy])
    obtain ⟨h1, h2⟩ := bump_rel Q _ 2 b hk rest [] (rel_weaken Q rest [] hrest)
    rw [rel_cons]; exact ⟨h1, h2⟩
  | _ :: _, [], hr => rw [rel_nil_cons] at hr; exact hr.elim
  | z :: zs, y :: ys, hr =>
    rw [rel_cons] at hr
    obtain ⟨⟨b, hb⟩, hr⟩ := hr
    have hP : y % 2 = z % 2 := by rw [hb, Nat.mul_assoc]; omega
    simp only [next] at h ⊢
    by_cases he : z % 2 = 0
    · simp only [he, ite_true] at h
      simp only [hP, he, ite_true]
      injection h with h; subst h
      refine ⟨_, rfl, ?_⟩
      have hk : y / 2 + 2 = z / 2 + 2 + Q * b := by rw [hb, Nat.mul_assoc]; omega
      obtain ⟨h1, h2⟩ := bump_rel Q _ _ b hk ys zs (rel_weaken Q ys zs hr)
      rw [rel_cons]; exact ⟨h1, h2⟩
    · simp only [he, ite_false] at h
      simp only [hP, he, ite_false]
      refine sweep_rel Q zs ys _ _ z' ((relg_cons _ _ _ _ _).2 ⟨⟨b, ?_⟩, by simp [RelG]⟩) hr h
      rw [hb, Nat.mul_assoc]; omega

/-- `Rel (2^t Q)` survives `t` passes as `Rel Q`. -/
theorem iter_rel : ∀ (t Q : Nat) (ys zs z' : List Nat), Rel (2 ^ t * Q) ys zs → iter t zs = .ok z' →
    ∃ y', iter t ys = .ok y' ∧ Rel Q y' z'
  | 0, Q, ys, zs, z', hr, h => by
    simp only [iter] at h; injection h with h; subst h
    exact ⟨ys, rfl, by simpa using hr⟩
  | t + 1, Q, ys, zs, z', hr, h => by
    simp only [iter] at h ⊢
    cases hz : iter t zs with
    | halt => rw [hz] at h; cases h
    | one => rw [hz] at h; cases h
    | ok w =>
      rw [hz] at h
      have hr' : Rel (2 ^ t * (2 * Q)) ys zs := by
        rw [← Nat.mul_assoc, ← Nat.pow_succ]; exact hr
      obtain ⟨v, hv, hvr⟩ := iter_rel t (2 * Q) ys zs w hr' hz
      rw [hv]
      exact next_rel Q v w z' hvr h

/-- `iter` from the first pass on. -/
theorem iter_succ' (n : Nat) : ∀ zs, iter (n + 1) zs =
    (match next zs with
     | .ok ws => iter n ws
     | e => e) := by
  induction n with
  | zero => intro zs; simp only [iter]; cases next zs <;> rfl
  | succ n ih =>
    intro zs
    rw [iter, ih]
    cases next zs with
    | ok ws => rfl
    | halt => rfl
    | one => rfl

/-- The first pass from `[a, 2a+1]`, a = 1 + 2k with k ≥ 1: `[k, 3k+5, 2k+3]`. -/
theorem first_pass (k : Nat) (hk : 1 ≤ k) :
    next [2 * (1 + 2 * k) + 1, 1 + 2 * k] = .ok [2 * k + 3, 3 * k + 5, k] := by
  have e1 : (2 * (1 + 2 * k) + 1) % 2 = 1 := by omega
  have e2 : (2 * (1 + 2 * k) + 1 + 3) / 2 = 2 * k + 3 := by omega
  have e3 : (1 + 2 * k) % 2 = 1 := by omega
  have e4 : 1 + 2 * k ≠ 1 := by omega
  have e5 : (1 + 2 * k - 1) / 2 = k := by omega
  simp only [next, e1, e2, sweep, e3, e4, e5, bump, zag, Nat.one_ne_zero, ite_false]
  rw [show k + (2 * k + 3) + 2 = 3 * k + 5 by omega]

/-- **The replay**: for a = 1 + 2^m u (m ≥ 1, u ≥ 1) and t ≤ m − 1, if the blank-tape orbit is a list `zs` at pass
t, the excursion from `[a, 2a+1]` is a list at pass t + 1, equal to `φ zs` modulo 2^(m−1−t) and at least it in
every block. -/
theorem replay (m u t : Nat) (hm : 1 ≤ m) (hu : 1 ≤ u) (ht : t + 1 ≤ m) (zs : List Nat)
    (h : orbit t = .ok zs) :
    ∃ ys, iter (t + 1) [2 * (1 + 2 ^ m * u) + 1, 1 + 2 ^ m * u] = .ok ys ∧ Rel (2 ^ (m - 1 - t)) ys (phi zs) := by
  have hm2 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hk : 1 ≤ 2 ^ (m - 1) * u := Nat.mul_le_mul (Nat.one_le_two_pow) hu
  rw [iter_succ', show 1 + 2 ^ m * u = 1 + 2 * (2 ^ (m - 1) * u) by rw [hm2, Nat.mul_assoc],
    first_pass _ hk]
  simp only
  have hs : iter t [3, 5] = .ok (phi zs) := by rw [sentinel_orbit, h]; rfl
  apply iter_rel t _ _ _ _ _ hs
  have hQ : 2 ^ t * 2 ^ (m - 1 - t) = 2 ^ (m - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hQ]
  rw [rel_cons, rel_cons, rel_nil]
  refine ⟨⟨2 * u, ?_⟩, ⟨3 * u, ?_⟩, fun y hy => ?_⟩
  · rw [Nat.mul_left_comm (2 ^ (m - 1)) 2 u]; omega
  · rw [Nat.mul_left_comm (2 ^ (m - 1)) 3 u]; omega
  · simp only [List.mem_singleton] at hy; exact ⟨u, hy⟩

/-- With the kernel bound on the blank orbit (`no_one_49153`): for every a = 1 + 2^m u, with no upper bound on a,
the first min(m, 49154) passes of the excursion from `[a, 2a+1]` are lists: no halt, no stop at a block of 1. -/
theorem replay_49153 (m u t : Nat) (hm : 1 ≤ m) (hu : 1 ≤ u) (ht : t + 1 ≤ m) (hb : t ≤ 49153) :
    ∃ ys, iter (t + 1) [2 * (1 + 2 ^ m * u) + 1, 1 + 2 ^ m * u] = .ok ys := by
  obtain ⟨zs, _, h, _⟩ := no_one_49153 t hb
  obtain ⟨ys, hy, _⟩ := replay m u t hm hu ht zs h
  exact ⟨ys, hy⟩

/-- The same with `no_one_3e18` (`native_decide`): min(m, 3·2^60 + 2) passes. -/
theorem replay_3e18 (m u t : Nat) (hm : 1 ≤ m) (hu : 1 ≤ u) (ht : t + 1 ≤ m) (hb : t ≤ 3 * 2 ^ 60 + 1) :
    ∃ ys, iter (t + 1) [2 * (1 + 2 ^ m * u) + 1, 1 + 2 ^ m * u] = .ok ys := by
  obtain ⟨zs, _, h, _⟩ := no_one_3e18 t hb
  obtain ⟨ys, hy, _⟩ := replay m u t hm hu ht zs h
  exact ⟨ys, hy⟩

end BB6d
