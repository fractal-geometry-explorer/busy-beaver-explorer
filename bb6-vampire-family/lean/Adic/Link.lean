import Core.Ctx
import Adic.Basic

/-!
# The 2-adic checker on the proved table

`mkTab e b` is `Core.tbl` as an `Adic.Tab`: context number i is entry i of `Core.tbl` (`ctx i`), and for n mod 4 = r
its entry is the rewrite `Core.look` gives for the parity bit `b r`, with d = e(n mod 2) + 2a, where the variant's
E-pass gives a block of (3n + e(n mod 2))/2 and the rewrite adds a.  `e` and `b` are the variant's (`Adic/V*.lean`).

`halts_of_meets`: given the variant's two facts about its E-pass (`NextOK`, `HaltOK`), if a start configuration
reaches the E-event (ctx i, n) with n ≥ 6 and the abstract orbit of (i, n) meets a halting entry, the start halts.
-/

namespace Adic

open TM

/-- The contexts of the table, numbered. -/
def ctxs : Array (List Bool) := (Core.tbl.map Prod.fst).toArray

def ctx (i : Nat) : List Bool := ctxs.getD i []

/-- The number of a context. -/
def idx (c : List Bool) : Option Nat := ctxs.findIdx? (· == c)

/-- The entry of context i for n mod 4 = r. -/
def mkRes (e : Nat → Nat) (b : Nat → Bool) (i r : Nat) : Res :=
  match Core.look (ctx i) with
  | none => .out
  | some x =>
    match (if b r then x.2 else x.1) with
    | none => .halt
    | some y =>
      match idx y.1 with
      | none => .out
      | some j => if ctx j = y.1 then .go j (e (r % 2) + 2 * y.2) else .out

def mkTab (e : Nat → Nat) (b : Nat → Bool) : Tab :=
  Array.ofFn (n := 4 * ctxs.size) fun k => mkRes e b (k.1 / 4) (k.1 % 4)

theorem get_mkTab (e : Nat → Nat) (b : Nat → Bool) (i r : Nat) (hr : r < 4) :
    get (mkTab e b) i r = if 4 * i + r < 4 * ctxs.size then mkRes e b i r else .out := by
  unfold get mkTab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : 4 * i + r < 4 * ctxs.size
  · simp only [h, ↓reduceDIte, ↓reduceIte]
    simp only [Option.getD_some]
    congr 1 <;> omega
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl

section
variable (f0 : Bool × Dir × Core.St) (e : Nat → Nat) (b : Nat → Bool)

/-- The variant's E-pass and rewrite, in the form the table uses. -/
def NextOK : Prop := ∀ (c : List Bool) (n : Nat) x c' a, 6 ≤ n → Core.look c = some x →
  (if b (n % 4) then x.2 else x.1) = some (c', a) →
    ∃ N, Core.Reaches f0 (Core.Ev c n) (Core.Ev c' ((3 * n + (e (n % 4 % 2) + 2 * a)) / 2)) N

def HaltOK : Prop := ∀ (c : List Bool) (n : Nat) x, 6 ≤ n → Core.look c = some x →
  (if b (n % 4) then x.2 else x.1) = none → Halts (Core.trans f0) (Core.Ev c n)

variable {f0 e b}

theorem step_link (hn : NextOK f0 e b) {i n : Nat} {y : Nat × Nat} (h6 : 6 ≤ n)
    (h : step (mkTab e b) (i, n) = some y) :
    (∃ N, Core.Reaches f0 (Core.Ev (ctx i) n) (Core.Ev (ctx y.1) y.2) N) ∧ 6 ≤ y.2 := by
  unfold step at h
  simp only at h
  rw [get_mkTab e b i (n % 4) (Nat.mod_lt _ (by decide))] at h
  split at h
  · next c d hg =>
    split at h
    · next he =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, by simp only; omega⟩
      split at hg
      · unfold mkRes at hg
        split at hg
        · cases hg
        · next x hl =>
          split at hg
          · cases hg
          · next y hp =>
            split at hg
            · cases hg
            · next j hj =>
              split at hg
              · next hc =>
                simp only [Res.go.injEq] at hg
                obtain ⟨rfl, rfl⟩ := hg
                have := hn (ctx i) n x y.1 y.2 h6 hl hp
                rw [hc]; exact this
              · cases hg
      · cases hg
    · cases h
  · cases h

theorem halt_link (hh : HaltOK f0 b) {i n : Nat} (h6 : 6 ≤ n) (h : H (mkTab e b) (i, n)) :
    Halts (Core.trans f0) (Core.Ev (ctx i) n) := by
  unfold H at h
  simp only at h
  rw [get_mkTab e b i (n % 4) (Nat.mod_lt _ (by decide))] at h
  split at h
  · unfold mkRes at h
    split at h
    · cases h
    · next x hl =>
      split at h
      · next hp => exact hh (ctx i) n x h6 hl hp
      · split at h
        · cases h
        · split at h <;> cases h
  · cases h

theorem iter_link (hn : NextOK f0 e b) : ∀ (j i n : Nat) (y : Nat × Nat), 6 ≤ n →
    iter (mkTab e b) j (i, n) = some y →
    (∃ N, Core.Reaches f0 (Core.Ev (ctx i) n) (Core.Ev (ctx y.1) y.2) N) ∧ 6 ≤ y.2 := by
  intro j
  induction j with
  | zero =>
    intro i n y h6 h
    simp only [iter, Option.some.injEq] at h
    subst h
    exact ⟨⟨0, Core.Reaches.refl _⟩, h6⟩
  | succ j ih =>
    intro i n y h6 h
    simp only [iter] at h
    cases hs : step (mkTab e b) (i, n) with
    | none => rw [hs] at h; cases h
    | some z =>
      rw [hs] at h
      obtain ⟨⟨N1, r1⟩, z6⟩ := step_link hn h6 hs
      obtain ⟨⟨N2, r2⟩, y6⟩ := ih z.1 z.2 y z6 h
      exact ⟨⟨N1 + N2, r1.trans' r2⟩, y6⟩

/-- **The link**: a start configuration that reaches the E-event (ctx i, n), n ≥ 6, halts if the abstract orbit of
(i, n) meets a halting entry. -/
theorem halts_of_meets (hn : NextOK f0 e b) (hh : HaltOK f0 b) {c0 : Core.Config} {i n N : Nat}
    (r : Core.Reaches f0 c0 (Core.Ev (ctx i) n) N) (h6 : 6 ≤ n) (m : MeetsHalt (mkTab e b) (i, n)) :
    Halts (Core.trans f0) c0 := by
  obtain ⟨j, y, hy, hH⟩ := m
  obtain ⟨⟨N1, r1⟩, y6⟩ := iter_link hn j i n y h6 hy
  exact Core.halts_of_reaches (r.trans' r1) (halt_link hh y6 hH)

/-- The checker's verdict: `s` segments of `L` passes (leaves of up to `Lf` passes, `f` levels) from
(context i, n), with n = val L ds, meet a halting entry. -/
theorem halts_of_seg (hn : NextOK f0 e b) (hh : HaltOK f0 b) {c0 : Core.Config} {i N : Nat} {ds : List Nat}
    (L Lf f s : Nat) (hL : 1 ≤ L) (r : Core.Reaches f0 c0 (Core.Ev (ctx i) (val L ds)) N) (h6 : 6 ≤ val L ds)
    (h : seg (mkTab e b) L Lf f (3 ^ L) s i ds = true) : Halts (Core.trans f0) c0 :=
  halts_of_meets hn hh r h6 (seg_sound _ L Lf f hL s i ds h)

end

end Adic
