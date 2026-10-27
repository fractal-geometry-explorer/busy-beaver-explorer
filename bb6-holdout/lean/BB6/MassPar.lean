import BB6.CleanEntryTree

/-!
# The measures of a clean-tape tree, evaluated in parallel

`exploreMassWE` (`BB6/CleanEntryTree.lean`) computes the measures and leaf counts of the clean-tape tree with entry
leaves without building it; the mass theorems evaluate it with `native_decide`, on one core.  This file cuts the same
computation at a split level `e`: `massPrefix` follows the exploration through its first `e` splits and returns the
tally of the leaves it meets on the way and the nodes it reaches after `e` splits, and `massPrefix_eq` proves that the
whole tally is that tally plus the tallies of `exploreMassWE` from those nodes with the splits that are left.
`massPar` computes the nodes' tallies as tasks (`Task.spawn`), which native code runs in parallel; logically
`(Task.spawn f).get = f ()`, so `massPar_eq` is `massPrefix_eq`.  Nothing here changes what is computed, only how
many cores compute it.
-/

namespace BB6.Sym
open BB6

/-- The arguments of `exploreMassWE` at a node, all but the number of splits left. -/
structure MNode where
  S : Nat
  nd : Nat
  D : Nat
  moved : Bool
  ss : List SMark
  sW : YForm
  w0 : YForm
  ts : List YForm

def ETally.zero : ETally := ⟨0, 0, 0, 0, 0⟩

theorem ETally.zero_add (a : ETally) : ETally.zero.add a = a := by
  cases a; simp [ETally.zero, ETally.add]

theorem ETally.add_zero (a : ETally) : a.add ETally.zero = a := by
  cases a; simp [ETally.zero, ETally.add]

theorem ETally.add_assoc (a b c : ETally) : (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c; simp only [ETally.add, ETally.mk.injEq]; omega

theorem ETally.add_comm (a b : ETally) : a.add b = b.add a := by
  cases a; cases b; simp only [ETally.add, ETally.mk.injEq]; omega

/-- The sum of a list of tallies. -/
def ETally.sum (l : List ETally) : ETally := l.foldr ETally.add ETally.zero

theorem ETally.sum_append (l₁ l₂ : List ETally) : ETally.sum (l₁ ++ l₂) = (ETally.sum l₁).add (ETally.sum l₂) := by
  induction l₁ with
  | nil => simp [ETally.sum, ETally.zero_add]
  | cons a l ih =>
    simp only [ETally.sum, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, ETally.add_assoc]

variable (Γ : Int) (fuel : Nat) (chk : List YForm → List SMark → YForm → YForm → Bool) (B : Nat)

/-- The tally of a node, explored with `d` splits left. -/
def MNode.mass (d : Nat) (n : MNode) : ETally :=
  exploreMassWE Γ fuel chk B n.S d n.nd n.D n.moved n.ss n.sW n.w0 n.ts

/-- `exploreMassWE` through its first `e` splits: the tally of the leaves met before the `e`-th split level, and the
nodes reached there. -/
def massPrefix : Nat → Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → ETally × List MNode
  | S, 0, nd, D, moved, ss, sW, w0, ts => (ETally.zero, [⟨S, nd, D, moved, ss, sW, w0, ts⟩])
  | 0, _ + 1, _, D, _, _, _, _, _ => (⟨2 ^ D, 1, 0, 0, 0⟩, [])
  | S + 1, e + 1, nd, D, moved, ss, sW, w0, ts =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then (⟨0, 0, 1, 0, 0⟩, []) else
    if chk ts ss sW w0 = true then (⟨0, 0, 0, 1, 2 ^ D⟩, []) else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => massPrefix S (e + 1) nd D true ss' sW' w0 ts
    | some _ => (⟨2 ^ D, 1, 0, 0, 0⟩, [])
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            massPrefix S (e + 1) nd D moved ss sW w0 [dropCone Γ z]
          else (⟨2 ^ D, 1, 0, 0, 0⟩, [])
        | _, _ => (⟨2 ^ D, 1, 0, 0, 0⟩, [])
      | some (none, i) =>
        if i < 2 then
          let a := massPrefix S e B (D - 1) moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0)
          let b := massPrefix S e B (D - 1) moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1)
          (a.1.add b.1, a.2 ++ b.2)
        else (⟨2 ^ D, 1, 0, 0, 0⟩, [])
      | some (some (j, s), i) =>
        if i < 2 then
          let a := massPrefix S e B (D - 1) moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
            ((w0.shear j s).subst i 0) (substT (shearT ts j s) i 0)
          let b := massPrefix S e B (D - 1) moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
            ((w0.shear j s).subst i 1) (substT (shearT ts j s) i 1)
          (a.1.add b.1, a.2 ++ b.2)
        else (⟨2 ^ D, 1, 0, 0, 0⟩, [])

/-- **The tally is the prefix's tally plus the tallies of the nodes after `e` splits.** -/
theorem massPrefix_eq : ∀ (S e d nd D : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    exploreMassWE Γ fuel chk B S (e + d) nd D moved ss sW w0 ts =
      (massPrefix Γ fuel chk B S e nd D moved ss sW w0 ts).1.add
        (ETally.sum ((massPrefix Γ fuel chk B S e nd D moved ss sW w0 ts).2.map (MNode.mass Γ fuel chk B d))) := by
  intro S
  induction S with
  | zero =>
    intro e d nd D moved ss sW w0 ts
    cases e with
    | zero => simp [massPrefix, ETally.sum, MNode.mass, ETally.zero_add, ETally.add_zero]
    | succ e => simp [massPrefix, exploreMassWE, ETally.sum, ETally.add_zero]
  | succ S ih =>
    intro e d nd D moved ss sW w0 ts
    cases e with
    | zero => simp [massPrefix, ETally.sum, MNode.mass, ETally.zero_add, ETally.add_zero]
    | succ e =>
      have he : e + 1 + d = (e + d) + 1 := by omega
      rw [he]
      have ih' : ∀ nd moved ss sW w0 ts, exploreMassWE Γ fuel chk B S (e + d + 1) nd D moved ss sW w0 ts =
          (massPrefix Γ fuel chk B S (e + 1) nd D moved ss sW w0 ts).1.add
            (ETally.sum ((massPrefix Γ fuel chk B S (e + 1) nd D moved ss sW w0 ts).2.map
              (MNode.mass Γ fuel chk B d))) := by
        intro nd moved ss sW w0 ts
        rw [← ih (e + 1) d nd D moved ss sW w0 ts, show e + 1 + d = e + d + 1 by omega]
      -- the two children of a split, added
      have hsplit : ∀ (a b : ETally × List MNode) (x y : ETally),
          x = a.1.add (ETally.sum (a.2.map (MNode.mass Γ fuel chk B d))) →
          y = b.1.add (ETally.sum (b.2.map (MNode.mass Γ fuel chk B d))) →
          x.add y = (a.1.add b.1).add (ETally.sum ((a.2 ++ b.2).map (MNode.mass Γ fuel chk B d))) := by
        intro a b x y hx hy
        rw [hx, hy, List.map_append, ETally.sum_append]
        generalize ETally.sum (a.2.map (MNode.mass Γ fuel chk B d)) = u
        generalize ETally.sum (b.2.map (MNode.mass Γ fuel chk B d)) = v
        rw [ETally.add_assoc, ETally.add_assoc]
        congr 1
        rw [← ETally.add_assoc, ← ETally.add_assoc, ETally.add_comm u]
      have hleaf : ∀ t : ETally, t = t.add (ETally.sum (([] : List MNode).map (MNode.mass Γ fuel chk B d))) := by
        intro t; simp [ETally.sum, ETally.add_zero]
      simp only [exploreMassWE, massPrefix]
      by_cases h1 : (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true
      · simp only [h1, ite_true]; exact hleaf _
      · simp only [h1, ite_false, Bool.false_eq_true]
        by_cases h2 : chk ts ss sW w0 = true
        · simp only [h2, ite_true]; exact hleaf _
        · simp only [h2, ite_false, Bool.false_eq_true]
          cases hr : symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
          | some r =>
            cases r with
            | newRound ss' sW' => exact ih' nd true ss' sW' w0 ts
            | gap _ _ _ _ => exact hleaf _
            | halt => exact hleaf _
            | uncovered => exact hleaf _
          | none =>
            cases hs : splitStep ts Γ ss sW with
            | none =>
              cases nd with
              | zero => exact hleaf _
              | succ nd =>
                cases hc : coneMin ts Γ with
                | none => exact hleaf _
                | some z =>
                  by_cases hd : dropOK Γ fuel z ss sW w0 ts = true
                  · simp only [hd, ite_true]; exact ih' nd moved ss sW w0 [dropCone Γ z]
                  · simp only [hd, ite_false, Bool.false_eq_true]; exact hleaf _
            | some p =>
              obtain ⟨o, i⟩ := p
              cases o with
              | none =>
                by_cases hi : i < 2
                · simp only [hi, ite_true]
                  exact hsplit _ _ _ _ (ih e d _ _ _ _ _ _ _) (ih e d _ _ _ _ _ _ _)
                · simp only [hi, ite_false]; exact hleaf _
              | some js =>
                obtain ⟨j, s⟩ := js
                by_cases hi : i < 2
                · simp only [hi, ite_true]
                  exact hsplit _ _ _ _ (ih e d _ _ _ _ _ _ _) (ih e d _ _ _ _ _ _ _)
                · simp only [hi, ite_false]; exact hleaf _

/-- `exploreMassWE` with its nodes after `e` splits computed as parallel tasks. -/
def massPar (S e d nd D : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm) : ETally :=
  let p := massPrefix Γ fuel chk B S e nd D moved ss sW w0 ts
  let tasks := p.2.map (fun n => Task.spawn fun _ => MNode.mass Γ fuel chk B d n)
  p.1.add (ETally.sum (tasks.map Task.get))

theorem massPar_eq (S e d nd D : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm) :
    massPar Γ fuel chk B S e d nd D moved ss sW w0 ts =
      exploreMassWE Γ fuel chk B S (e + d) nd D moved ss sW w0 ts := by
  rw [massPrefix_eq]
  simp only [massPar, List.map_map]
  rfl

end BB6.Sym
