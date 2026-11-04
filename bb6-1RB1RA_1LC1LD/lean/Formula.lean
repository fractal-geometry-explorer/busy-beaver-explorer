import Recur
import Blocks

/-!
# The last block after a recursive pass: `2j + c`

A recursive pass starts at `K ls (3j - 1)`: blocks `ls` to the left (nearest first, the nearest is `x`), and a last
block `3j`.  `k_start` turns the last block into the words `0`, `0 1` and `j` words `0 1 1` (`twos j`), and the block
machine of `Recur.lean` takes over.  Three facts, all kernel only:

* **The trailing words `0 1 1` are a loop** (`tail_two`, `tail_iter`, `tail_end`): from `A` before a block `a` and `m`
  words `0 1 1`, every two words add 4 to `a` and 2 to the block left of it, and the pass ends with last block `a + 2m`.
* **What happens before is the same for every `j`** (`astep_app`, `pre`, `pre_sound`): the block machine only reads the
  words in front of it, so it can be run once on `0, 0 1` with the words `0 1 1` taken from an unbounded supply as they
  are needed (`pre`).  When it stops, at `A` with only words `0 1 1` ahead, it returns the blocks `a :: b :: M` to the
  left, the number `p` of words `0 1 1` still in front, and the number `u` it took from the supply.
* **The formula** (`recur_sound`): if `pre` stops for `ls`, then for every `j ≥ u` the recursive pass from `K ls (3j - 1)`
  reaches the pass start with last block `2j + c` where `c = a + 2p - 2u`, which depends only on `ls`.

`recur_two`: for `x = 2` this is closed form for every list to the left and every `j`: `c = -1`, so a last block `3j`
after a block 2 becomes `2j - 1`, which halts for `j = 1` (`recur_two_three`) and keeps the pass start good for `j ≥ 2`
(`recur_two_good`).  For other `x`, `c ≥ 0` is checked by the kernel on every list of one to three blocks from 2 to 10,
for every `j` (`recur_small`); in general it is not proved.
-/

namespace BB6c

open TM

/-- `m` words `0 1 1`. -/
abbrev twos (m : Nat) : List Nat := List.replicate m 2

theorem tw_two (j : Nat) : tw 2 j 0 = twos (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => show 2 :: tw 2 j 0 = _; rw [ih]; rfl

/-! ## The loop over the words `0 1 1` -/

/-- Two words `0 1 1`: the block before the head gains 4, the one left of it 2. -/
theorem tail_two (a b : Nat) (M W : List Nat) :
    Reaches (enc ⟨.A, 0, a :: b :: M, 2 :: 2 :: W⟩) (enc ⟨.A, 0, (a + 4) :: (b + 2) :: M, W⟩) := by
  have h₁ := s_a_tok 1 (a :: b :: M) (2 :: W)
  have h₂ := s_b_one 0 0 2 (a :: b :: M) W
  have h₃ := s_b_zero a 0 (b :: M) (tw 1 0 2 ++ W)
  have h₄ := s_c_move 3 (b :: M) W a
  have h₅ := s_c_one b M ((3 + a) :: W)
  have h₆ := s_f_tok (3 + a) 0 ((b + 2) :: M) W
  rw [show 0 + (3 + a) + 1 = a + 4 by omega] at h₆
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))

theorem tail_iter (M W : List Nat) : ∀ (i a b : Nat),
    Reaches (enc ⟨.A, 0, a :: b :: M, twos (2 * i) ++ W⟩) (enc ⟨.A, 0, (a + 4 * i) :: (b + 2 * i) :: M, W⟩)
  | 0, a, b => ⟨0, rfl⟩
  | i + 1, a, b => by
    have h := (tail_two a b M (twos (2 * i) ++ W)).trans (tail_iter M W i (a + 4) (b + 2))
    rw [show a + 4 + 4 * i = a + 4 * (i + 1) by omega, show b + 2 + 2 * i = b + 2 * (i + 1) by omega] at h
    have e : twos (2 * (i + 1)) ++ W = 2 :: 2 :: (twos (2 * i) ++ W) := by
      simp [twos, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.replicate_succ]
    rw [e]; exact h

/-- **The end of a recursive pass**: from `A` before a block `a` and `m` words `0 1 1`, the next pass start has last
block `a + 2m`, and the block left of it gains `2 ⌈m/2⌉`. -/
theorem tail_end (a b : Nat) (M : List Nat) (m : Nat) (h : 1 ≤ a + 2 * m) :
    Reaches (enc ⟨.A, 0, a :: b :: M, twos m⟩) (K ((b + 2 * ((m + 1) / 2)) :: M) (a + 2 * m - 1)) := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, m = 2 * i ∨ m = 2 * i + 1 := ⟨m / 2, by omega⟩
  · have h₁ := tail_iter M [] i a b
    have h₂ := s_a_end (a + 4 * i - 1) ((b + 2 * i) :: M)
    rw [show a + 4 * i - 1 + 1 = a + 4 * i by omega] at h₂
    rw [List.append_nil] at h₁
    rw [show (2 * i + 1) / 2 = i by omega, show a + 2 * (2 * i) - 1 = a + 4 * i - 1 by omega]
    exact h₁.trans h₂
  · have h₁ := tail_iter M [2] i a b
    have h₂ := s_a_tok 1 ((a + 4 * i) :: (b + 2 * i) :: M) []
    have h₃ := s_b_end (b + 2 * i) (a + 4 * i) M
    rw [show (2 * i + 1 + 1) / 2 = i + 1 by omega, show a + 2 * (2 * i + 1) - 1 = a + 4 * i + 1 by omega,
      show b + 2 * (i + 1) = b + 2 * i + 2 by omega, show twos (2 * i + 1) = twos (2 * i) ++ [2] from
        List.replicate_succ' ..]
    exact h₁.trans (h₂.trans h₃)

/-! ## The block machine does not look past the words in front of it -/

def appW (S : List Nat) : Out → Out
  | .go c => .go ⟨c.q, c.h, c.L, c.W ++ S⟩
  | o => o

def withW (c : ACfg) (S : List Nat) : ACfg := ⟨c.q, c.h, c.L, c.W ++ S⟩

theorem bstep_app0 (n c d : Nat) (M : List Nat) (k : Nat) (W S : List Nat) :
    bstep n c d M k (W ++ S) = (bstep n c d M k W).map (appW S) := by
  unfold bstep
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    simp [appW, List.append_assoc]

theorem bstep_app (n c d : Nat) (M : List Nat) (k w : Nat) (W S : List Nat) :
    bstep n c d M k (w :: (W ++ S)) = (bstep n c d M k (w :: W)).map (appW S) :=
  bstep_app0 n c d M k (w :: W) S

theorem bstep_cons (n c d : Nat) (M : List Nat) (k s : Nat) (S : List Nat) :
    bstep n c d M k (s :: S) = (bstep n c d M k []).map (appW (s :: S)) :=
  bstep_app0 n c d M k [] (s :: S)

set_option maxHeartbeats 0 in
theorem astep'_app2 (q : St) (h : Nat) (L : List Nat) (w₀ w₁ : Nat) (W S : List Nat) :
    astep' q h L (w₀ :: w₁ :: (W ++ S)) = (astep' q h L (w₀ :: w₁ :: W)).map (appW S) := by
  rcases q with _ | _ | _ | _ | _ | _ <;> rcases h with _ | _ | h <;>
  rcases L with _ | ⟨_ | _ | a, _ | ⟨_ | b, _ | ⟨d, M⟩⟩⟩ <;> rcases w₀ with _ | _ | _ | w₀ <;>
  first | rfl | simp [astep', bstep_app]

set_option maxHeartbeats 0 in
/-- With a single word in front, only `C` before a word `0 1` looks at the next word. -/
theorem astep'_app1 (q : St) (h : Nat) (L : List Nat) (w₀ : Nat) (S : List Nat) (hc : q ≠ .C ∨ w₀ ≠ 1) :
    astep' q h L (w₀ :: S) = (astep' q h L [w₀]).map (appW S) := by
  rcases S with _ | ⟨s, S⟩
  · cases astep' q h L [w₀] with
    | none => rfl
    | some o => cases o <;> simp [appW]
  rcases q with _ | _ | _ | _ | _ | _ <;> rcases h with _ | _ | h <;>
  rcases L with _ | ⟨_ | _ | a, _ | ⟨_ | b, _ | ⟨d, M⟩⟩⟩ <;> rcases w₀ with _ | _ | _ | w₀ <;>
  first | rfl | simp_all [astep', bstep_cons]

/-- One step of the block machine is the same whatever follows the words in front of the head, as long as there is
one (and two in front of `C` before a word `0 1`). -/
theorem astep_app {c : ACfg} (hne : c.W ≠ []) (hc : ¬(c.q = .C ∧ c.W = [1])) (S : List Nat) :
    astep (withW c S) = (astep c).map (appW S) := by
  obtain ⟨q, h, L, W⟩ := c
  rcases W with _ | ⟨w₀, _ | ⟨w₁, W⟩⟩
  · exact absurd rfl hne
  · refine astep'_app1 q h (pad 4 L) w₀ S ?_
    by_cases hq : q = .C
    · exact .inr fun h1 => hc ⟨hq, by rw [h1]⟩
    · exact .inl hq
  · exact astep'_app2 q h (pad 4 L) w₀ w₁ W S

/-! ## Before the loop: once for every `j` -/

def allTwo : List Nat → Bool
  | [] => true
  | k :: W => k == 2 && allTwo W

theorem allTwo_eq : ∀ {W : List Nat}, allTwo W = true → W = twos W.length
  | [], _ => rfl
  | k :: W, h => by
    simp only [allTwo, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1]
    show 2 :: W = 2 :: twos W.length
    exact congrArg _ (allTwo_eq h.2)

/-- The block machine for at most `f` steps, with words `0 1 1` taken (`u` counts them) from an unbounded supply after
the words `c.W` when they are needed; it stops at `A` with nothing but words `0 1 1` ahead and returns the blocks to the
left (two of them explicit), the number of words `0 1 1` in front, and `u`. -/
def pre : Nat → ACfg → Nat → Option (List Nat × Nat × Nat)
  | 0, _, _ => none
  | f + 1, c, u =>
    if c.q = .A ∧ c.h = 0 ∧ allTwo c.W = true then some (pad 2 c.L, c.W.length, u)
    else if c.W = [] ∨ (c.q = .C ∧ c.W = [1]) then pre f ⟨c.q, c.h, c.L, c.W ++ [2]⟩ (u + 1)
    else match astep c with
      | some (.go c') => pre f c' u
      | _ => none

theorem twos_succ (W : List Nat) (n : Nat) : W ++ twos (n + 1) = (W ++ [2]) ++ twos n := by
  simp [List.replicate_succ, List.append_assoc]

/-- **`pre` is sound for every supply**: `v` words taken, then any `m` more, give the same run. -/
theorem pre_sound : ∀ (f : Nat) {c : ACfg} {u : Nat} {L : List Nat} {p u' : Nat}, pre f c u = some (L, p, u') →
    ∃ v, u' = u + v ∧ ∀ m, Reaches (enc (withW c (twos (v + m)))) (enc ⟨.A, 0, L, twos (p + m)⟩) := by
  intro f
  induction f with
  | zero => intro c u L p u' e; cases e
  | succ f ih =>
    intro c u L p u' e
    unfold pre at e
    split at e
    · rename_i hs
      cases e
      refine ⟨0, rfl, fun m => ⟨0, ?_⟩⟩
      obtain ⟨q, h, L₀, W⟩ := c
      obtain ⟨rfl, rfl, h2⟩ := hs
      have hW := allTwo_eq h2
      show some (enc ⟨.A, 0, L₀, W ++ twos (0 + m)⟩) = some (enc ⟨.A, 0, pad 2 L₀, twos (W.length + m)⟩)
      have e : W ++ twos m = twos (W.length + m) := by
        dsimp only at hW
        calc W ++ twos m = twos W.length ++ twos m := by rw [← hW]
          _ = twos (W.length + m) := List.replicate_append_replicate ..
      rw [Nat.zero_add, e]
      unfold enc; rw [lt_pad]
    split at e
    · obtain ⟨v, rfl, hv⟩ := ih e
      refine ⟨v + 1, by omega, fun m => ?_⟩
      have := hv m
      unfold withW at this ⊢
      rw [show v + 1 + m = (v + m) + 1 by omega, twos_succ]
      exact this
    · rename_i hs1 hs2
      split at e
      · rename_i c' hc'
        obtain ⟨v, rfl, hv⟩ := ih e
        refine ⟨v, rfl, fun m => ?_⟩
        have hne : c.W ≠ [] := fun h => hs2 (.inl h)
        have hcc : ¬(c.q = .C ∧ c.W = [1]) := fun h => hs2 (.inr h)
        have ha := astep_app hne hcc (twos (v + m))
        rw [hc'] at ha
        exact Reaches.trans (astep_sound ha : Reaches _ (enc (withW c' (twos (v + m))))) (hv m)
      · cases e

/-! ## The formula -/

/-- **The last block after a recursive pass** (kernel only).  If `pre` stops for the blocks `ls` with `a :: b :: M`,
`p` and `u`, then for every `j ≥ max 1 u` the pass from `K ls (3j - 1)` (last block `3j`) reaches the pass start with the
blocks `b + 2⌈(p + j - u)/2⌉, M` and last block `a + 2(p + j - u) = 2j + c`, `c = a + 2p - 2u`, the same `c` for
every `j`. -/
theorem recur_sound {f : Nat} {ls M : List Nat} {a b p u : Nat}
    (e : pre f ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 = some (a :: b :: M, p, u)) (j : Nat) (hj1 : 1 ≤ j) (hj : u ≤ j)
    (hpos : 1 ≤ a + 2 * (p + (j - u))) :
    Reaches (K ls (3 * j - 1)) (K ((b + 2 * ((p + (j - u) + 1) / 2)) :: M) (a + 2 * (p + (j - u)) - 1)) := by
  obtain ⟨v, hv, hr⟩ := pre_sound f e
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h₀ := s_k_start (ls.headD 0) i ls.tail
  rw [tw_two, show i + 1 = v + (i + 1 - u) by omega] at h₀
  rw [show 3 * (i + 1) - 1 = 3 * i + 2 by omega, K_pad1]
  exact h₀.trans ((hr (i + 1 - u)).trans (tail_end a b M (p + (i + 1 - u)) hpos))

/-! ## A block 2 left of the last: `c = -1`, closed form -/

/-- **After a block 2, a last block `3(j + 2)` becomes `2j + 3`**, for every list to the left (kernel only). -/
theorem recur_two (d j : Nat) (M : List Nat) :
    Reaches (K (2 :: d :: M) (3 * j + 5)) (K ((d + 8 + 2 * ((j + 1) / 2)) :: M) (2 * j + 2)) := by
  have h₀ := s_k_start 2 (j + 1) (d :: M)
  have h₁ := s_b_two0 d 0 M (1 :: tw 2 (j + 1) 0)
  have h₂ := s_e_one (d + 3) M (tw 2 (j + 1) 0)
  have h₃ := s_d_two (d + 3 + 3) M (tw 2 j 0)
  have h₄ := s_f_tok 2 0 ((d + 3 + 3 + 2) :: M) (twos j)
  have h₅ := tail_end (0 + 2 + 1) (d + 3 + 3 + 2) M j (by omega)
  rw [tw_two] at h₀ h₁ h₂ h₃
  rw [show 3 * j + 5 = 3 * (j + 1) + 2 by omega]
  rw [show d + 3 + 3 + 2 = d + 8 by omega, show 0 + 2 + 1 + 2 * j - 1 = 2 * j + 2 by omega] at h₅
  rw [show d + 3 + 3 + 2 = d + 8 by omega] at h₄
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))))

/-- After a block 2, a last block 3 becomes 1, which halts (`K_zero_halts`). -/
theorem recur_two_three (d : Nat) (M : List Nat) : Reaches (K (2 :: d :: M) 2) (K ((d + 8) :: M) 0) := by
  have h₀ := s_k_start 2 0 (d :: M)
  have h₁ := s_b_two0 d 0 M [1, 2]
  have h₂ := s_e_one (d + 3) M [2]
  have h₃ := s_d_two (d + 3 + 3) M []
  have h₄ := s_f_end 0 ((d + 3 + 3 + 2) :: M)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

theorem recur_two_three_halts (d : Nat) (M : List Nat) : TM.Halts trans (K (2 :: d :: M) 2) :=
  halts_of_reaches (recur_two_three d M)

/-- A good pass start with a block 2 left of a last block `3j`, `j ≥ 2`, is followed by a good one. -/
theorem recur_two_good {d j : Nat} {M : List Nat} (hg : Good (2 :: d :: M) (3 * j + 5)) :
    Good ((d + 8 + 2 * ((j + 1) / 2)) :: M) (2 * j + 2) := by
  obtain ⟨hb, -, -⟩ := hg
  refine ⟨cons_good (by omega) (tail_good (tail_good hb)), by omega, by omega⟩

/-! ## Small lists: `c ≥ -1`, and `-1` only after a block 2 -/

/-- The check behind `recur_small` for one list: `pre` stops with `c = a + 2p - 2u ≥ -1`, `-1` exactly when the block
left of the last is 2, and for `j < u` (only `j = 1`, as `u ≤ 2`) the pass map gives the same last block `2j + c`. -/
def smallOk (ls : List Nat) : Bool :=
  match pre 1000 ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 with
  | some (a :: _ :: _, p, u) =>
    decide (u ≤ 2) && decide (2 * u ≤ a + 2 * p + 1) && (decide (2 * u = a + 2 * p + 1) == (ls.headD 0 == 2)) &&
      (decide (u < 2) || match pass 1000 ls 2 with
        | some (.pass _ n) => decide (n + 1 + 2 * u = a + 2 * p + 2)
        | _ => false)
  | _ => false

/-- Every list of one, two or three blocks from 2 to 10, nearest first. -/
def smallLists : List (List Nat) :=
  let r := (List.range 9).map (· + 2)
  r.map (fun x => [x]) ++ r.flatMap (fun x => r.map (fun y => [x, y])) ++
    r.flatMap (fun x => r.flatMap (fun y => r.map (fun z => [x, y, z])))

theorem smallLists_ok : smallLists.all smallOk = true := by decide +kernel

theorem smallOk_sound {ls : List Nat} (h : smallOk ls = true) :
    ∃ a p u : Nat, 2 * u ≤ a + 2 * p + 1 ∧ (2 * u = a + 2 * p + 1 ↔ ls.headD 0 = 2) ∧
      ∀ j, 1 ≤ j → ∃ ls', Reaches (K ls (3 * j - 1)) (K ls' (a + 2 * p + 2 * j - 2 * u - 1)) := by
  unfold smallOk at h
  split at h
  · rename_i a b M p u e
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hu, hc⟩, hx⟩, hs⟩ := h
    refine ⟨a, p, u, hc, ?_, fun j hj => ?_⟩
    · by_cases h2 : 2 * u = a + 2 * p + 1 <;> by_cases hx2 : ls.headD 0 = 2 <;> simp_all
    by_cases hju : u ≤ j
    · have r := recur_sound e j hj hju (by omega)
      rw [show a + 2 * (p + (j - u)) - 1 = a + 2 * p + 2 * j - 2 * u - 1 by omega] at r
      exact ⟨_, r⟩
    · obtain rfl : j = 1 := by omega
      obtain rfl : u = 2 := by omega
      simp only [show ¬(2 < 2) from by omega, false_or] at hs
      split at hs
      · rename_i ls' n ep
        simp only [decide_eq_true_eq] at hs
        refine ⟨ls', ?_⟩
        rw [show a + 2 * p + 2 * 1 - 2 * 2 - 1 = n by omega]
        exact pass_sound ep
      · cases hs
  · cases h

/-- **`c ≥ -1` on small lists, for every `j`** (kernel only): for every list of one to three blocks from 2 to 10 to the
left of a last block `3j`, the next pass start has last block `2j + c` with `c` the same for all `j ≥ 1`, `c ≥ -1`, and
`c = -1` exactly when the block left of the last is 2. -/
theorem recur_small {ls : List Nat} (hl : ls ∈ smallLists) :
    ∃ a p u : Nat, 2 * u ≤ a + 2 * p + 1 ∧ (2 * u = a + 2 * p + 1 ↔ ls.headD 0 = 2) ∧
      ∀ j, 1 ≤ j → ∃ ls', Reaches (K ls (3 * j - 1)) (K ls' (a + 2 * p + 2 * j - 2 * u - 1)) :=
  smallOk_sound (List.all_eq_true.1 smallLists_ok ls hl)

end BB6c
