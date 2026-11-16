import TM.Basic
import TM.CTL

/-!
# Two machines that part and rejoin

Two machines `δ` and `η` (with their own state types) run on the same tape.  A *pair* `(p, q)` from a list `P` means:
the two machines have the same tape and the same head cell, `δ` is in `p` and `η` in `q`, and the configuration is
one of `δ`'s run from blank tape.  A certificate shows that from every such configuration either both machines halt,
or `δ` after `n ≥ 1` steps and `η` after `m ≥ 1` steps have the same tape and head cell again, in a pair of `P`.
Then (`halts_iff`) `δ` halts from blank tape if and only if `η` does.

Which configurations `δ`'s run can reach is given by a closed tape language (`TM.CTL`): automata `ML`, `MR` and a set
`S` of abstract configurations.  For each pair `(p, q)` and each abstract configuration `(p, ql, qr)` of `S`, the
certificate is a tree: a leaf says what happens on a finite window of cells around the head (`sync n m` or
`halt n m`, run on the window by `wrun`, which fails if a machine reads past the window), and an inner node reads one
more cell on the left (`left`) or on the right (`right`), with one subtree for each way the automaton can go on
(`TM.CTL.Auto.pops`).  `checkAll` is a computation, run by `decide`.
-/

namespace TM.Sync

open TM

/-- A finite window of the tape: cells left of the head nearest first, cells from the head rightwards, a state. -/
structure Win (Q : Type) where
  l : List Bool
  r : List Bool
  st : Q

/-- The result of running a machine on a window. -/
inductive WRes (Q : Type) where
  | ok (w : Win Q)
  | halt
  | out

section run

variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))

/-- One step on a window (`out` if the machine reads past it). -/
def wstep (w : Win Q) : WRes Q :=
  match w.r with
  | [] => .out
  | a :: r' =>
    match δ w.st a with
    | none => .halt
    | some (b, .R, s) => .ok ⟨b :: w.l, r', s⟩
    | some (b, .L, s) =>
      match w.l with
      | [] => .out
      | c :: l' => .ok ⟨l', c :: b :: r', s⟩

/-- `n` steps on a window; `halt` if the machine reaches a halting configuration on the way. -/
def wrun : Nat → Win Q → WRes Q
  | 0, w => .ok w
  | n + 1, w =>
    match wstep δ w with
    | .ok w' => wrun n w'
    | .halt => .halt
    | .out => .out

/-- A window placed on a tape: the streams `L` and `R` beyond it. -/
def emb (w : Win Q) (L R : Tape) : Cfg Q := ⟨app w.l L, app w.r R, w.st⟩

theorem wstep_ok {w w' : Win Q} (h : wstep δ w = .ok w') (L R : Tape) :
    step δ (emb w L R) = some (emb w' L R) := by
  rcases w with ⟨l, r, s⟩
  cases r with
  | nil => simp [wstep] at h
  | cons a r' =>
    cases hd : δ s a with
    | none => simp [wstep, hd] at h
    | some t =>
      obtain ⟨b, d, s'⟩ := t
      cases d with
      | R =>
        simp only [wstep, hd, WRes.ok.injEq] at h
        subst h
        simp [step, emb, hd]
      | L =>
        cases l with
        | nil => simp [wstep, hd] at h
        | cons c l' =>
          simp only [wstep, hd, WRes.ok.injEq] at h
          subst h
          simp [step, emb, hd]

theorem wstep_halt {w : Win Q} (h : wstep δ w = .halt) (L R : Tape) : step δ (emb w L R) = none := by
  rcases w with ⟨l, r, s⟩
  cases r with
  | nil => simp [wstep] at h
  | cons a r' =>
    cases hd : δ s a with
    | none => simp [step, emb, hd]
    | some t =>
      obtain ⟨b, d, s'⟩ := t
      cases d with
      | R => simp [wstep, hd] at h
      | L => cases l <;> simp [wstep, hd] at h

theorem wrun_ok : ∀ (n : Nat) {w w' : Win Q}, wrun δ n w = .ok w' → ∀ L R : Tape,
    steps δ n (emb w L R) = some (emb w' L R)
  | 0, w, w', h, L, R => by simp [wrun] at h; subst h; rfl
  | n + 1, w, w', h, L, R => by
    cases hs : wstep δ w with
    | ok w1 =>
      simp only [wrun, hs] at h
      rw [steps_succ_of_step δ n (wstep_ok δ hs L R)]
      exact wrun_ok n h L R
    | halt => simp [wrun, hs] at h
    | out => simp [wrun, hs] at h

theorem wrun_halt : ∀ (n : Nat) {w : Win Q}, wrun δ n w = .halt → ∀ L R : Tape, Halts δ (emb w L R)
  | 0, w, h, L, R => by simp [wrun] at h
  | n + 1, w, h, L, R => by
    cases hs : wstep δ w with
    | ok w1 =>
      simp only [wrun, hs] at h
      obtain ⟨k, c, h1, h2⟩ := wrun_halt n h L R
      exact ⟨k + 1, c, by rw [steps_succ_of_step δ k (wstep_ok δ hs L R)]; exact h1, h2⟩
    | halt => exact ⟨0, _, rfl, wstep_halt δ hs L R⟩
    | out => simp [wrun, hs] at h

/-- Runs compose: `a + b` steps are `a` steps, then `b`. -/
theorem steps_add : ∀ (a b : Nat) (c : Cfg Q), steps δ (a + b) c = (steps δ a c).bind (steps δ b)
  | 0, b, c => by simp
  | a + 1, b, c => by
    cases hs : step δ c with
    | none =>
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e]; simp [steps, hs]
    | some d =>
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e, steps_succ_of_step δ (a + b) hs, steps_succ_of_step δ a hs]
      exact steps_add a b d

/-- If `c` reaches `c'` in `n` steps and halts after `N` steps, then `n ≤ N` and `c'` halts after `N - n`. -/
theorem halt_after {n N : Nat} {c c' ch : Cfg Q} (h1 : steps δ n c = some c') (h2 : steps δ N c = some ch)
    (h3 : step δ ch = none) : n ≤ N ∧ steps δ (N - n) c' = some ch := by
  have hle : n ≤ N := by
    rcases Nat.lt_or_ge N n with hlt | hge
    · have e : n = N + ((n - N - 1) + 1) := by omega
      rw [e, steps_halt δ h2 h3] at h1
      cases h1
    · exact hge
  refine ⟨hle, ?_⟩
  have e : N = n + (N - n) := by omega
  rw [e, steps_add, h1] at h2
  simpa using h2

theorem halts_of_steps {n : Nat} {c c' : Cfg Q} (h : steps δ n c = some c') (hh : Halts δ c') : Halts δ c := by
  obtain ⟨k, d, h1, h2⟩ := hh
  exact ⟨n + k, d, steps_seq δ h h1, h2⟩

end run

section check

variable {Q R : Type} [DecidableEq Q] [DecidableEq R]
variable (δ : Q → Bool → Option (Bool × Dir × Q)) (η : R → Bool → Option (Bool × Dir × R))
variable (ML MR : CTL.Auto) (P : List (Q × R))

/-- A certificate tree for one pair and one abstract configuration. -/
inductive Cert where
  | sync (n m : Nat)
  | halt (n m : Nat)
  | left (cs : List Cert)
  | right (cs : List Cert)

/-- A leaf on a window `wl`, `wr`, with `δ` in `p` and `η` in `q`. -/
def leafOk (wl wr : List Bool) (p : Q) (q : R) : Cert → Bool
  | .sync n m =>
    0 < n && 0 < m &&
      (match wrun δ n ⟨wl, wr, p⟩, wrun η m ⟨wl, wr, q⟩ with
        | .ok a, .ok b => a.l == b.l && a.r == b.r && decide ((a.st, b.st) ∈ P)
        | _, _ => false)
  | .halt n m =>
      (match wrun δ n ⟨wl, wr, p⟩, wrun η m ⟨wl, wr, q⟩ with
        | .halt, .halt => true
        | _, _ => false)
  | _ => false

/-- The check of a tree (with `fuel` bounding its depth). -/
def chk : Nat → List Bool → List Bool → Nat → Nat → Q → R → Cert → Bool
  | 0, _, _, _, _, _, _, _ => false
  | fuel + 1, wl, wr, ql, qr, p, q, c =>
    match c with
    | .left cs =>
      cs.length == (ML.pops ql).length &&
        (cs.zip (ML.pops ql)).all (fun e => chk fuel (wl ++ [e.2.1]) wr e.2.2 qr p q e.1)
    | .right cs =>
      cs.length == (MR.pops qr).length &&
        (cs.zip (MR.pops qr)).all (fun e => chk fuel wl (wr ++ [e.2.1]) ql e.2.2 p q e.1)
    | c => leafOk δ η P wl wr p q c

/-- What a certificate gives for two configurations with the same tape. -/
def Good (c : Cfg Q) (d : Cfg R) : Prop :=
  (∃ n m c' d', 0 < n ∧ 0 < m ∧ steps δ n c = some c' ∧ steps η m d = some d' ∧ c'.l = d'.l ∧ c'.r = d'.r ∧
    (c'.st, d'.st) ∈ P) ∨ (Halts δ c ∧ Halts η d)

theorem leafOk_sound {wl wr : List Bool} {p : Q} {q : R} {c : Cert} (h : leafOk δ η P wl wr p q c = true)
    (L R' : Tape) : Good δ η P (emb ⟨wl, wr, p⟩ L R') (emb ⟨wl, wr, q⟩ L R') := by
  cases c with
  | sync n m =>
    simp only [leafOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hn, hm⟩, h⟩ := h
    cases hx : wrun δ n ⟨wl, wr, p⟩ with
    | ok a =>
      cases hy : wrun η m ⟨wl, wr, q⟩ with
      | ok b =>
        rw [hx, hy] at h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨hl, hr⟩, hP⟩ := h
        left
        refine ⟨n, m, emb a L R', emb b L R', hn, hm, wrun_ok δ n hx L R', wrun_ok η m hy L R', ?_, ?_, hP⟩
        · simp [emb, hl]
        · simp [emb, hr]
      | halt => rw [hx, hy] at h; simp at h
      | out => rw [hx, hy] at h; simp at h
    | halt => rw [hx] at h; cases hy : wrun η m ⟨wl, wr, q⟩ <;> rw [hy] at h <;> simp at h
    | out => rw [hx] at h; cases hy : wrun η m ⟨wl, wr, q⟩ <;> rw [hy] at h <;> simp at h
  | halt n m =>
    simp only [leafOk] at h
    cases hx : wrun δ n ⟨wl, wr, p⟩ <;> cases hy : wrun η m ⟨wl, wr, q⟩ <;> rw [hx, hy] at h <;>
      simp at h
    exact Or.inr ⟨wrun_halt δ n hx L R', wrun_halt η m hy L R'⟩
  | left cs => simp [leafOk] at h
  | right cs => simp [leafOk] at h

theorem exists_zip {α β : Type} : ∀ (as : List α) (bs : List β), as.length = bs.length → ∀ b ∈ bs,
    ∃ a, (a, b) ∈ as.zip bs
  | [], [], _, b, hb => by simp at hb
  | a :: as, b' :: bs, hl, b, hb => by
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨a, by simp⟩
    · obtain ⟨a', ha'⟩ := exists_zip as bs (by simpa using hl) b hb
      exact ⟨a', by simp [ha']⟩
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem app_snoc (w : List Bool) (x : Bool) (t : Tape) : app (w ++ [x]) t = app w (cons x t) := by
  rw [← app_app]; rfl

theorem chk_sound : ∀ (fuel : Nat) (wl wr : List Bool) (ql qr : Nat) (p : Q) (q : R) (c : Cert),
    chk δ η ML MR P fuel wl wr ql qr p q c = true → ∀ L R' : Tape, CTL.Lang ML ql L → CTL.Lang MR qr R' →
    Good δ η P (emb ⟨wl, wr, p⟩ L R') (emb ⟨wl, wr, q⟩ L R')
  | 0, _, _, _, _, _, _, _, h, _, _, _, _ => by simp [chk] at h
  | fuel + 1, wl, wr, ql, qr, p, q, c, h, L, R', hL, hR => by
    cases c with
    | sync n m => exact leafOk_sound δ η P (by simpa [chk] using h) L R'
    | halt n m => exact leafOk_sound δ η P (by simpa [chk] using h) L R'
    | left cs =>
      simp only [chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨hlen, hall⟩ := h
      obtain ⟨e, he, hx, hL'⟩ := hL.pop
      obtain ⟨c', hc'⟩ := exists_zip cs (ML.pops ql) hlen e he
      have := chk_sound fuel (wl ++ [e.1]) wr e.2 qr p q c' (hall _ hc') (tail L) R' hL' hR
      have eL : app (wl ++ [e.1]) (tail L) = app wl L := by
        rw [app_snoc, ← hx, CTL.cons_head_tail]
      simpa [emb, eL] using this
    | right cs =>
      simp only [chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨hlen, hall⟩ := h
      obtain ⟨e, he, hx, hR'⟩ := hR.pop
      obtain ⟨c', hc'⟩ := exists_zip cs (MR.pops qr) hlen e he
      have := chk_sound fuel wl (wr ++ [e.1]) ql e.2 p q c' (hall _ hc') L (tail R') hL hR'
      have eR : app (wr ++ [e.1]) (tail R') = app wr R' := by
        rw [app_snoc, ← hx, CTL.cons_head_tail]
      simpa [emb, eR] using this

/-- For every pair `(p, q)` of `P`, the abstract configurations of `S` in state `p`, in order, each with its
certificate: `certs` lists, for each pair in the order of `P`, the trees in the order of `S.filter`. -/
def checkAll (S : List (Q × Nat × Nat)) (certs : List (List Cert)) (fuel : Nat) : Bool :=
  P.length == certs.length &&
    (P.zip certs).all (fun e =>
      let F := S.filter (fun a => a.1 == e.1.1)
      F.length == e.2.length &&
        (F.zip e.2).all (fun f => chk δ η ML MR P fuel [] [] f.1.2.1 f.1.2.2 e.1.1 e.1.2 f.2))

theorem good_of_inv {S : List (Q × Nat × Nat)} {certs : List (List Cert)} {fuel : Nat}
    (hc : checkAll δ η ML MR P S certs fuel = true) {c : Cfg Q} {q : R} (hinv : CTL.Inv ML MR S c)
    (hP : (c.st, q) ∈ P) : Good δ η P c ⟨c.l, c.r, q⟩ := by
  simp only [checkAll, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨hlen, hall⟩ := hc
  obtain ⟨cs, hcs⟩ := exists_zip certs P hlen.symm _ hP
  have hz : ((c.st, q), cs) ∈ P.zip certs := by
    rw [List.mem_iff_getElem] at hcs ⊢
    obtain ⟨i, hi, he⟩ := hcs
    simp only [List.getElem_zip, Prod.mk.injEq] at he
    exact ⟨i, by simp [List.length_zip] at hi ⊢; omega, by simp [List.getElem_zip, he.1, he.2]⟩
  obtain ⟨hl2, hall2⟩ := hall _ hz
  obtain ⟨ql, qr, hm, hL, hR⟩ := hinv
  have hf : (c.st, ql, qr) ∈ S.filter (fun a => a.1 == c.st) := by simp [hm]
  obtain ⟨t, ht⟩ := exists_zip cs _ hl2.symm _ hf
  have hz2 : ((c.st, ql, qr), t) ∈ (S.filter (fun a => a.1 == c.st)).zip cs := by
    rw [List.mem_iff_getElem] at ht ⊢
    obtain ⟨i, hi, he⟩ := ht
    simp only [List.getElem_zip, Prod.mk.injEq] at he
    exact ⟨i, by simp [List.length_zip] at hi ⊢; omega, by simp [List.getElem_zip, he.1, he.2]⟩
  have := chk_sound δ η ML MR P fuel [] [] ql qr c.st q t (hall2 _ hz2) c.l c.r hL hR
  simpa [emb] using this

end check

section main

variable {Q R : Type} [DecidableEq Q] [DecidableEq R]
variable {δ : Q → Bool → Option (Bool × Dir × Q)} {η : R → Bool → Option (Bool × Dir × R)}
variable {ML MR : CTL.Auto} {P : List (Q × R)} {S : List (Q × Nat × Nat)} {certs : List (List Cert)}
variable {fuel : Nat} {q₀ : Q}

/-- The two runs are together: `c` is on `δ`'s run, `d` has the same tape and head, and the states are a pair. -/
def Rel (δ : Q → Bool → Option (Bool × Dir × Q)) (P : List (Q × R)) (q₀ : Q) (c : Cfg Q) (d : Cfg R) : Prop :=
  (∃ n, steps δ n (blankCfg q₀) = some c) ∧ c.l = d.l ∧ c.r = d.r ∧ (c.st, d.st) ∈ P

theorem good_of_rel (hS : CTL.closed δ ML MR S = true) (h₀ : CTL.starts ML MR S q₀ = true)
    (hc : checkAll δ η ML MR P S certs fuel = true) {c : Cfg Q} {d : Cfg R} (h : Rel δ P q₀ c d) :
    Good δ η P c d := by
  obtain ⟨⟨n, hn⟩, hl, hr, hP⟩ := h
  have hinv := CTL.reach δ hS h₀ hn
  have := good_of_inv δ η ML MR P hc hinv hP
  rcases d with ⟨dl, dr, ds⟩
  simp only at hl hr
  subst hl hr
  exact this

theorem fwd (hS : CTL.closed δ ML MR S = true) (h₀ : CTL.starts ML MR S q₀ = true)
    (hc : checkAll δ η ML MR P S certs fuel = true) :
    ∀ (N : Nat) {c : Cfg Q} {d : Cfg R} {ch : Cfg Q}, Rel δ P q₀ c d → steps δ N c = some ch →
      step δ ch = none → Halts η d := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro c d ch hrel hN hh
    rcases good_of_rel hS h₀ hc hrel with ⟨n, m, c', d', hn, _, hc', hd', hl, hr, hP⟩ | ⟨_, hy⟩
    · obtain ⟨hle, hrest⟩ := halt_after δ hc' hN hh
      have hrel' : Rel δ P q₀ c' d' := by
        obtain ⟨⟨k, hk⟩, _⟩ := hrel
        exact ⟨⟨k + n, steps_seq δ hk hc'⟩, hl, hr, hP⟩
      exact halts_of_steps η hd' (ih (N - n) (by omega) hrel' hrest hh)
    · exact hy

theorem bwd (hS : CTL.closed δ ML MR S = true) (h₀ : CTL.starts ML MR S q₀ = true)
    (hc : checkAll δ η ML MR P S certs fuel = true) :
    ∀ (N : Nat) {c : Cfg Q} {d : Cfg R} {dh : Cfg R}, Rel δ P q₀ c d → steps η N d = some dh →
      step η dh = none → Halts δ c := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro c d dh hrel hN hh
    rcases good_of_rel hS h₀ hc hrel with ⟨n, m, c', d', _, hm, hc', hd', hl, hr, hP⟩ | ⟨hx, _⟩
    · obtain ⟨hle, hrest⟩ := halt_after η hd' hN hh
      have hrel' : Rel δ P q₀ c' d' := by
        obtain ⟨⟨k, hk⟩, _⟩ := hrel
        exact ⟨⟨k + n, steps_seq δ hk hc'⟩, hl, hr, hP⟩
      exact halts_of_steps δ hc' (ih (N - m) (by omega) hrel' hrest hh)
    · exact hx

/-- From a common configuration: if `δ`'s run reaches `c₀` and `η`'s run reaches `d₀` with the same tape and head,
in a pair of `P`, the two machines halt from blank tape together. -/
theorem halts_iff_of (hS : CTL.closed δ ML MR S = true) (h₀ : CTL.starts ML MR S q₀ = true)
    (hc : checkAll δ η ML MR P S certs fuel = true) {r₀ : R} {a b : Nat} {c₀ : Cfg Q} {d₀ : Cfg R}
    (ha : steps δ a (blankCfg q₀) = some c₀) (hb : steps η b (blankCfg r₀) = some d₀)
    (hl : c₀.l = d₀.l) (hr : c₀.r = d₀.r) (hP : (c₀.st, d₀.st) ∈ P) :
    Halts δ (blankCfg q₀) ↔ Halts η (blankCfg r₀) := by
  have hrel : Rel δ P q₀ c₀ d₀ := ⟨⟨a, ha⟩, hl, hr, hP⟩
  constructor
  · rintro ⟨N, ch, hN, hh⟩
    obtain ⟨_, hrest⟩ := halt_after δ ha hN hh
    exact halts_of_steps η hb (fwd hS h₀ hc _ hrel hrest hh)
  · rintro ⟨N, dh, hN, hh⟩
    obtain ⟨_, hrest⟩ := halt_after η hb hN hh
    exact halts_of_steps δ ha (bwd hS h₀ hc _ hrel hrest hh)

/-- From blank tape: `(q₀, r₀)` is a pair. -/
theorem halts_iff (hS : CTL.closed δ ML MR S = true) (h₀ : CTL.starts ML MR S q₀ = true)
    (hc : checkAll δ η ML MR P S certs fuel = true) {r₀ : R} (hP : (q₀, r₀) ∈ P) :
    Halts δ (blankCfg q₀) ↔ Halts η (blankCfg r₀) :=
  halts_iff_of hS h₀ hc (a := 0) (b := 0) rfl rfl rfl rfl hP

end main

end TM.Sync
