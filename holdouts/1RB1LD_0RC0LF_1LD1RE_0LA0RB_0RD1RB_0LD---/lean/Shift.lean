import Cascade

/-! # The shift law and the dirty stop, for 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---

A round leaves its stream, up to where its cascade stopped, as a row of *tokens* `000`, `100`, `1010`
(`Casc.toks`, from `Blk.out`). The next round reads that row again, starting two cells earlier (`X = 1 0 S`).

**The shift law.** Every block of the next round starts one or two cells before the end of a token, one block
per token: never at a token boundary. What is left of the token ahead of the block (`Rem`) is `0` (two cells into a
`000`/`100`), `10` (two cells into a `1010`) or `00` (one cell into a `000`/`100`), and it moves from token to
token by `Rem.next`: after a `1010` it is `10`, after a `100` it is `0`, after a `000` it stays `0` or becomes `00`.
`shift`: every block start `q` of any number of visits is one of the positions `Pt` (one per token) or lies at
least 3 cells past the last of them, `endp`, which is 1 or 2 cells before the end of the row. So the block of the
next round that holds the old stop starts 1 or 2 cells before it, never at it (`never_at_stop`).

**The dirty stop.** A stop that leaves two adjacent 1s (`010` hit once leaves `110`; `011` hit once leaves `111`)
is followed by the next round at `endp`. If what is left there is `0` the block reads `011` and halts on a second
visit; if it is `10` or `00` the block reads `1011` or `0011`, which is safe here (`1011 -> 1000`), and any halt
lies further right. `dirty`: a halt of the next round is at the cell just before the dirty pair, and then the row's
last token other than `000` is a `100` (`fin_r0`), or it is at least one cell past the pair.

Kernel only (no `native_decide`). -/

namespace H173741

open TM

/-! ## Tokens -/

inductive Tok | z | o | w
  deriving DecidableEq

/-- `000`, `100`, `1010`. -/
def Tok.bits : Tok → List Bool
  | .z => [false, false, false]
  | .o => [true, false, false]
  | .w => [true, false, true, false]

def toks : List Tok → List Bool
  | [] => []
  | T :: L => T.bits ++ toks L

/-- What is left of the token ahead of a block of the next round: `0`, `10` or `00`. -/
inductive Rem | r0 | r10 | r00
  deriving DecidableEq

def Rem.bits : Rem → List Bool
  | .r0 => [false]
  | .r10 => [true, false]
  | .r00 => [false, false]

def Rem.next : Rem → Tok → Rem
  | _, .w => .r10
  | _, .o => .r0
  | .r0, .z => .r0
  | .r10, .z => .r00
  | .r00, .z => .r00

/-- The length of the block that starts at `st` and reads into the token `T`. -/
def Rem.len (st : Rem) (T : Tok) : Nat := st.bits.length + T.bits.length - (st.next T).bits.length

/-- `Pt st L q`: a block of the next round may start at offset `q` (one position per token). -/
inductive Pt : Rem → List Tok → Nat → Prop
  | here {st : Rem} {L : List Tok} : Pt st L 0
  | step {st : Rem} {T : Tok} {L : List Tok} {q : Nat} : Pt (st.next T) L q → Pt st (T :: L) (st.len T + q)

/-- The last of the positions `Pt`: where the block that reads past the row starts. -/
def endp : Rem → List Tok → Nat
  | _, [] => 0
  | st, T :: L => st.len T + endp (st.next T) L

/-- What is left ahead of the last position. -/
def fin : Rem → List Tok → Rem
  | st, [] => st
  | st, T :: L => fin (st.next T) L

theorem len_pos (st : Rem) (T : Tok) : 3 ≤ st.len T := by
  cases st <;> cases T <;> decide

theorem endp_fin (st : Rem) (L : List Tok) :
    endp st L + (fin st L).bits.length = st.bits.length + (toks L).length := by
  induction L generalizing st with
  | nil => simp [endp, fin, toks]
  | cons T L ih =>
    have := ih (st.next T)
    simp only [endp, fin, toks, List.length_append]
    have h3 : (st.next T).bits.length ≤ st.bits.length + T.bits.length := by
      cases st <;> cases T <;> decide
    unfold Rem.len; omega

theorem fin_bits_pos (st : Rem) (L : List Tok) : 1 ≤ (fin st L).bits.length ∧ (fin st L).bits.length ≤ 2 := by
  cases (fin st L) <;> decide

theorem Pt.le {st : Rem} {L : List Tok} {q : Nat} (h : Pt st L q) : q ≤ endp st L := by
  induction h with
  | here => exact Nat.zero_le _
  | step _ ih => simp only [endp]; omega

/-! ## Block starts -/

/-- `Starts n s q`: some block of a cascade of `n` visits to `s` starts at offset `q` (following the rules of
`Casc` and `CascH`; every block of an actual cascade is one, see `Casc.starts`, `CascH.starts`). -/
inductive Starts : Nat → Tape → Nat → Prop
  | here {n : Nat} {s : Tape} : Starts n s 0
  | fwd {n m q : Nat} {w w' : List Bool} {t : Tape} :
      Blk n w w' (m + 1) → Starts (m + 1) t q → Starts n (app w t) (w.length + q)
  | e {n q : Nat} {t : Tape} :
      Starts n (app [true, false, false, false] t) q → Starts (n + 1) (app [true, false, true, true] t) q
  | d {n q : Nat} {t : Tape} :
      Starts n (app [true, false, true, true] t) q → Starts (n + 1) (app [false, false, true, true] t) q

theorem Casc.starts {n f : Nat} {s s' : Tape} {E : List Nat} (h : Casc n s s' f E) : Starts n s f := by
  induction h with
  | fin _ => exact Starts.here
  | fwd hb _ ih => exact Starts.fwd hb ih
  | e1 => exact Starts.here
  | e _ ih => exact Starts.e ih
  | d1 => exact Starts.here
  | d _ ih => exact Starts.d ih
  | u1 => exact Starts.here

theorem CascH.starts {n p : Nat} {s : Tape} (h : CascH n s p) : Starts n s p := by
  induction h with
  | h111 => exact Starts.here
  | h011 => exact Starts.here
  | fwd hb _ ih => exact Starts.fwd hb ih
  | e _ ih => exact Starts.e ih
  | d _ ih => exact Starts.d ih

/-! ## Reading tapes -/

theorem cons_inj {a b : Bool} {s t : Tape} (h : cons a s = cons b t) : a = b ∧ s = t :=
  ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩

theorem app_cancel : ∀ (w : List Bool) {s t : Tape}, app w s = app w t → s = t
  | [], _, _, h => h
  | _ :: w, _, _, h => app_cancel w (cons_inj h).2

theorem app_toks_cons (T : Tok) (L : List Tok) (u : Tape) : app (toks (T :: L)) u = app T.bits (app (toks L) u) := by
  simp [toks, app_app]

/-- The block that starts at `st` and reads into the token `T`: its length, and the rest of the row. -/
theorem blk_step {n m : Nat} {w w' : List Bool} {t u : Tape} {st : Rem} {T : Tok} {L : List Tok}
    (hb : Blk n w w' m) (h : app w t = app (st.bits ++ toks (T :: L)) u) :
    w.length = st.len T ∧ t = app ((st.next T).bits ++ toks L) u := by
  rw [← app_app, app_toks_cons] at h
  rw [← app_app]
  generalize app (toks L) u = v at h ⊢
  cases st <;> cases T <;> cases hb <;>
    simp only [Rem.bits, Tok.bits, Rem.next, Rem.len, app, List.length] at h ⊢ <;>
    first
    | (have h' := h; replace h' := congrFun h' 0; simp [cons] at h'; done)
    | (have h' := h; replace h' := congrFun h' 1; simp [cons] at h'; done)
    | (have h' := h; replace h' := congrFun h' 2; simp [cons] at h'; done)
    | (have h' := h; replace h' := congrFun h' 3; simp [cons] at h'; done)
    | (refine ⟨by first | trivial | rfl, ?_⟩
       first
       | exact (cons_inj (cons_inj (cons_inj (cons_inj h).2).2).2).2
       | exact (cons_inj (cons_inj (cons_inj h).2).2).2)

/-- No `1011`, `0011`, `011` or `111` at the start of a row with at least one token. -/
theorem no1011 {t u : Tape} {st : Rem} {T : Tok} {L : List Tok}
    (h : app [true, false, true, true] t = app (st.bits ++ toks (T :: L)) u) : False := by
  rw [← app_app, app_toks_cons] at h
  generalize app (toks L) u = v at h
  cases st <;> cases T <;> simp only [Rem.bits, Tok.bits, app] at h <;>
    first
    | (replace h := congrFun h 0; simp [cons] at h; done)
    | (replace h := congrFun h 2; simp [cons] at h; done)
    | (replace h := congrFun h 3; simp [cons] at h; done)

theorem no0011 {t u : Tape} {st : Rem} {T : Tok} {L : List Tok}
    (h : app [false, false, true, true] t = app (st.bits ++ toks (T :: L)) u) : False := by
  rw [← app_app, app_toks_cons] at h
  generalize app (toks L) u = v at h
  cases st <;> cases T <;> simp only [Rem.bits, Tok.bits, app] at h <;>
    first
    | (replace h := congrFun h 0; simp [cons] at h; done)
    | (replace h := congrFun h 1; simp [cons] at h; done)
    | (replace h := congrFun h 2; simp [cons] at h; done)
    | (replace h := congrFun h 3; simp [cons] at h; done)

theorem no011 {t u : Tape} {st : Rem} {T : Tok} {L : List Tok}
    (h : app [false, true, true] t = app (st.bits ++ toks (T :: L)) u) : False := by
  rw [← app_app, app_toks_cons] at h
  generalize app (toks L) u = v at h
  cases st <;> cases T <;> simp only [Rem.bits, Tok.bits, app] at h <;>
    first
    | (replace h := congrFun h 0; simp [cons] at h; done)
    | (replace h := congrFun h 1; simp [cons] at h; done)
    | (replace h := congrFun h 2; simp [cons] at h; done)

theorem no111 {t u : Tape} {st : Rem} {L : List Tok}
    (h : app [true, true, true] t = app (st.bits ++ toks L) u) : False := by
  cases L with
  | nil =>
    cases st <;> simp only [Rem.bits, toks, List.append_nil, app] at h <;>
      first
      | (replace h := congrFun h 0; simp [cons] at h; done)
      | (replace h := congrFun h 1; simp [cons] at h; done)
  | cons T L =>
    rw [← app_app, app_toks_cons] at h
    generalize app (toks L) u = v at h
    cases st <;> cases T <;> simp only [Rem.bits, Tok.bits, app] at h <;>
      first
      | (replace h := congrFun h 0; simp [cons] at h; done)
      | (replace h := congrFun h 1; simp [cons] at h; done)

/-! ## The shift law -/

/-- Visits to `1000` start their blocks at 0 or at 3 and beyond. -/
theorem starts1000 {n q : Nat} {t : Tape} (h : Starts n (app [true, false, false, false] t) q) : q = 0 ∨ 3 ≤ q := by
  generalize hs : app [true, false, false, false] t = s at h
  cases h with
  | here => exact Or.inl rfl
  | @fwd _ m _ _ _ _ hb _ =>
    right
    generalize m + 1 = M at hb
    cases hb <;> simp only [app, List.length] at hs ⊢ <;>
      first
      | omega
      | (replace hs := congrFun hs 0; simp [cons] at hs; done)
      | (replace hs := congrFun hs 1; simp [cons] at hs; done)
      | (replace hs := congrFun hs 2; simp [cons] at hs; done)
  | e _ => replace hs := congrFun hs 2; simp [app, cons] at hs
  | d _ => replace hs := congrFun hs 0; simp [app, cons] at hs

theorem starts1011 {n q : Nat} {t : Tape} (h : Starts n (app [true, false, true, true] t) q) : q = 0 ∨ 3 ≤ q := by
  generalize hs : app [true, false, true, true] t = s at h
  cases h with
  | here => exact Or.inl rfl
  | @fwd _ m _ _ _ _ hb _ =>
    exfalso
    generalize m + 1 = M at hb
    cases hb <;> simp only [app] at hs <;>
      first
      | (replace hs := congrFun hs 0; simp [cons] at hs; done)
      | (replace hs := congrFun hs 1; simp [cons] at hs; done)
      | (replace hs := congrFun hs 2; simp [cons] at hs; done)
      | (replace hs := congrFun hs 3; simp [cons] at hs; done)
  | e h' =>
    have e := app_cancel [true, false, true, true] hs
    subst e; exact starts1000 h'
  | d _ => replace hs := congrFun hs 0; simp [app, cons] at hs

theorem Blk.len_ge {n m : Nat} {w w' : List Bool} (hb : Blk n w w' m) : 3 ≤ w.length := by
  cases hb <;> simp

/-- **The shift law.** On a row of tokens entered at `st`, every block starts at one of the positions `Pt`, one
per token, or at least 3 cells past the last of them. -/
theorem shift {n q : Nat} {s : Tape} (h : Starts n s q) :
    ∀ (st : Rem) (L : List Tok) (u : Tape), s = app (st.bits ++ toks L) u → Pt st L q ∨ endp st L + 3 ≤ q := by
  induction h with
  | here => exact fun _ _ _ _ => Or.inl Pt.here
  | @fwd n m q w w' t hb _ ih =>
    intro st L u hs
    cases L with
    | nil => right; have := hb.len_ge; simp only [endp]; omega
    | cons T L =>
      obtain ⟨hl, ht⟩ := blk_step hb hs
      rcases ih (st.next T) L u ht with hp | hp
      · left; rw [hl]; exact Pt.step hp
      · right; simp only [endp]; omega
  | @e n q t h' _ =>
    intro st L u hs
    cases L with
    | nil =>
      rcases starts1000 h' with rfl | hq
      · exact Or.inl Pt.here
      · right; simp only [endp]; omega
    | cons T L => exact absurd (no1011 hs) id
  | @d n q t h' _ =>
    intro st L u hs
    cases L with
    | nil =>
      rcases starts1011 h' with rfl | hq
      · exact Or.inl Pt.here
      · right; simp only [endp]; omega
    | cons T L => exact absurd (no0011 hs) id

/-! ## The dirty stop -/

theorem cascH1000 {n p : Nat} {t : Tape} (h : CascH n (app [true, false, false, false] t) p) : 3 ≤ p := by
  rcases starts1000 h.starts with rfl | hp
  · exfalso
    generalize hs : app [true, false, false, false] t = s at h
    generalize hp0 : (0 : Nat) = p0 at h
    cases h with
    | h111 => replace hs := congrFun hs 1; simp [app, cons] at hs
    | h011 => replace hs := congrFun hs 0; simp [app, cons] at hs
    | fwd hb _ => have := hb.len_ge; omega
    | e _ => replace hs := congrFun hs 2; simp [app, cons] at hs
    | d _ => replace hs := congrFun hs 0; simp [app, cons] at hs
  · exact hp

theorem cascH1011 {n p : Nat} {t : Tape} (h : CascH n (app [true, false, true, true] t) p) : 3 ≤ p := by
  generalize hs : app [true, false, true, true] t = s at h
  cases h with
  | h111 => replace hs := congrFun hs 1; simp [app, cons] at hs
  | h011 => replace hs := congrFun hs 0; simp [app, cons] at hs
  | @fwd _ m _ _ _ _ hb _ =>
    exfalso
    generalize m + 1 = M at hb
    cases hb <;> simp only [app] at hs <;>
      first
      | (replace hs := congrFun hs 0; simp [cons] at hs; done)
      | (replace hs := congrFun hs 1; simp [cons] at hs; done)
      | (replace hs := congrFun hs 2; simp [cons] at hs; done)
      | (replace hs := congrFun hs 3; simp [cons] at hs; done)
  | e h' =>
    have e := app_cancel [true, false, true, true] hs
    subst e; exact cascH1000 h'
  | d _ => replace hs := congrFun hs 0; simp [app, cons] at hs

/-- **A halt after a dirty stop.** On a row of tokens entered at `st` and followed by two 1s, a cascade can halt
only at `endp`, with `0` left ahead of it (the block reads `011`), or at least one cell past the two 1s. -/
theorem dirty {n p : Nat} {s : Tape} (h : CascH n s p) :
    ∀ (st : Rem) (L : List Tok) (u : Tape), s = app (st.bits ++ toks L) u → u 0 = true → u 1 = true →
      (fin st L = .r0 ∧ p = endp st L) ∨ endp st L + (fin st L).bits.length + 1 ≤ p := by
  induction h with
  | @h111 n t => intro st L u hs _ _; exact absurd (no111 hs) id
  | @h011 n t =>
    intro st L u hs h0 h1
    cases L with
    | nil =>
      cases st with
      | r0 => left; exact ⟨rfl, rfl⟩
      | r10 => replace hs := congrFun hs 0; simp [Rem.bits, toks, app, cons] at hs
      | r00 => replace hs := congrFun hs 1; simp [Rem.bits, toks, app, cons] at hs
    | cons T L => exact absurd (no011 hs) id
  | @fwd n m p w w' t hb _ ih =>
    intro st L u hs h0 h1
    cases L with
    | nil =>
      exfalso
      generalize m + 1 = M at hb
      cases st <;> cases hb <;> simp only [Rem.bits, toks, List.append_nil, app] at hs <;>
        first
        | (replace hs := congrFun hs 0; simp [cons] at hs; done)
        | (replace hs := congrFun hs 1; simp [cons] at hs; done)
        | (replace hs := congrFun hs 1; simp [cons, h0] at hs; done)
        | (replace hs := congrFun hs 2; simp [cons, h0, h1] at hs; done)
        | (replace hs := congrFun hs 3; simp [cons, h0, h1] at hs; done)
    | cons T L =>
      obtain ⟨hl, ht⟩ := blk_step hb hs
      rcases ih (st.next T) L u ht h0 h1 with ⟨hf, hp⟩ | hp
      · left; exact ⟨hf, by simp only [endp]; omega⟩
      · right; simp only [endp, fin] at hp ⊢; omega
  | @e n p t h' _ =>
    intro st L u hs h0 h1
    cases L with
    | nil =>
      have := cascH1000 h'
      right
      cases st with
      | r10 => simp [endp, fin, Rem.bits]; omega
      | r0 => replace hs := congrFun hs 0; simp [Rem.bits, toks, app, cons] at hs
      | r00 => replace hs := congrFun hs 0; simp [Rem.bits, toks, app, cons] at hs
    | cons T L => exact absurd (no1011 hs) id
  | @d n p t h' _ =>
    intro st L u hs h0 h1
    cases L with
    | nil =>
      have := cascH1011 h'
      right
      cases st with
      | r00 => simp [endp, fin, Rem.bits]; omega
      | r0 => replace hs := congrFun hs 1; simp [Rem.bits, toks, app, cons, h0] at hs
      | r10 => replace hs := congrFun hs 0; simp [Rem.bits, toks, app, cons] at hs
    | cons T L => exact absurd (no0011 hs) id

/-! ## What is left ahead of the last position -/

/-- The row's last token other than `000` is `100`. -/
def LastO (L : List Tok) : Prop := ∃ L1 L2, L = L1 ++ Tok.o :: L2 ∧ ∀ T ∈ L2, T = .z

theorem lastO_cons (T : Tok) (L : List Tok) : LastO (T :: L) ↔ LastO L ∨ (T = .o ∧ ∀ U ∈ L, U = .z) := by
  constructor
  · rintro ⟨L1, L2, he, hz⟩
    cases L1 with
    | nil => simp at he; obtain ⟨rfl, rfl⟩ := he; exact Or.inr ⟨rfl, hz⟩
    | cons U L1 => simp at he; obtain ⟨rfl, rfl⟩ := he; exact Or.inl ⟨L1, L2, rfl, hz⟩
  · rintro (⟨L1, L2, rfl, hz⟩ | ⟨rfl, hz⟩)
    · exact ⟨T :: L1, L2, rfl, hz⟩
    · exact ⟨[], L, rfl, hz⟩

/-- **`0` is left ahead of the last position exactly when the row's last token other than `000` is `100`** (or
there is none and the row was entered at `0`). -/
theorem fin_r0 (st : Rem) (L : List Tok) :
    fin st L = .r0 ↔ LastO L ∨ (st = .r0 ∧ ∀ T ∈ L, T = .z) := by
  induction L generalizing st with
  | nil =>
    simp only [fin, List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · exact Or.inr
    · rintro (⟨L1, L2, he, _⟩ | h)
      · simp at he
      · exact h
  | cons T L ih =>
    simp only [fin]
    rw [ih, lastO_cons]
    cases T <;> cases st <;> simp [Rem.next]

/-! ## Cascades leave tokens -/

theorem Blk.tok {n m : Nat} {w w' : List Bool} (hb : Blk n w w' (m + 1)) : ∃ T : Tok, w' = T.bits := by
  generalize hM : m + 1 = M at hb
  cases hb with
  | z0 k => exact ⟨.o, rfl⟩
  | z1 k => exact ⟨.z, rfl⟩
  | o0 k => exact ⟨.z, rfl⟩
  | o1 k => exact ⟨.o, rfl⟩
  | t0 k => exact ⟨.z, rfl⟩
  | t1 k => exact ⟨.o, rfl⟩
  | w0 k => exact ⟨.z, rfl⟩
  | w2 k => exact ⟨.o, rfl⟩
  | w1 => omega
  | p n => exact ⟨.w, rfl⟩
  | q n => exact ⟨.w, rfl⟩

/-- **A cascade leaves a row of tokens up to where it stopped.** -/
theorem Casc.tokens {n f : Nat} {s s' : Tape} {E : List Nat} (h : Casc n s s' f E) :
    ∃ L u, s' = app (toks L) u ∧ (toks L).length = f := by
  induction h with
  | fin _ => exact ⟨[], _, rfl, rfl⟩
  | @fwd n m f w w' t t' E hb _ ih =>
    obtain ⟨L, u, rfl, hl⟩ := ih
    obtain ⟨T, rfl⟩ := hb.tok
    refine ⟨T :: L, u, by rw [app_toks_cons], ?_⟩
    rw [show toks (T :: L) = T.bits ++ toks L from rfl, List.length_append, hb.len, hl]
  | e1 => exact ⟨[], _, rfl, rfl⟩
  | e _ ih => exact ih
  | d1 => exact ⟨[], _, rfl, rfl⟩
  | d _ ih => exact ih
  | u1 => exact ⟨[], _, rfl, rfl⟩

/-! ## On the run -/

/-- After round `r + 1` the stream `1 0 S` is `10` followed by tokens up to the stop `F`. -/
theorem reach_toks {r F : Nat} {S : Tape} (h : Reach (r + 1) S F) :
    ∃ L u, cons true (cons false S) = app (Rem.r10.bits ++ toks L) u ∧ F = 2 + (toks L).length := by
  generalize hr : r + 1 = r' at h
  cases h with
  | start => omega
  | next _ hc =>
    obtain ⟨L, u, rfl, hl⟩ := hc.tokens
    exact ⟨L, u, by simp [Rem.bits], by omega⟩

/-- **The next round never starts a block at the stop.** The block of round `r + 2` that holds the cell where
round `r + 1` stopped starts one or two cells before it (`endp + 1 = F` or `endp + 2 = F`), and every other block
starts at or before `endp` or at least 3 cells past it. -/
theorem never_at_stop {r F : Nat} {S : Tape} (h : Reach (r + 1) S F) :
    ∃ L, (endp .r10 L + 1 = F ∨ endp .r10 L + 2 = F) ∧
      ∀ n q, Starts n (cons true (cons false S)) q → q ≤ endp .r10 L ∨ endp .r10 L + 3 ≤ q := by
  obtain ⟨L, u, hs, hF⟩ := reach_toks h
  refine ⟨L, ?_, ?_⟩
  · have := endp_fin .r10 L
    have hb := fin_bits_pos .r10 L
    rw [show (Rem.r10.bits).length = 2 from rfl] at this
    omega
  · intro n q hq
    rcases shift hq .r10 L u hs with hp | hp
    · exact Or.inl hp.le
    · exact Or.inr hp

/-- **After a dirty stop, the next round halts at the cell before it only if the last token other than `000` is
`100`.** If round `r + 1` stopped at `F` leaving two adjacent 1s at `F` and `F + 1` (`010` hit once leaves `110`,
`011` hit once leaves `111`), a halt of round `r + 2` lies either at `F - 1`, where the block reads `011`, and then
the row of tokens before `F` ends in `100` followed by `000`s only, or at `F + 1` or beyond. -/
theorem dirty_next {r F p : Nat} {S : Tape} (h : Reach (r + 1) S F)
    (h0 : cons true (cons false S) F = true) (h1 : cons true (cons false S) (F + 1) = true)
    (hc : CascH 1 (cons true (cons false S)) p) :
    (p + 1 = F ∧ ∃ L u, cons true (cons false S) = app ([true, false] ++ toks L) u ∧ F = 2 + (toks L).length ∧
        LastO L) ∨ F + 1 ≤ p := by
  obtain ⟨L, u, hs, hF⟩ := reach_toks h
  have hu : ∀ i, u i = cons true (cons false S) (F + i) := by
    intro i; rw [hs, hF, ← app_app]
    have : 2 + (toks L).length + i = (Rem.r10.bits).length + ((toks L).length + i) := by simp [Rem.bits]; omega
    rw [this, app_at, app_at]
  have hu0 : u 0 = true := by rw [hu]; simpa using h0
  have hu1 : u 1 = true := by rw [hu]; exact h1
  have he := endp_fin .r10 L
  rw [show (Rem.r10.bits).length = 2 from rfl] at he
  rcases dirty hc .r10 L u hs hu0 hu1 with ⟨hf, hp⟩ | hp
  · left
    have hf1 : (fin .r10 L).bits.length = 1 := by rw [hf]; rfl
    refine ⟨by omega, L, u, hs, hF, ?_⟩
    rcases (fin_r0 .r10 L).mp hf with h' | ⟨h', _⟩
    · exact h'
    · cases h'
  · right; omega

end H173741
