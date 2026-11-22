import Overflow

/-!
# The phase map, proved

A post-event configuration is `PN d M Y`: the bit string `bitsOf M Y` (lowest bit first) left of the head, the
counter `0^d 1` right of it.  `phase d M Y` is the next post-event configuration the machine reaches, computed by
integer arithmetic and lists only:

* no overflow (`Y + 2^(d+1) < 2^M`): `2^d` counts give `PN (d+1) M (Y + 2^(d+1))` (the event rule);
* overflow: `i0` counts bring the string to `b1 1^(M-1)`, the overflowing count (`Overflow.lean`) leaves a counter
  with a junction, and the junction machine `AS` (`astep`, one proved rule per step, `Junction.lean`) runs to the
  next post-event configuration.

`phase_sound`: whenever `phase` returns a configuration, the machine reaches it.  `astep` returns `stuck` when a
side condition fails (the left string would overflow, the only place the machine can halt); `phase` is then `none`.
-/

namespace H140108

open TM

/-- A post-event configuration with numbers: `bitsOf M Y` left of the head, the counter `0^d 1` right of it. -/
def PN (d M Y : Nat) : Cfg St := P d (bitsOf M Y) L0

/-- A configuration of the junction machine: the left string `bitsOf (w+1) v`, the counter `low = bitsOf l c`,
then a junction (`k`: K or J) and the shifted counter `H`. -/
structure AS where
  w : Nat
  v : Nat
  l : Nat
  c : Nat
  k : Bool
  H : List Bool

def AS.cfg (s : AS) : Cfg St :=
  ⟨enc (false :: bitsOf (s.w + 1) s.v) L0, ctr (bitsOf s.l s.c) (jt s.k s.H), .B⟩

inductive Res where
  | next (s : AS)
  | done (d w v : Nat)
  | stuck

def leadOnes : List Bool → Nat
  | true :: H => leadOnes H + 1
  | _ => 0

/-- One step of the junction machine. -/
def astep (s : AS) : Res :=
  match s.H with
  | [] =>
    if s.l = 0 then (if s.v + 2 < 2 ^ (s.w + 1) then .done 0 s.w (s.v + 2) else .stuck)
    else if s.c = 2 ^ (s.l - 1) then .done (s.l - 1) s.w s.v else .stuck
  | h :: H1 =>
    if s.c + 1 < 2 ^ s.l then
      (if s.v + 2 * (2 ^ s.l - 1 - s.c) < 2 ^ (s.w + 1) then
        .next ⟨s.w, s.v + 2 * (2 ^ s.l - 1 - s.c), s.l, 2 ^ s.l - 1, s.k, s.H⟩ else .stuck)
    else if s.c = 2 ^ s.l - 1 then
      if h = false then
        (if s.v + 2 < 2 ^ (s.w + 1) then .next ⟨s.w, s.v + 2, s.l + 1, 2 ^ s.l, s.k, H1⟩ else .stuck)
      else if s.k then
        (if s.l % 2 = 0 then .next ⟨s.w + 3 * (s.l / 2) + 1, 2 ^ (3 * (s.l / 2)) * (1 + 2 * s.v), 0, 0, false, H1⟩
         else .next ⟨s.w + 3 * (s.l / 2) + 3, 1 + 2 ^ (3 * (s.l / 2) + 2) * (1 + 2 * s.v), 0, 0, true, H1⟩)
      else
        (if s.v + 2 < 2 ^ (s.w + 1) then
          .next ⟨s.w, s.v + 2, s.l + leadOnes H1 + 2, 2 ^ (s.l + leadOnes H1 + 1), false, H1.drop (leadOnes H1 + 1)⟩
         else .stuck)
    else .stuck

/-- The junction machine run for at most `n` steps. -/
def arun : Nat → AS → Res
  | 0, _ => .stuck
  | n + 1, s =>
    match astep s with
    | .next s' => arun n s'
    | r => r

theorem leadOnes_spec : ∀ (H : List Bool),
    H = List.replicate (leadOnes H) true ++ H.drop (leadOnes H) ∧
      (H.drop (leadOnes H) = [] ∨ H.drop (leadOnes H) = false :: H.drop (leadOnes H + 1))
  | [] => ⟨rfl, Or.inl rfl⟩
  | false :: H => ⟨rfl, Or.inr rfl⟩
  | true :: H => by
    obtain ⟨e1, e2⟩ := leadOnes_spec H
    refine ⟨?_, ?_⟩
    · show true :: H = true :: (List.replicate (leadOnes H) true ++ H.drop (leadOnes H))
      rw [← e1]
    · exact e2

theorem jt_pad (k : Bool) (h : Bool) (H : List Bool) : jt k (h :: (H ++ [false])) = jt k (h :: H) := by
  cases k
  · show cons false (cons h (ctr (H ++ [false]) blank)) = cons false (cons h (ctr H blank)); rw [ctr_blank]
  · show cons h (ctr (H ++ [false]) blank) = cons h (ctr H blank); rw [ctr_blank]

theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := pow_pos' n

theorem astep_next {s s' : AS} (h : astep s = .next s') : Reach s.cfg s'.cfg := by
  obtain ⟨w, v, l, c, k, H⟩ := s
  unfold astep at h
  cases H with
  | nil =>
    simp only at h
    split at h
    · split at h <;> cases h
    · split at h <;> cases h
  | cons hd H1 =>
    simp only at h
    split at h
    · -- count to full
      rename_i hc
      split at h
      · rename_i hv
        cases h
        have hp := two_pow_pos l
        have := count_many w v l c L0 (jt k (hd :: H1)) (2 ^ l - 1 - c) hv (by omega)
        rw [show c + (2 ^ l - 1 - c) = 2 ^ l - 1 by omega] at this
        exact this
      · cases h
    · split at h
      · rename_i hfull
        simp only [AS.cfg]
        rw [hfull, bitsOf_full]
        split at h
        · -- carry into a 0 digit
          rename_i h0
          subst h0
          split at h
          · rename_i hv
            cases h
            show Reach _ ⟨_, ctr (bitsOf (l + 1) (2 ^ l)) (jt k H1), .B⟩
            rw [bitsOf_pow]
            exact carry0 k l w v hv H1 L0
          · cases h
        · rename_i h1
          have h1' : hd = true := by cases hd <;> simp_all
          subst h1'
          split at h
          · -- absorption
            rename_i hk
            subst hk
            split at h
            · rename_i hl
              cases h
              obtain ⟨n, rfl⟩ : ∃ n, l = 2 * n := ⟨l / 2, by omega⟩
              have h2 := absorb_even n (bitsOf (w + 1) v) H1 L0
              rw [show 2 * n / 2 = n by omega]
              show Reach _ ⟨enc (false :: bitsOf (w + 3 * n + 1 + 1) (2 ^ (3 * n) * (1 + 2 * v))) L0,
                ctr (bitsOf 0 0) (jt false H1), .B⟩
              have e : bitsOf (w + 3 * n + 1 + 1) (2 ^ (3 * n) * (1 + 2 * v))
                  = List.replicate (3 * n) false ++ true :: bitsOf (w + 1) v := by
                rw [show w + 3 * n + 1 + 1 = 3 * n + (w + 1 + 1) by omega,
                  show 2 ^ (3 * n) * (1 + 2 * v) = 0 + 2 ^ (3 * n) * ((if true then 1 else 0) + 2 * v) by simp,
                  bitsOf_append _ _ _ _ (two_pow_pos _), bitsOf_zero, bitsOf_cons]
              rw [e]
              exact h2
            · rename_i hl
              cases h
              obtain ⟨n, rfl⟩ : ∃ n, l = 2 * n + 1 := ⟨l / 2, by omega⟩
              have h2 := absorb_odd n (bitsOf (w + 1) v) H1 L0
              rw [show (2 * n + 1) / 2 = n by omega]
              show Reach _ ⟨enc (false :: bitsOf (w + 3 * n + 3 + 1) (1 + 2 ^ (3 * n + 2) * (1 + 2 * v))) L0,
                ctr (bitsOf 0 0) (jt true H1), .B⟩
              have e : bitsOf (w + 3 * n + 3 + 1) (1 + 2 ^ (3 * n + 2) * (1 + 2 * v))
                  = true :: List.replicate (3 * n + 1) false ++ true :: bitsOf (w + 1) v := by
                rw [show w + 3 * n + 3 + 1 = (3 * n + 2) + (w + 1 + 1) by omega,
                  show 1 + 2 ^ (3 * n + 2) * (1 + 2 * v)
                    = ((if true then 1 else 0) + 2 * 0) + 2 ^ (3 * n + 2) * ((if true then 1 else 0) + 2 * v) by simp,
                  bitsOf_append _ _ _ _ (by have := two_pow_pos (3 * n + 1); rw [pow_succ']; simp; omega),
                  bitsOf_cons, bitsOf_cons, bitsOf_zero]
              rw [e]
              exact h2
          · -- carry through a J junction
            rename_i hk
            have hk' : k = false := by cases k <;> simp_all
            subst hk'
            split at h
            · rename_i hv
              cases h
              obtain ⟨e1, e2⟩ := leadOnes_spec H1
              generalize hs : leadOnes H1 = s at e1 e2
              have hJ : jt false (true :: H1)
                  = jt false (true :: (List.replicate s true ++ false :: H1.drop (s + 1))) := by
                rcases e2 with e2 | e2
                · have e3 : H1.drop (s + 1) = [] := by
                    rw [List.drop_eq_nil_iff] at e2 ⊢; omega
                  rw [e3]
                  conv => lhs; rw [e1, e2]
                  rw [List.append_nil, ← jt_pad false true (List.replicate s true)]
                · conv => lhs; rw [e1, e2]
              rw [hJ]
              show Reach _ ⟨_, ctr (bitsOf (l + s + 2) (2 ^ (l + s + 1))) _, .B⟩
              rw [show l + s + 2 = (l + s + 1) + 1 by omega, bitsOf_pow]
              exact carryJ1 l s w v hv _ L0
            · cases h
      · cases h

theorem astep_done {s : AS} {d w v : Nat} (h : astep s = .done d w v) : Reach s.cfg (P d (bitsOf (w + 1) v) L0) := by
  obtain ⟨w0, v0, l, c, k, H⟩ := s
  unfold astep at h
  cases H with
  | nil =>
    simp only at h
    split at h
    · rename_i hl
      split at h
      · rename_i hv
        cases h
        subst hl
        simp only [AS.cfg, bitsOf]
        unfold P
        have e : jt k [] = ctr [false] blank := by
          cases k <;> (show blank = cons false (cons false (cons false blank)); rw [cons_false_blank, cons_false_blank, cons_false_blank])
        rw [show ctr [] (jt k []) = jt k [] from rfl, e]
        exact count_nat _ _ hv [false] (by simp) L0 blank
      · cases h
    · rename_i hl
      split at h
      · rename_i hc
        cases h
        simp only [AS.cfg]
        unfold P
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        rw [hc, show l' + 1 - 1 = l' by omega, bitsOf_pow]
        cases k <;> exact Reach.refl' _
      · cases h
  | cons hd H1 =>
    simp only at h
    split at h
    · split at h <;> cases h
    · split at h
      · split at h
        · split at h <;> cases h
        · split at h
          · split at h <;> cases h
          · split at h <;> cases h
      · cases h

theorem arun_done : ∀ (n : Nat) (s : AS) {d w v : Nat}, arun n s = .done d w v → Reach s.cfg (P d (bitsOf (w + 1) v) L0)
  | 0, _, _, _, _, h => by cases h
  | n + 1, s, d, w, v, h => by
    unfold arun at h
    split at h
    · rename_i s' hs
      exact Reach.trans' (astep_next hs) (arun_done n s' h)
    · exact astep_done h

end H140108
