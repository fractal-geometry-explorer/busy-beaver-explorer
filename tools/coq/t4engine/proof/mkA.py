"""Turn H155900.v (T4 started in B) into H181655.v: 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE halts.
That machine is the T4 table (1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---) with E and F exchanged and D0 = 1RA replaced
by the detour 1LE, E0 = 0RA, A1 = 1RA, which ends where 1RA ends or halts (E1). So T4 halting from A implies it halts.
usage: mkA.py H155900.v OUT.v [fast]"""
import sys
s = open(sys.argv[1]).read()
def rep(a, b, count=1):
    global s
    n = s.count(a); assert n == count, (n, a[:80]); s = s.replace(a, b)
rep('Definition tm : TM := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---".',
    'Definition tm : TM := TM_from_str "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE".')
i = s.index('Definition permState'); j = s.index('Lemma halted_halts')
DET = '''(* tm is src_tm with E and F exchanged, except D0: src_tm has 1RA, tm has the detour
   D0 1LE, E0 0RA, A1 1RA, which ends in the same configuration when the cell left of the head is 0
   and halts (E1) when it is 1. So every halt of src_tm is a halt of tm. *)
Definition pS (q : Q) : Q := match q with E => F | F => E | q => q end.

Lemma det_halts_step c c' : c -[ tm ]-> c' -> halts tm c' -> halts tm c.
Proof.
  intros H [n [ch [Hm Hh]]]. exists (S n), ch. split; [econstructor; eauto | exact Hh].
Qed.

Lemma det_halted_halts c : halted tm c -> halts tm c.
Proof. intros H. exists 0%nat, c. split; [constructor | exact H]. Qed.

Lemma detour n : forall q t, halts_in src_tm (q;; t) n -> halts tm (pS q;; t).
Proof.
  induction n as [|n IH]; intros q t [ch [Hm Hh]].
  - inversion Hm; subst. apply det_halted_halts.
    destruct t as [[l s] r]. destruct q, s; cbv in Hh |- *; congruence.
  - inversion Hm as [|n0 c1 c' c2 Hs Hm']; subst.
    destruct c' as [q' t'].
    assert (IH' : halts tm (pS q';; t')) by (apply IH; exists ch; auto).
    clear IH Hm Hm'.
    destruct t as [[l s] r].
    inversion Hs as [q0 q1 s0 s1 l0 r0 Ht | q0 q1 s0 s1 l0 r0 Ht]; subst;
    destruct q, s; cbv in Ht; inversion Ht; subst;
    try (eapply det_halts_step; [ solve [ constructor; reflexivity ] | exact IH' ]).
    (* D reading 0 *)
    destruct l as [x l'].
    destruct x.
    + eapply det_halts_step; [ eapply step_left; reflexivity |].
      eapply det_halts_step; [ eapply step_right; reflexivity |].
      eapply det_halts_step; [ eapply step_right; reflexivity |].
      exact IH'.
    + eapply det_halts_step; [ eapply step_left; reflexivity |].
      apply det_halted_halts. reflexivity.
Qed.

Lemma halts_iso : halts src_tm (A;; tape0) -> halts tm c0.
Proof. intros [n H]. exact (detour n A tape0 H). Qed.
'''
s = s[:i] + DET + s[j:]
s = s.replace('Module H155900.', 'Module H181655.').replace('End H155900.', 'End H181655.').replace('H155900.', 'H181655.')
rep('Definition initFastB : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW B R).',
    'Definition initFastA : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW A R).')
s = s.replace('initFastB', 'initFastA')
rep('(B;; tape0)', '(A;; tape0)', 2)
if len(sys.argv) > 3 and sys.argv[3] == 'fast':
    s = s.replace('Lemma run_ok : is_none (run_pow 19 initFastA) = true.\nProof. vm_check_eq. Qed.',
                  'Lemma run_ok : is_none (run_pow 19 initFastA) = true.\nAdmitted.')   # input may already be fast
open(sys.argv[2], 'w').write(s)
