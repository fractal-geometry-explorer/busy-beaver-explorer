"""mkU.py PR93.v OUT.v MACHINE START K [fast]
Proof that MACHINE halts, where MACHINE is (up to renaming / mirroring) U = 1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LE_0RA---,
i.e. PR 93's table T3 = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB--- with
  (1) F merged into E (E1 = 0LE: T3's E1 0LF and F's 0LB/0L. are the same moves) and
  (2) D0 = 1RA replaced by the detour D0 1LF, F0 0RA, A1 1RA, which ends where 1RA ends, or halts (F1) when the cell left of
      the head is 1.
The engine runs on W = T3 with F1 := 0LF (no halting transition; all of PR 93's macro rules hold for W unchanged, since they
never use F1), and its raw step stops (None) on a D0 whose left neighbour is 1. Soundness of None is `HaltsU c` =
`halts U (pS c)`; W-steps transport to U by the lemma det_step."""
import sys
src=open(sys.argv[1]).read(); out=sys.argv[2]; M=sys.argv[3]; START=sys.argv[4]; K=sys.argv[5]
fast=len(sys.argv)>6 and sys.argv[6]=='fast'
def rep(a,b,count=1):
    global src
    n=src.count(a); assert n==count,(n,a[:90]); src=src.replace(a,b)
W='1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF'; U='1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LE_0RA---'
rep('Definition tm : TM := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---".','Definition tm : TM := TM_from_str "%s".'%M)
rep('(TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---")','(TM_from_str "%s")'%W)
# --- the transport part: replaces permState .. evstep_halts
i=src.index('Definition permState'); j=src.index('(* ==========', src.index('Lemma evstep_halts'))
if M=='1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF':   # U from A, E and F exchanged, no mirror
    ISO='''Definition permU (q : Q) : Q := match q with E => F | F => E | q => q end.
Lemma perm_U : Perm ut tm permU.
Proof.
  split.
  - intros q s H. destruct q, s; cbv in H |- *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q, s; cbv in H |- *; inversion H; subst; reflexivity.
Qed.
Lemma haltsU_iso : halts ut (A;; tape0) -> halts tm c0.
Proof. intros H. exact (perm_halts _ _ _ _ _ perm_U H). Qed.
'''
elif M=='1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF':  # U from C, mirrored
    ISO='''Definition permU (q : Q) : Q := match q with A => D | B => E | C => A | D => B | E => F | F => C end.
Lemma perm_U : Perm (flip ut) tm permU.
Proof.
  split.
  - intros q s H. destruct q, s; cbv in H |- *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q, s; cbv in H |- *; inversion H; subst; reflexivity.
Qed.
Lemma haltsU_iso : halts ut (C;; tape0) -> halts tm c0.
Proof.
  intros H. apply flip_halts in H.
  change (flip_conf (C;; tape0)) with (C;; tape0) in H.
  exact (perm_halts _ _ _ _ _ perm_U H).
Qed.
'''
else: raise SystemExit('unknown machine')
TR='''Definition ut : TM := Eval compute in (TM_from_str "%s").
(* src_tm (W) is ut with F merged into E, and with D0 = 1RA where ut has the detour D0 1LF, F0 0RA, A1 1RA. *)
Definition pS (q : Q) : Q := match q with F => E | q => q end.
Definition pSc (c : Q * tape) : Q * tape := let '(q, t) := c in (pS q, t).
Definition HaltsU (c : Q * tape) : Prop := halts ut (pSc c).

%s
Lemma u_halts_step c c' : c -[ ut ]-> c' -> halts ut c' -> halts ut c.
Proof.
  intros H [n [ch [Hm Hh]]]. exists (S n), ch. split; [econstructor; eauto | exact Hh].
Qed.
Lemma u_halted_halts c : halted ut c -> halts ut c.
Proof. intros H. exists 0%%nat, c. split; [constructor | exact H]. Qed.

Lemma det_step c c' : c -[ src_tm ]-> c' -> HaltsU c' -> HaltsU c.
Proof.
  unfold HaltsU. intros Hs IH.
  inversion Hs as [q0 q1 s0 s1 l0 r0 Ht | q0 q1 s0 s1 l0 r0 Ht]; subst;
  destruct q0, s0; cbv in Ht; inversion Ht; subst; cbn [pSc pS] in IH |- *;
  try (eapply u_halts_step; [ solve [ constructor; reflexivity ] | exact IH ]).
  (* D reading 0 *)
  destruct l0 as [x l'].
  destruct x.
  + eapply u_halts_step; [ eapply step_left; reflexivity |].
    eapply u_halts_step; [ eapply step_right; reflexivity |].
    eapply u_halts_step; [ eapply step_right; reflexivity |].
    exact IH.
  + eapply u_halts_step; [ eapply step_left; reflexivity |].
    apply u_halted_halts. reflexivity.
Qed.

Lemma ev_trans c1 c2 c3 : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof.
  induction 1; eauto.
Qed.

Lemma evstep_halts c c' : c -->* c' -> HaltsU c' -> HaltsU c.
Proof.
  induction 1 as [c | c c1 c2 H1 _ IH]; [auto |].
  intros H2. exact (det_step _ _ H1 (IH H2)).
Qed.

Lemma src_total q s : src_tm (q, s) = None -> False.
Proof. destruct q, s; cbv; discriminate. Qed.

Lemma haltsU_D0 l r : HaltsU (D;; (1 >> l) {{0}} r).
Proof.
  unfold HaltsU; cbn [pSc pS].
  eapply u_halts_step; [ eapply step_left; reflexivity |].
  apply u_halted_halts. reflexivity.
Qed.

'''%(U,ISO)
src=src[:i]+TR+src[j:]
src=src.replace('halts src_tm','HaltsU')
# raw step: stop on D0 with left neighbour 1
rep('''  match src_tm (q, b) with
  | Some (b', L, q') =>
    Some (MkFastState l' (MkRTape (runs_push (SW_raw [b']) 1 (r_raw rt')) (d_front rt') (d_back rt') (r_tail rt')) (RAW q' L))''',
'''  if (match q, b, fst (runs_pop l') with D, S0, S1 => true | _, _, _ => false end) then None else
  match src_tm (q, b) with
  | Some (b', L, q') =>
    Some (MkFastState l' (MkRTape (runs_push (SW_raw [b']) 1 (r_raw rt')) (d_front rt') (d_back rt') (r_tail rt')) (RAW q' L))''')
old_spec=src[src.index('Lemma rawStep_spec'):src.index('Definition toRawAndStep')]
new_spec='''Lemma rawStep_spec l rt q d :
  match rawStep l rt q d with
  | Some s' => fs_denote (MkFastState l rt (RAW q d)) -->* fs_denote s'
  | None => HaltsU (fs_denote (MkFastState l rt (RAW q d)))
  end.
Proof.
  destruct d; unfold rawStep; cbn [fs_denote fs_L fs_R fs_mode].
  - pose proof (runs_pop_spec l) as Hp.
    destruct (runs_pop l) as [b l']; cbn [fst snd] in Hp.
    rewrite Hp; cbn [hd tl].
    pose proof (runs_pop_spec l') as Hp'.
    destruct (runs_pop l') as [x l'']; cbn [fst snd] in Hp' |- *.
    destruct (match q, b, x with D, S0, S1 => true | _, _, _ => false end) eqn:Hd.
    { destruct q, b, x; try discriminate. rewrite Hp'. apply haltsU_D0. }
    destruct (src_tm (q, b)) as [[[b' [|]] q']|] eqn:E.
    + cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_left E) | apply evstep_refl].
    + cbn [fs_denote fs_L fs_R fs_mode].
      rewrite runs_push_spec. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_right E) | apply evstep_refl].
    + exfalso. exact (src_total _ _ E).
  - pose proof (popBitRTape_spec rt) as Hp.
    destruct (popBitRTape rt) as [b rt']; cbn [fst snd] in Hp.
    rewrite Hp; cbn [hd tl].
    pose proof (runs_pop_spec l) as Hp'.
    destruct (runs_pop l) as [x l'']; cbn [fst snd] in Hp' |- *.
    destruct (match q, b, x with D, S0, S1 => true | _, _, _ => false end) eqn:Hd.
    { destruct q, b, x; try discriminate. rewrite Hp'. apply haltsU_D0. }
    destruct (src_tm (q, b)) as [[[b' [|]] q']|] eqn:E.
    + cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_left E) | apply evstep_refl].
    + cbn [fs_denote fs_L fs_R fs_mode].
      rewrite runs_push_spec. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_right E) | apply evstep_refl].
    + exfalso. exact (src_total _ _ E).
Qed.

'''
src=src.replace(old_spec,new_spec)
# remove the old halted_halts / ev_trans / evstep_halts if still present after the cut (they were inside i..j)
src=src.replace('Module M598.','Module HU.').replace('End M598.','End HU.').replace('M598.','HU.')
init='init'+START
src=src.replace('Definition initFastC : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW C R).',
                'Definition %s : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW %s R).'%(init,START))
src=src.replace('initFastC',init).replace('(C;; tape0)','(%s;; tape0)'%START).replace('run_pow 22','run_pow %s'%K).replace('run_pow_spec 22','run_pow_spec %s'%K)
rep('Lemma src_halt : HaltsU (%s;; tape0).'%START,'Lemma src_halt : halts ut (%s;; tape0).'%START)
rep('Proof. exact (HU.halts_iso HU.src_halt). Qed.','Proof. exact (HU.haltsU_iso HU.src_halt). Qed.')
if fast: src=src.replace('Proof. vm_check_eq. Qed.','Admitted.')
src=src.rstrip('\n')+'\n\nPrint Assumptions halt.\n'
open(out,'w').write(src)
