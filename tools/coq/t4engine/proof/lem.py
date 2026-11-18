"""Second pass over H155900.v: restate the four changed base rules and redo the lemmas and specs built on them."""
import re,sys
p=sys.argv[1]; s=open(p).read()
R=[
("""Lemma rule_collision l r : CfgL (l <* [0; 0; 1; 1; 0; 1]) r -->* CfgJ l ([1; 1; 1; 1] *> r).""",
 """Lemma rule_collision l r : CfgL (l <* [0; 0; 1; 1; 0; 1]) r -->* CfgL l ([1; 1; 1; 1; 1; 1] *> r)."""),
("""Lemma rule_finishP l r b : CfgL (l <* S_word 0 <* [0; 1] <* [1; 0]^^(1 + b)) r -->*
  CfgJ l (D_word (1 + b) *> r).""","""Lemma rule_finishP l r b : CfgL (l <* S_word 0 <* [0; 1] <* [1; 0]^^(1 + b)) r -->*
  CfgL l (D_word (2 + b) *> r)."""),
("""Lemma rule_defect0 l r m : CfgR l ([1; 0] *> D_word 0 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgJ l ([1; 1; 1; 1] *> D_word m *> [1] *> r).""","""Lemma rule_defect0 l r m : CfgR l ([1; 0] *> D_word 0 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgL l ([1; 1; 1; 1; 1; 1] *> D_word m *> [1] *> r)."""),
("""Lemma rule_collide l r : CfgR l ([1; 0] *> D_word 0 *> D_word 0 *> r) -->*
  CfgJ l (D_word 2 *> [1; 0] *> r).""","""Lemma rule_collide l r : CfgR l ([1; 0] *> D_word 0 *> D_word 0 *> r) -->*
  CfgL l (D_word 3 *> [1; 0] *> r)."""),
]
for a,b in R:
    assert s.count(a)==1,a[:60]; s=s.replace(a,b)
def lemma(name):
    m=re.search(r'^Lemma '+re.escape(name)+r'\b.*?^Qed\.\n', s, flags=re.S|re.M)
    assert m, name; return m
def repl(name,new):
    global s
    m=lemma(name); s=s[:m.start()]+new.strip('\n')+'\n'+s[m.end():]
repl('call_collision0','''Lemma call_collision0 j r :
  call (D_word j *> [1; 0] *> D_word 0 *> D_word 0 *> r)
       (D_word j *> D_word 3 *> [1; 0] *> r).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply rule_collide |].
  apply rule_left.
Qed.''')
repl('calls_collision','''Lemma calls_collision k j r :
  calls (1 + k)
    (D_word j *> [1; 0] *> (D_word 0)^^((1 + k) * 2) *> r)
    (D_word j *> (D_word 3)^^(1 + k) *> [1; 0] *> r).
Proof.
  gen j. induction k as [|k IH]; intros j.
  - change ((1 + 0) * 2)%nat with 2%nat.
    cbn [lpow]. rewrite ?app_nil_r, !Str_app_assoc.
    eapply calls_S; [apply call_collision0 | constructor].
  - replace ((1 + S k) * 2)%nat with (2 + (1 + k) * 2)%nat by lia.
    rewrite lpow_add, !Str_app_assoc.
    replace ((D_word 0)^^2) with (D_word 0 ++ D_word 0)
      by (cbn [lpow]; rewrite ?app_nil_r; reflexivity).
    rewrite ?Str_app_assoc.
    eapply calls_S; [apply call_collision0 |].
    pose proof (calls_D_pow j 1 (IH 3%nat)) as H.
    cbn [lpow] in H. rewrite ?app_nil_r in H.
    replace ((D_word 3)^^(1 + S k)) with (D_word 3 ++ (D_word 3)^^(1 + k)) by reflexivity.
    rewrite Str_app_assoc. exact H.
Qed.''')
repl('returnP_L','''Lemma returnP_L {n r s} (H : calls (1 + n * 2) r s) l :
  CfgL (PL_word (1 + n * 3) *> l) r -->* CfgL l (D_word (6 + n * 3) *> s).
Proof.
  rewrite pl_decomp.
  change (6 + n * 3)%nat with (2 + (4 + n * 3))%nat.
  change (5 + n * 3)%nat with (1 + (4 + n * 3))%nat.
  eapply ev_trans; [apply (loopL H) |].
  apply rule_finishP.
Qed.''')
repl('returnP_J','''Lemma returnP_J {n r s} (H : calls (1 + n * 2) r s) l :
  CfgJ (PL_word (1 + n * 3) *> l) r -->* CfgL l (D_word (7 + n * 3) *> s).
Proof.
  rewrite pl_decomp.
  eapply ev_trans; [apply (loopJ H _ (5 + n * 3)) |].
  change (7 + n * 3)%nat with (2 + (5 + n * 3))%nat.
  apply rule_finishP.
Qed.''')
repl('returnsP_J','''Lemma returnsP_L0 k n {r s} (H : calls (k * (1 + n * 2)) r s) l :
  CfgL ((PL_word (1 + n * 3))^^k *> l) r -->* CfgL l ((D_word (6 + n * 3))^^k *> s).
Proof.
  gen r s l. induction k as [|k IH]; intros r s H l; cbn [Nat.mul] in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (calls_split (1 + n * 2) (k * (1 + n * 2)) H) as [u [Hu Hv]].
    cbn [lpow]. rewrite Str_app_assoc.
    eapply ev_trans; [apply (returnP_L Hu) |].
    pose proof (calls_D_pow (6 + n * 3) 1 Hv) as Hv'.
    cbn [lpow] in Hv'. rewrite ?app_nil_r in Hv'.
    eapply ev_trans; [apply (IH _ _ Hv') |].
    rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma returnsP_J k n {r s} (H : calls ((1 + k) * (1 + n * 2)) r s) l :
  CfgJ ((PL_word (1 + n * 3))^^(1 + k) *> l) r -->*
  CfgL l ((D_word (6 + n * 3))^^k *> D_word (7 + n * 3) *> s).
Proof.
  cbn [Nat.add Nat.mul] in H.
  destruct (calls_split (1 + n * 2) (k * (1 + n * 2)) H) as [u [Hu Hv]].
  cbn [Nat.add lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply (returnP_J Hu) |].
  pose proof (calls_D_pow (7 + n * 3) 1 Hv) as Hv'.
  cbn [lpow] in Hv'. rewrite ?app_nil_r in Hv'.
  exact (returnsP_L0 k n Hv' l).
Qed.''')
repl('returnsP_L','''Lemma returnsP_L k n {r s} (H : calls ((1 + k) * (1 + n * 2)) r s) l :
  CfgL ((PL_word (1 + n * 3))^^(1 + k) *> l) r -->*
  CfgL l ((D_word (6 + n * 3))^^(1 + k) *> s).
Proof. exact (returnsP_L0 (1 + k) n H l). Qed.''')
repl('rule_collisionD','''Lemma rule_collisionD l r n :
  CfgL ([0; 0; 1; 1; 0; 1] *> l) (D_word n *> r) -->*
  CfgL l (D_word (3 + n) *> r).
Proof.
  replace (D_word (3 + n) *> r) with ([1; 1; 1; 1; 1; 1] *> D_word n *> r)
    by (unfold D_word; cbn [Nat.add lpow app Str_app]; reflexivity).
  apply rule_collision.
Qed.''')
repl('rule_defect0D','''Lemma rule_defect0D l r m :
  CfgR l ([1; 0] *> D_word 0 *> D_word m *> r) -->*
  CfgL l (D_word (3 + m) *> [1; 0] *> r).
Proof.
  replace (D_word m *> r) with ([1] *> [1; 1]^^m *> [0] *> ([0] *> r))
    by (unfold D_word; rewrite ?Str_app_assoc; reflexivity).
  replace (D_word (3 + m) *> [1; 0] *> r)
    with ([1; 1; 1; 1; 1; 1] *> D_word m *> [1] *> ([0] *> r))
    by (unfold D_word; cbn [Nat.add lpow app Str_app]; rewrite ?Str_app_assoc; reflexivity).
  apply rule_defect0.
Qed.''')
repl('call_defect0','''Lemma call_defect0 j m r :
  call (D_word j *> [1; 0] *> D_word 0 *> D_word m *> r)
       (D_word j *> D_word (3 + m) *> [1; 0] *> r).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply rule_defect0D |].
  apply rule_left.
Qed.''')
repl('def_k0_ML','''Lemma def_k0_ML {a} (Ha : (1 <= a)%nat) l r :
  CfgL (DefWord a 0 *> l) r -->* CfgL l (D_word (1 + a) *> r).
Proof.
  replace a with (1 + (a - 1))%nat by lia.
  unfold DefWord. cbn [lpow app]. rewrite !Str_app_assoc.
  replace (1 + (1 + (a - 1)))%nat with (2 + (a - 1))%nat by lia.
  apply rule_finishP.
Qed.''')
repl('rule_mr_a0_DEF','Lemma rule_mr_a0_DEF {la lk} (Hla : (1 <= la)%nat) (Hlk : (3 <= lk)%nat) m l r :\n  CfgR (DefWord la lk *> l) ([1; 0] *> D_word 0 *> D_word m *> r) -->*\n  CfgR (S_word (m + 3) *> DefWord la (lk - 3) *> l) ([1; 0] *> r).\nProof.\n  eapply ev_trans; [apply rule_defect0D |].\n  replace (3 + m)%nat with (m + 3)%nat by lia.\n  eapply ev_trans; [exact (def_restart Hla Hlk l _) |].\n  apply rule_right.\nQed.')
repl('rule_mr_a0_S_DEF','Lemma rule_mr_a0_S_DEF {la lk} (Hla : (1 <= la)%nat) (Hlk : (3 <= lk)%nat) sn m l r :\n  CfgR (S_word sn *> DefWord la lk *> l) ([1; 0] *> D_word 0 *> D_word m *> r) -->*\n  CfgR (S_word (m + 3) *> S_word sn *> DefWord la (lk - 3) *> l) ([1; 0] *> r).\nProof.\n  eapply ev_trans; [apply rule_defect0D |].\n  replace (3 + m)%nat with (m + 3)%nat by lia.\n  eapply ev_trans; [apply rule_left |].\n  eapply ev_trans; [exact (def_restart Hla Hlk l _) |].\n  eapply ev_trans; [apply rule_right | apply rule_right].\nQed.')
open(p,'w').write(s)

def edit(name, pairs):
    global s
    m=lemma(name); t=m.group(0)
    for a,b,c in pairs:
        assert t.count(a)==c,(name,a,t.count(a)); t=t.replace(a,b)
    s=s[:m.start()]+t+s[m.end():]
J1="        replace (N.to_nat (j + 1)%N) with (1 + N.to_nat j)%nat by lia.\n"
edit('doCallsDSlow_spec',[(J1,'',2),("replace (N.to_nat (m + 2)%N) with (2 + N.to_nat m)%nat by lia.","replace (N.to_nat (m + 3)%N) with (3 + N.to_nat m)%nat by lia.",1)])
edit('doCallsD_spec',[("    replace (N.to_nat (j + 1)%N) with (1 + N.to_nat j)%nat by lia.\n",'',1)])
open(p,'w').write(s)
edit('trySweepMR_a0_spec',[
 ("replace (N.to_nat (m + 2)%N) with (N.to_nat m + 2)%nat by lia.","replace (N.to_nat (m + 3)%N) with (N.to_nat m + 3)%nat by lia.",4),
 ("      replace (N.to_nat (sn + 1)%N) with (N.to_nat sn + 1)%nat by lia.\n","",2),
 ("replace (N.to_nat (pln + 5)%N) with ((N.to_nat pln + 4) + 1)%nat by lia.","replace (N.to_nat (pln + 4)%N) with (N.to_nat pln + 4)%nat by lia.",1),
 ("    replace (N.to_nat (la + 1)%N) with (N.to_nat la + 1)%nat by lia.\n","",1),
 ("""    cbv beta iota zeta delta [trySweepMR_a0].
    destruct (N.leb_spec 3 lk) as [Hlk3 | _]; [| discriminate].""","""    cbv beta iota zeta delta [trySweepMR_a0].
    destruct (if N.leb 1 la then N.leb 3 lk else false) eqn:Hc; [| discriminate].
    destruct (N.leb_spec 1 la) as [Hla1 | _]; [| discriminate].
    destruct (N.leb_spec 3 lk) as [Hlk3 | _]; [| discriminate].""",1)])
open(p,'w').write(s)
m=lemma('rule_defect0D')
s=s[:m.end()]+'''
Lemma rule_defect0' l r m : CfgR l ([1; 0] *> D_word 0 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgL l (D_word (m + 3) *> [1] *> r).
Proof.
  replace (D_word (m + 3) *> [1] *> r) with ([1; 1; 1; 1; 1; 1] *> D_word m *> [1] *> r)
    by (replace (m + 3)%nat with (3 + m)%nat by lia; unfold D_word; cbn [Nat.add lpow app Str_app]; rewrite ?Str_app_assoc; reflexivity).
  apply rule_defect0.
Qed.
'''+s[m.end():]
edit('stepMR_imm_spec',[
 ("replace (N.to_nat (m + 2)%N) with (2 + N.to_nat m)%nat by lia.","replace (N.to_nat (m + 3)%N) with (3 + N.to_nat m)%nat by lia.",1),
 ("""          rewrite !lpow_1. apply rule_defect0. }""","""          rewrite !lpow_1.
          replace (N.to_nat (c1 / 2 + 3)%N) with (N.to_nat (c1 / 2)%N + 3)%nat by lia.
          apply rule_defect0'. }""",1)])
open(p,'w').write(s)
edit('def_rem_ML_spec',[
 ("    if N.eqb rem 0 then (true, pushD a 1 df)","    if N.eqb rem 0 then (false, pushD (a + 1)%N 1 df)",1),
 ("""    exact (def_k0_ML Ha _ _).""","""    replace (N.to_nat (a + 1)%N) with (1 + N.to_nat a)%nat by lia.
    exact (def_k0_ML Ha _ _).""",1)])
edit('handleDefInSweep_spec',[
 ("            replace (a + 1 - 1)%N with a in Hstep2 by lia.\n","            replace (a + 1 - 1)%N with a in Hstep2 by lia.\n            replace (a + 1 + 1)%N with (a + 2)%N in Hstep2 by lia.\n",1)])
open(p,'w').write(s)
edit('sweepLeftOne_spec',[("""      * (* MJ *)
        rewrite denD_pushD.
        replace (N.to_nat cnt1) with (N.to_nat mc + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
        rewrite lpow_add, Str_app_assoc, Hpln.
        replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat req) with (N.to_nat mc * (1 + N.to_nat n * 2))%nat in Hcalls
          by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
        exact (returnsP_J (N.to_nat mc) (N.to_nat n) Hcalls _).
      * (* ML *)
        rewrite !denD_pushD.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat cnt1) with ((1 + N.to_nat (mc - 1)%N) + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
        rewrite lpow_add, Str_app_assoc, Hpln.
        replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat (5 + n * 3)%N) with (5 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat req) with ((1 + N.to_nat (mc - 1)%N) * (1 + N.to_nat n * 2))%nat in Hcalls
          by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
        exact (returnsP_L (N.to_nat (mc - 1)%N) (N.to_nat n) Hcalls _).""","""      * (* MJ *)
        rewrite !denD_pushD.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat cnt1) with ((1 + N.to_nat (mc - 1)%N) + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
        rewrite lpow_add, Str_app_assoc, Hpln.
        replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat (7 + n * 3)%N) with (7 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat req) with ((1 + N.to_nat (mc - 1)%N) * (1 + N.to_nat n * 2))%nat in Hcalls
          by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
        exact (returnsP_J (N.to_nat (mc - 1)%N) (N.to_nat n) Hcalls _).
      * (* ML *)
        rewrite denD_pushD.
        replace (N.to_nat cnt1) with (N.to_nat mc + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
        rewrite lpow_add, Str_app_assoc, Hpln.
        replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat req) with (N.to_nat mc * (1 + N.to_nat n * 2))%nat in Hcalls
          by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
        exact (returnsP_L0 (N.to_nat mc) (N.to_nat n) Hcalls _).""",1)])
open(p,'w').write(s)
edit('sweepLeftBlankDef1_spec',[("""        replace (a + 1 - 1)%N with a in Hstep2 by lia.
""","""        replace (a + 1 - 1)%N with a in Hstep2 by lia.
        replace (a + 1 + 1)%N with (a + 2)%N in Hstep2 by lia.
""",1)])
open(p,'w').write(s)
edit('sweepLeftBlank_spec',[("""        { rewrite denD_pushD.
          replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
          replace (N.to_nat req) with (N.to_nat cnt1 * (1 + N.to_nat n * 2))%nat in Hcalls
            by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
          exact (returnsP_J (N.to_nat cnt1) (N.to_nat n) Hcalls _). }
        { unfold cnt1 in *; rewrite !denD_pushD, (pos_to_nat_succ pc).
          change (N.to_nat 1) with 1%nat. rewrite lpow_1.
          replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
          replace (N.to_nat (5 + n * 3)%N) with (5 + N.to_nat n * 3)%nat by lia.
          change (S (N.to_nat (N.pred (Npos pc)))) with (1 + N.to_nat (N.pred (Npos pc)))%nat.
          replace (N.to_nat req) with ((1 + N.to_nat (N.pred (Npos pc))) * (1 + N.to_nat n * 2))%nat in Hcalls
            by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
          exact (returnsP_L (N.to_nat (N.pred (Npos pc))) (N.to_nat n) Hcalls _). }""","""        { unfold cnt1 in *; rewrite !denD_pushD, (pos_to_nat_succ pc).
          change (N.to_nat 1) with 1%nat. rewrite lpow_1.
          replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
          replace (N.to_nat (7 + n * 3)%N) with (7 + N.to_nat n * 3)%nat by lia.
          change (S (N.to_nat (N.pred (Npos pc)))) with (1 + N.to_nat (N.pred (Npos pc)))%nat.
          replace (N.to_nat req) with ((1 + N.to_nat (N.pred (Npos pc))) * (1 + N.to_nat n * 2))%nat in Hcalls
            by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
          exact (returnsP_J (N.to_nat (N.pred (Npos pc))) (N.to_nat n) Hcalls _). }
        { rewrite denD_pushD.
          replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
          replace (N.to_nat req) with (N.to_nat cnt1 * (1 + N.to_nat n * 2))%nat in Hcalls
            by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
          exact (returnsP_L0 (N.to_nat cnt1) (N.to_nat n) Hcalls _). }""",1)])
open(p,'w').write(s)
edit('stepML_col_spec',[("replace (N.to_nat (dn + 2)%N) with (2 + N.to_nat dn)%nat by lia.","replace (N.to_nat (dn + 3)%N) with (3 + N.to_nat dn)%nat by lia.",1)])
open(p,'w').write(s)
