
Definition Good (t : Q * tape) : Prop :=
  (exists a b c, t = fO a b c /\ gOp a b c) \/
  (exists a c, t = fO a 0 c /\ gO0 a c) \/
  (exists a b c, t = fS1 a b c /\ gS1 a b c) \/
  (exists a k m, t = fRF a k m /\ gRF a k m) \/
  (exists a q, t = fEF a q /\ gEF a q) \/
  (exists a x d y z c, t = fT3 a x d y z c /\ gT3 a x d y z c) \/
  (exists a x y c, t = fT2 a x y c /\ gT2 a x y c) \/
  (exists a x y z c, t = fU3 a x y z c /\ gU3 a x y z c) \/
  (exists a x n m, t = fRG a x n m /\ gRG a x n m) \/
  (exists a x y n m, t = fRG3 a x y n m /\ gRG3 a x y n m).

Lemma good_Op : forall a b c, gOp a b c -> Good (fO a b c).
Proof. intros. left. eauto 6. Qed.
Lemma good_O0 : forall a c, gO0 a c -> Good (fO a 0 c).
Proof. intros. do 1 right. left. eauto 6. Qed.
Lemma good_S1 : forall a b c, gS1 a b c -> Good (fS1 a b c).
Proof. intros. do 2 right. left. eauto 6. Qed.
Lemma good_RF : forall a k m, gRF a k m -> Good (fRF a k m).
Proof. intros. do 3 right. left. eauto 6. Qed.
Lemma good_EF : forall a q, gEF a q -> Good (fEF a q).
Proof. intros. do 4 right. left. eauto 6. Qed.
Lemma good_T3 : forall a x d y z c, gT3 a x d y z c -> Good (fT3 a x d y z c).
Proof. intros. do 5 right. left. eauto 10. Qed.
Lemma good_T2 : forall a x y c, gT2 a x y c -> Good (fT2 a x y c).
Proof. intros. do 6 right. left. eauto 8. Qed.
Lemma good_U3 : forall a x y z c, gU3 a x y z c -> Good (fU3 a x y z c).
Proof. intros. do 7 right. left. eauto 8. Qed.
Lemma good_RG : forall a x n m, gRG a x n m -> Good (fRG a x n m).
Proof. intros. do 8 right. left. eauto 8. Qed.
Lemma good_RG3 : forall a x y n m, gRG3 a x y n m -> Good (fRG3 a x y n m).
Proof. intros. do 9 right. eauto 8. Qed.

(** ** The moves: one cycle iterate and one exit rule each *)

Ltac lia_eq := first [ apply fO_eq | apply fS1_eq | apply fT2_eq | apply fT3_eq | apply fRF_eq | apply fEF_eq
                     | apply fU3_eq | apply fRG_eq | apply fRG3_eq ]; lia.
Ltac mv ITER EXIT :=
  eapply evstep_progress_trans; [eapply tr; [exact ITER | lia_eq | reflexivity] |];
  eapply trp; [exact EXIT | lia_eq | lia_eq].

Lemma mv_oentry : forall a b c, fO a (b + 6) (c + 2) -->+ fS1 (a + 1) (b + 6) c.
Proof. exact oentry. Qed.
Lemma mv_ozero : forall a c, fO a 0 (c + 3) -->+ fS1 (a + 2) 7 c.
Proof. intros. rewrite <- t3_s1. exact (ozero a c). Qed.
Lemma mv_s1even : forall a b k, fS1 a (b + 6) (2 * k) -->+ fRF (a + 3 * k + 3) 4 (b + 12 * k + 13).
Proof. intros. mv (cycle_iter k a (b + 4) 0) (sexit0 (a + 3 * k) (b + 12 * k + 3)). Qed.
Lemma mv_s1odd : forall a b k, fS1 a (b + 6) (2 * k + 1) -->+ fRF (a + 3 * k + 3) 5 (b + 12 * k + 12).
Proof. intros. mv (cycle_iter k a (b + 4) 1) (oexit (a + 3 * k) (b + 12 * k)). Qed.
Lemma mv_rfodd : forall a k m q, k + m = 2 * q + 1 -> fRF a k (m + 1) -->+ fEF a q.
Proof. intros. mv (rcyc_iter m a k 0) (rend_ a q). Qed.
Lemma mv_rfeven : forall a k m q, k + m = 2 * q -> fRF a k (m + 1) -->+ fO a 0 (q + 1).
Proof. intros. mv (rcyc_iter m a k 0) (rende_ a q). Qed.
Lemma mv_eentry : forall a q, fEF (a + 7) (q + 5) -->+ fT3 5 14 a 8 7 (q + 2).
Proof. exact eentry. Qed.
Lemma mv_texit0 : forall a x y z c k, fT3 a (x + 6) (5 * k) (y + 6) (z + 6) (c + 2 * k + 1) -->+
  fT2 (a + 4 * k + 1) (x + y + 15 * k + 11) (z + 5 * k + 10) (c + 1).
Proof. intros. mv (cycle3_iter k a x 0 y z (c + 1)) (texit0 (a + 4 * k) c (x + 8 * k + 1) (y + 7 * k + 4) (z + 5 * k + 4)). Qed.
Lemma mv_texit1 : forall a x y z c k, fT3 a (x + 6) (5 * k + 1) (y + 6) (z + 6) (c + 2 * k + 2) -->+
  fU3 (a + 4 * k + 2) (x + 8 * k + 6) (y + 7 * k + 7) (z + 5 * k + 11) c.
Proof. intros. mv (cycle3_iter k a x 1 y z (c + 2)) (texit1 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k)). Qed.
Lemma mv_texit2 : forall a x y z c k, fT3 a (x + 6) (5 * k + 2) (y + 6) (z + 6) (c + 2 * k + 2) -->+
  fU3 (a + 4 * k + 2) (x + 8 * k + 8) (y + 7 * k + 7) (z + 5 * k + 11) c.
Proof. intros. mv (cycle3_iter k a x 2 y z (c + 2)) (texit2 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k)). Qed.
Lemma mv_texit3 : forall a x y z c k, fT3 a (x + 6) (5 * k + 3) (y + 6) (z + 6) (c + 2 * k + 3) -->+
  fT2 (a + 4 * k + 5) (x + y + 15 * k + 22) (z + 5 * k + 15) (c + 1).
Proof. intros. mv (cycle3_iter k a x 3 y z (c + 3)) (texit3 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k)). Qed.
Lemma mv_texit4 : forall a x y z c k, fT3 a (x + 6) (5 * k + 4) (y + 6) (z + 6) (c + 2 * k + 3) -->+
  fT2 (a + 4 * k + 5) (x + y + 15 * k + 24) (z + 5 * k + 15) (c + 1).
Proof. intros. mv (cycle3_iter k a x 4 y z (c + 3)) (texit4 (a + 4 * k) c (x + 8 * k) (y + 7 * k + 1) (z + 5 * k)). Qed.
Lemma mv_t2even : forall a x y k, fT2 a (x + 6) (y + 10) (2 * k) -->+ fRG (a + 3 * k + 3) (x + 7 * k + 5) 4 (y + 5 * k + 6).
Proof. intros. mv (cycle2_iter k a x (y + 4) 0) (t2exit0 (a + 3 * k) (x + 7 * k + 4) (y + 5 * k)). Qed.
Lemma mv_t2odd : forall a x y k, fT2 a (x + 6) (y + 12) (2 * k + 1) -->+ fRG (a + 3 * k + 3) (x + 7 * k + 5) 5 (y + 5 * k + 7).
Proof. intros. mv (cycle2_iter k a x (y + 6) 1) (t2exit1 (a + 3 * k) (x + 7 * k + 4) (y + 5 * k)). Qed.
Lemma mv_u3even : forall a x y z k, fU3 a (x + 2) (y + 6) (z + 10) (2 * k) -->+
  fRG3 (a + 3 * k + 3) (x + 7 * k + 7) (y + 4) 4 (z + 5 * k + 10).
Proof. intros. mv (ucyc_iter k a x y (z + 4) 0) (uexit0 (a + 3 * k) (x + 7 * k) y (z + 5 * k)). Qed.
Lemma mv_u3odd : forall a x y z k, fU3 a (x + 2) (y + 6) (z + 12) (2 * k + 1) -->+
  fRG3 (a + 3 * k + 3) (x + 7 * k + 7) (y + 4) 5 (z + 5 * k + 11).
Proof. intros. mv (ucyc_iter k a x y (z + 6) 1) (uexit1 (a + 3 * k) (x + 7 * k) y (z + 5 * k)). Qed.
Lemma mv_rgeven : forall a x n m q, n + m = 2 * q -> fRG (a + 2) x n (m + 1) -->+ fO (a + 1) (x + 9) (q + 1).
Proof. intros. mv (gcyc_iter m (a + 2) x n 0) (gend_ a x q). Qed.
Lemma mv_rgodd : forall a x n m q, n + m = 2 * q + 7 -> fRG (a + 3) (x + 6) n (m + 1) -->+ fT3 1 6 a 11 (x + 14) (q + 1).
Proof. intros. mv (gcyc_iter m (a + 3) (x + 6) n 0) (gendo_ a x q). Qed.
Lemma mv_rg3even : forall a x y n m q, n + m = 2 * q + 4 ->
  fRG3 a x (y + 4) n (m + 1) -->+ fT2 (a + 3) (x + 9) (y + 10) (q + 1).
Proof. intros. mv (g3cyc_iter m a x (y + 4) n 0) (g3end_ a x y q). Qed.
Lemma mv_rg3odd : forall a x y n m q, n + m = 2 * q + 7 ->
  fRG3 (a + 7) (x + 10) (y + 2) n (m + 1) -->+ fT3 5 14 a 15 (x + y + 17) (q + 1).
Proof. intros. mv (g3cyc_iter m (a + 7) (x + 10) (y + 2) n 0) (g3endo_ a x y q). Qed.

(** ** The invariant is restored *)

Lemma off : forall b k, k <= b -> exists b', b = b' + k.
Proof. intros b k H. exists (b - k). lia. Qed.
Lemma off3 : forall c k r, 2 * k + r <= c -> exists c', c = c' + 2 * k + r.
Proof. intros c k r H. exists (c - 2 * k - r). lia. Qed.
Lemma split5 : forall d, exists k, d = 5 * k \/ d = 5 * k + 1 \/ d = 5 * k + 2 \/ d = 5 * k + 3 \/ d = 5 * k + 4.
Proof.
  intros d. exists (d / 5). pose proof (Nat.div_mod d 5 ltac:(lia)). pose proof (Nat.mod_upper_bound d 5 ltac:(lia)).
  lia.
Qed.
Ltac sh v v' k := destruct (off v k ltac:(lia)) as [v' ->].
Ltac fin G := eexists; split; [eassumption || eauto | apply G; repeat split; lia].
Ltac fin2 M G := eexists; split; [apply M; lia | apply G; repeat split; lia].

Definition Next (t : Q * tape) : Prop := exists t', t -->+ t' /\ Good t'.

Lemma step_Op : forall a b c, gOp a b c -> Next (fO a b c).
Proof.
  unfold gOp. intros a b c h. sh b b' 6. sh c c' 2.
  exists (fS1 (a + 1) (b' + 6) c'). split; [apply mv_oentry | apply good_S1; unfold gS1; repeat split; lia].
Qed.
Lemma step_O0 : forall a c, gO0 a c -> Next (fO a 0 c).
Proof.
  unfold gO0. intros a c h. sh c c' 3.
  exists (fS1 (a + 2) 7 c'). split; [apply mv_ozero | apply good_S1; unfold gS1; repeat split; lia].
Qed.
Lemma step_S1 : forall a b c, gS1 a b c -> Next (fS1 a b c).
Proof.
  unfold gS1. intros a b c h. sh b b' 6.
  destruct (Nat.Even_or_Odd c) as [[k ->] | [k ->]].
  - exists (fRF (a + 3 * k + 3) 4 (b' + 12 * k + 13)). split; [apply mv_s1even | apply good_RF; unfold gRF; repeat split; lia].
  - exists (fRF (a + 3 * k + 3) 5 (b' + 12 * k + 12)). split; [apply mv_s1odd | apply good_RF; unfold gRF; repeat split; lia].
Qed.
Lemma step_RF : forall a k m, gRF a k m -> Next (fRF a k m).
Proof.
  unfold gRF. intros a k m h. sh m m' 1.
  destruct (Nat.Even_or_Odd (k + m')) as [[q Hq] | [q Hq]].
  - exists (fO a 0 (q + 1)). split; [apply mv_rfeven; lia | apply good_O0; unfold gO0; repeat split; lia].
  - exists (fEF a q). split; [apply mv_rfodd; lia | apply good_EF; unfold gEF; repeat split; lia].
Qed.
Lemma step_EF : forall a q, gEF a q -> Next (fEF a q).
Proof.
  unfold gEF. intros a q h. sh a a' 7. sh q q' 5.
  exists (fT3 5 14 a' 8 7 (q' + 2)). split; [apply mv_eentry | apply good_T3; unfold gT3; repeat split; lia].
Qed.
Lemma step_T3 : forall a x d y z c, gT3 a x d y z c -> Next (fT3 a x d y z c).
Proof.
  unfold gT3. intros a x d y z c h. sh x x' 6. sh y y' 6. sh z z' 6.
  destruct (split5 d) as [k [-> | [-> | [-> | [-> | ->]]]]].
  - destruct (off3 c k 1 ltac:(lia)) as [c' ->].
    exists (fT2 (a + 4 * k + 1) (x' + y' + 15 * k + 11) (z' + 5 * k + 10) (c' + 1)).
    split; [apply mv_texit0 | apply good_T2; unfold gT2; repeat split; lia].
  - destruct (off3 c k 2 ltac:(lia)) as [c' ->].
    exists (fU3 (a + 4 * k + 2) (x' + 8 * k + 6) (y' + 7 * k + 7) (z' + 5 * k + 11) c').
    split; [apply mv_texit1 | apply good_U3; unfold gU3; repeat split; lia].
  - destruct (off3 c k 2 ltac:(lia)) as [c' ->].
    exists (fU3 (a + 4 * k + 2) (x' + 8 * k + 8) (y' + 7 * k + 7) (z' + 5 * k + 11) c').
    split; [apply mv_texit2 | apply good_U3; unfold gU3; repeat split; lia].
  - destruct (off3 c k 3 ltac:(lia)) as [c' ->].
    exists (fT2 (a + 4 * k + 5) (x' + y' + 15 * k + 22) (z' + 5 * k + 15) (c' + 1)).
    split; [apply mv_texit3 | apply good_T2; unfold gT2; repeat split; lia].
  - destruct (off3 c k 3 ltac:(lia)) as [c' ->].
    exists (fT2 (a + 4 * k + 5) (x' + y' + 15 * k + 24) (z' + 5 * k + 15) (c' + 1)).
    split; [apply mv_texit4 | apply good_T2; unfold gT2; repeat split; lia].
Qed.
Lemma step_T2 : forall a x y c, gT2 a x y c -> Next (fT2 a x y c).
Proof.
  unfold gT2. intros a x y c h. sh x x' 6.
  destruct (Nat.Even_or_Odd c) as [[k ->] | [k ->]].
  - sh y y' 10. exists (fRG (a + 3 * k + 3) (x' + 7 * k + 5) 4 (y' + 5 * k + 6)).
    split; [apply mv_t2even | apply good_RG; unfold gRG; repeat split; lia].
  - sh y y' 12. exists (fRG (a + 3 * k + 3) (x' + 7 * k + 5) 5 (y' + 5 * k + 7)).
    split; [apply mv_t2odd | apply good_RG; unfold gRG; repeat split; lia].
Qed.
Lemma step_U3 : forall a x y z c, gU3 a x y z c -> Next (fU3 a x y z c).
Proof.
  unfold gU3. intros a x y z c h. sh x x' 2. sh y y' 6.
  destruct (Nat.Even_or_Odd c) as [[k ->] | [k ->]].
  - sh z z' 10. exists (fRG3 (a + 3 * k + 3) (x' + 7 * k + 7) (y' + 4) 4 (z' + 5 * k + 10)).
    split; [apply mv_u3even | apply good_RG3; unfold gRG3; repeat split; lia].
  - sh z z' 12. exists (fRG3 (a + 3 * k + 3) (x' + 7 * k + 7) (y' + 4) 5 (z' + 5 * k + 11)).
    split; [apply mv_u3odd | apply good_RG3; unfold gRG3; repeat split; lia].
Qed.
Lemma step_RG : forall a x n m, gRG a x n m -> Next (fRG a x n m).
Proof.
  unfold gRG. intros a x n m h. sh m m' 1.
  destruct (Nat.Even_or_Odd (n + m')) as [[q Hq] | [q Hq]].
  - sh a a' 2. exists (fO (a' + 1) (x + 9) (q + 1)).
    split; [apply mv_rgeven; lia | apply good_Op; unfold gOp; repeat split; lia].
  - sh a a' 3. sh x x' 6. exists (fT3 1 6 a' 11 (x' + 14) (q - 3 + 1)).
    split; [apply mv_rgodd; lia | apply good_T3; unfold gT3; repeat split; lia].
Qed.
Lemma step_RG3 : forall a x y n m, gRG3 a x y n m -> Next (fRG3 a x y n m).
Proof.
  unfold gRG3. intros a x y n m h. sh m m' 1.
  destruct (Nat.Even_or_Odd (n + m')) as [[q Hq] | [q Hq]].
  - sh y y' 4. exists (fT2 (a + 3) (x + 9) (y' + 10) (q - 2 + 1)).
    split; [apply mv_rg3even; lia | apply good_T2; unfold gT2; repeat split; lia].
  - sh a a' 7. sh x x' 10. sh y y' 2. exists (fT3 5 14 a' 15 (x' + y' + 17) (q - 3 + 1)).
    split; [apply mv_rg3odd; lia | apply good_T3; unfold gT3; repeat split; lia].
Qed.

Lemma good_step : forall t, Good t -> exists t', t -->+ t' /\ Good t'.
Proof.
  intros t [[a [b [c [-> h]]]] | [[a [c [-> h]]] | [[a [b [c [-> h]]]] | [[a [k [m [-> h]]]] |
    [[a [q [-> h]]] | [[a [x [d [y [z [c [-> h]]]]]]] | [[a [x [y [c [-> h]]]]] | [[a [x [y [z [c [-> h]]]]]] |
    [[a [x [n [m [-> h]]]]] | [a [x [y [n [m [-> h]]]]]]]]]]]]]]].
  - exact (step_Op a b c h).
  - exact (step_O0 a c h).
  - exact (step_S1 a b c h).
  - exact (step_RF a k m h).
  - exact (step_EF a q h).
  - exact (step_T3 a x d y z c h).
  - exact (step_T2 a x y c h).
  - exact (step_U3 a x y z c h).
  - exact (step_RG a x n m h).
  - exact (step_RG3 a x y n m h).
Qed.
