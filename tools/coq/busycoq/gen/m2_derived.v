(** ** The ends written on the base forms *)

Lemma rend_ : forall a q, fRF a (2 * q + 1) 1 -->+ fEF a q.
Proof. intros. rewrite rf_odd. exact (rend a q). Qed.
Lemma rende_ : forall a q, fRF a (2 * q) 1 -->+ fO a 0 (q + 1).
Proof. intros. rewrite rf_even. exact (rende a q). Qed.
Lemma gend_ : forall a x q, fRG (a + 2) x (2 * q) 1 -->+ fO (a + 1) (x + 9) (q + 1).
Proof. intros. rewrite rg_even. exact (gend a q x). Qed.
Lemma gendo_ : forall a x q, fRG (a + 3) (x + 6) (2 * q + 7) 1 -->+ fT3 1 6 a 11 (x + 14) (q + 1).
Proof. intros. replace (2 * q + 7) with (2 * (q + 3) + 1) by lia. rewrite rg_odd. exact (gendo a q x). Qed.
Lemma g3end_ : forall a x y q, fRG3 a x (y + 4) (2 * q + 4) 1 -->+ fT2 (a + 3) (x + 9) (y + 10) (q + 1).
Proof. intros. replace (2 * q + 4) with (2 * (q + 2)) by lia. rewrite rg3_even. exact (g3end a q x y). Qed.
Lemma g3endo_ : forall a x y q,
  fRG3 (a + 7) (x + 10) (y + 2) (2 * q + 7) 1 -->+ fT3 5 14 a 15 (x + y + 17) (q + 1).
Proof. intros. replace (2 * q + 7) with (2 * (q + 3) + 1) by lia. rewrite rg3_odd. exact (g3endo a q x y). Qed.

(** ** The cycles, iterated *)

Ltac step_then R :=
  eapply evstep_trans; [apply progress_evstep; eapply trp; [exact R | lia_eq | reflexivity] |]
with lia_eq := first [ apply fO_eq | apply fS1_eq | apply fT2_eq | apply fT3_eq | apply fRF_eq | apply fEF_eq
                     | apply fU3_eq | apply fRG_eq | apply fRG3_eq ]; lia.
Ltac base := eapply tr; [apply evstep_refl | reflexivity | lia_eq].
Ltac close IH := eapply tr; [exact IH | lia_eq | lia_eq].

Lemma cycle_iter : forall k a b c, fS1 a (b + 2) (c + 2 * k) -->* fS1 (a + 3 * k) (b + 2 + 12 * k) c.
Proof.
  induction k as [| k IH]; intros a b c; [base |].
  step_then (cycle a b (c + 2 * k)). close (IH (a + 3) (b + 12) c).
Qed.

Lemma cycle2_iter : forall k a x y c,
  fT2 a (x + 6) (y + 6) (c + 2 * k) -->* fT2 (a + 3 * k) (x + 6 + 7 * k) (y + 6 + 5 * k) c.
Proof.
  induction k as [| k IH]; intros a x y c; [base |].
  step_then (cycle2 a (c + 2 * k) x y). close (IH (a + 3) (x + 7) (y + 5) c).
Qed.

Lemma cycle3_iter : forall k a x d y z c,
  fT3 a (x + 6) (d + 5 * k) (y + 6) (z + 6) (c + 2 * k) -->*
  fT3 (a + 4 * k) (x + 6 + 8 * k) d (y + 6 + 7 * k) (z + 6 + 5 * k) c.
Proof.
  induction k as [| k IH]; intros a x d y z c; [base |].
  step_then (cycle3 a (c + 2 * k) (d + 5 * k) x y z). close (IH (a + 4) (x + 8) d (y + 7) (z + 5) c).
Qed.

Lemma ucyc_iter : forall k a x y z c,
  fU3 a (x + 2) (y + 6) (z + 6) (c + 2 * k) -->* fU3 (a + 3 * k) (x + 2 + 7 * k) (y + 6) (z + 6 + 5 * k) c.
Proof.
  induction k as [| k IH]; intros a x y z c; [base |].
  step_then (ucyc a (c + 2 * k) x y z). close (IH (a + 3) (x + 7) y (z + 5) c).
Qed.

Lemma rcyc_iter : forall t a k m, fRF a k (m + 1 + t) -->* fRF a (k + t) (m + 1).
Proof.
  induction t as [| t IH]; intros a k m; [base |].
  step_then (rcyc a k (m + t)). close (IH a (k + 1) m).
Qed.

Lemma gcyc_iter : forall t a x n m, fRG a x n (m + 1 + t) -->* fRG a x (n + t) (m + 1).
Proof.
  induction t as [| t IH]; intros a x n m; [base |].
  step_then (gcyc a (m + t) n x). close (IH a x (n + 1) m).
Qed.

Lemma g3cyc_iter : forall t a x y n m, fRG3 a x y n (m + 1 + t) -->* fRG3 a x y (n + t) (m + 1).
Proof.
  induction t as [| t IH]; intros a x y n m; [base |].
  step_then (g3cyc a (m + t) n x y). close (IH a x y (n + 1) m).
Qed.
