(** * bbchallenge 32641: one period of the bouncer, for every number of blocks

    [Cyc X k] is [0^inf A> 0 (1010001000100)^k X 0^inf].  Given three facts about two runs on a finite window
    (the excursions into the stretch [X]: where they end, [F1] and [F2], and that they leave [X] one block
    further on, [FC]), [period] proves
    [Cyc X (n+1) -->+ Cyc X (n+2)] for every [n]: the blocks are crossed by three shift rules, proved here by
    induction.  Ordinary proof, no computation. *)

From Coq Require Import Lists.List PArith. Import ListNotations.
From BusyCoq Require Import H32641_Sim.
Set Default Goal Selector "!".

(** The block, left to right; what pass 1 leaves of it (read right to left); what the way back leaves of it. *)
Definition accb : list sym := [1;0;1;0;0;0;1;0;0;0;1;0;0].
Definition lb : list sym := [1;0;0;0;1;0;0;1;0;1;0;1;0].
Definition mid : list sym := [1;0;0;0;1;0;0;0;1;0;0;1;0].

Definition Cyc (X : list sym) (k : nat) : Q * tape :=
  const 0 {{A}}> (0 >> accb ^^ k *> X *> const 0).

Lemma c1 : forall Lt Rt, Lt << 1 {{B}}> accb *> Rt -->* (lb *> Lt) << 1 {{B}}> Rt.
Proof. unfold accb, lb. execute. Qed.

Lemma p1 : forall n Lt Rt, Lt << 1 {{B}}> accb ^^ n *> Rt -->* (lb ^^ n *> Lt) << 1 {{B}}> Rt.
Proof.
  induction n as [| n IH]; intros Lt Rt; [apply evstep_refl |].
  change (accb ^^ S n) with (accb ++ accb ^^ n). rewrite Str_app_assoc.
  eapply evstep_trans; [apply c1 |]. eapply evstep_trans; [apply IH |].
  rewrite lpow_shift'. apply evstep_refl.
Qed.

Lemma c2 : forall Lt Rt, (lb *> Lt) {{E}}> (0 >> Rt) -->* Lt {{E}}> (0 >> mid *> Rt).
Proof. unfold lb, mid. execute. Qed.

Lemma p2 : forall n Lt Rt, (lb ^^ n *> Lt) {{E}}> (0 >> Rt) -->* Lt {{E}}> (0 >> mid ^^ n *> Rt).
Proof.
  induction n as [| n IH]; intros Lt Rt; [apply evstep_refl |].
  change (lb ^^ S n) with (lb ++ lb ^^ n). rewrite Str_app_assoc.
  eapply evstep_trans; [apply c2 |]. eapply evstep_trans; [apply IH |].
  rewrite lpow_shift'. apply evstep_refl.
Qed.

Lemma turn2 : forall Rt, const 0 {{E}}> (0 >> Rt) -->* const 0 << 1 {{B}}> (1 >> 0 >> Rt).
Proof. execute. Qed.

Lemma turn3 : forall Rt, const 0 {{E}}> (0 >> Rt) -->* const 0 {{A}}> (0 >> 1 >> 0 >> Rt).
Proof. execute. Qed.

Lemma into2 : forall Lt Rt, Lt << 1 {{B}}> (1 >> 0 >> Rt) -->* Lt << 0 << 1 << 1 {{B}}> Rt.
Proof. execute. Qed.

Lemma rotate : forall n (Rt : Stream sym), 1 >> 0 >> mid ^^ n *> Rt = accb ^^ n *> 1 >> 0 >> Rt.
Proof.
  induction n as [| n IH]; intros Rt; [reflexivity |].
  change (mid ^^ S n) with (mid ++ mid ^^ n). change (accb ^^ S n) with (accb ++ accb ^^ n).
  rewrite !Str_app_assoc.
  change (1 >> 0 >> mid *> mid ^^ n *> Rt) with (accb *> 1 >> 0 >> mid ^^ n *> Rt).
  rewrite IH. reflexivity.
Qed.

(** A window run that ends facing left, as a run of the machine. *)
Lemma wrun_end : forall n c l q, (wl (wrun n c), wq (wrun n c), wf (wrun n c)) = (l, q, false) ->
  forall Lt Rt, wsem Lt Rt c -->* wsem Lt Rt (mkW l (wr (wrun n c)) q false).
Proof.
  intros n c l q H Lt Rt. pose proof (wrun_ok n c Lt Rt) as G.
  destruct (wrun n c) as [l' r' q' f']. cbn [wl wr wq wf] in *.
  injection H as -> -> ->. exact G.
Qed.

Lemma app_zeros : forall (l : list sym) j, (l ++ repeat 0 j) *> const 0 = l *> const 0.
Proof.
  intros l j. rewrite Str_app_assoc. f_equal.
  induction j as [| j IH]; cbn [repeat Str_app]; [reflexivity |].
  rewrite IH, <- const_unfold. reflexivity.
Qed.

(** The first excursion into the stretch [X] (with [pad] blank cells after it): [n1] steps from [1 B> X].
    The second: [n2] steps from [0 1 1 B> r1], where [r1] is what the first one left. *)
Definition exc1 (X : list sym) (pad : nat) (n1 : positive) : W :=
  wrun n1 (mkW [1] (X ++ repeat 0 pad) B true).
Definition exc2 (X : list sym) (pad : nat) (n1 n2 : positive) : W :=
  wrun n2 (mkW [1;1;0] (wr (exc1 X pad n1)) B true).

Section Period.
Variable X : list sym.
Variables pad pad' : nat.
Variables n1 n2 : positive.
(** Both excursions come back in state E, facing left, onto a [0] next to the blocks (so they never left the
    window on its left), *)
Hypothesis F1 : (wl (exc1 X pad n1), wq (exc1 X pad n1), wf (exc1 X pad n1)) = ([0], E, false).
Hypothesis F2 : (wl (exc2 X pad n1 n2), wq (exc2 X pad n1 n2), wf (exc2 X pad n1 n2)) = ([0], E, false).
(** and then the stretch is [X] again, one block further on. *)
Hypothesis FC : [1;0] ++ wr (exc2 X pad n1 n2) = accb ++ X ++ repeat 0 pad'.

Let r1 := wr (exc1 X pad n1).
Let r2 := wr (exc2 X pad n1 n2).

Lemma H1 : forall Lt, Lt << 1 {{B}}> X *> const 0 -->* Lt {{E}}> (0 >> r1 *> const 0).
Proof.
  intros Lt. pose proof (wrun_end _ _ _ _ F1 Lt (const 0)) as G.
  rewrite <- (app_zeros X pad). exact G.
Qed.

Lemma H2 : forall Lt, Lt << 0 << 1 << 1 {{B}}> r1 *> const 0 -->* Lt {{E}}> (0 >> r2 *> const 0).
Proof. intros Lt. exact (wrun_end _ _ _ _ F2 Lt (const 0)). Qed.

Lemma close : forall n, 1 >> 0 >> mid ^^ n *> r2 *> const 0 = accb ^^ S n *> X *> const 0.
Proof.
  intros n. rewrite rotate.
  change (1 >> 0 >> r2 *> const 0) with (([1;0] ++ r2) *> const 0).
  unfold r2. rewrite FC, Str_app_assoc, app_zeros, lpow_shift'. reflexivity.
Qed.

Theorem period : forall n, Cyc X (S n) -->+ Cyc X (S (S n)).
Proof.
  intros n. unfold Cyc.
  apply progress_intro with (c' := const 0 << 1 {{B}}> accb ^^ S n *> X *> const 0);
    [apply step_right; reflexivity |].
  eapply evstep_trans; [apply p1 |]. eapply evstep_trans; [apply H1 |].
  eapply evstep_trans; [apply p2 |]. eapply evstep_trans; [apply turn2 |].
  rewrite rotate. eapply evstep_trans; [apply p1 |]. eapply evstep_trans; [apply into2 |].
  eapply evstep_trans; [apply H2 |].
  eapply evstep_trans; [apply p2 |]. eapply evstep_trans; [apply turn3 |].
  rewrite close. apply evstep_refl.
Qed.

End Period.
