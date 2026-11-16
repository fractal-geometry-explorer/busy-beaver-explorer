(** * 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE halts, after exactly K steps

    BB(6) holdout, bbchallenge id 172044.  The final theorems are

      [halts_172044 : halts tm c0]
      [steps_172044 : halts_in tm c0 (N.to_nat K) /\ forall n, halts_in tm c0 n -> n = N.to_nat K]

    with K = 853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808
    111420498351739937140047615589682 (about 8.53e131), the number of steps to the halting configuration.  With
    the halting transition counted (the bbchallenge convention) the machine runs for K + 1 steps.

    The machine keeps a binary odometer on its tape: counters (011)^n separated by 11 (bit 0) or 01 (bit 1).
    A visit of the right end is a binary increment of the bits ([visit], proved for every zone, with its step
    count [vcnt]), and V visits are applied at once in closed form ([jump], with the number of steps [Jz V ps],
    a sum over the levels of the odometer).  Between jumps a run-length simulator follows the machine
    ([gstep]: one transition, a run crossed one or two copies at a time, a copy unpacked), with two block rules
    for whole counter levels ([macL]: D walks left across 1 0 (011)^k 1; [macR]: C walks right across
    (100)^m 1 0 1 1 0).  Every lemma states its exact number of steps, as busycoq's [multistep].  Every round
    is proved to follow the machine and to add its steps to the count ([round_sound]); the simulator's
    strategy is not trusted.  [run_halts] evaluates 2^25 rounds from blank tape with the kernel's virtual
    machine; the halting transition F0 is met after 19,026,768 rounds, with the count K. *)

From Coq Require Import String.
From Coq Require Import Lists.List Arith PArith NArith ZArith Lia Bool.
Import ListNotations.
From BusyCoq Require Import Individual62.
Set Default Goal Selector "!".

Module M172044.

(** * Sim *)

(** Part 1: a run-length simulator for any machine, and its soundness. *)

(** ** Tapes as lists of items *)

Inductive item := Bit (s : Sym) | Run (w : list Sym) (n : positive).

(** Stacks are nearest cell first. *)
Fixpoint den (l : list item) (t : side) : side :=
  match l with
  | [] => t
  | Bit s :: l' => s >> den l' t
  | Run w n :: l' => w ^^ (Pos.to_nat n) *> den l' t
  end.

Lemma den_app : forall l l' t, den (l ++ l') t = den l (den l' t).
Proof. induction l as [|[s|w n] l IH]; intros; simpl; rewrite ?IH; reflexivity. Qed.

Lemma den_bits : forall w l t, den (List.map Bit w ++ l) t = w *> den l t.
Proof. induction w; intros; simpl; rewrite ?IHw; reflexivity. Qed.

(** The configuration with the head on the first cell of [f], moving away from [b]. *)
Definition semR (f b : list item) (q : Q) : Q * tape :=
  (den b 0inf) {{q}}> (den f 0inf).

(** Popping the cell under the head (blank if the stack is empty). *)
Definition popc (f : list item) : option (Sym * list item) :=
  match f with
  | [] => Some (S0, [])
  | Bit s :: f' => Some (s, f')
  | Run _ _ :: _ => None
  end.

Lemma popc_den : forall f s f', popc f = Some (s, f') -> den f 0inf = s >> den f' 0inf.
Proof.
  intros [|[s0|w n] f] s f' H; simpl in H; inversion H; subst; simpl; try reflexivity.
  apply const_unfold.
Qed.

(** ** Crossing a word *)

Definition sym_eqb (a b : Sym) : bool :=
  match a, b with S0, S0 | S1, S1 => true | _, _ => false end.
Lemma sym_eqb_eq : forall a b, sym_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

Definition st_eqb (a b : Q) : bool :=
  match a, b with A, A | B, B | C, C | D, D | E, E | F, F => true | _, _ => false end.
Lemma st_eqb_eq : forall a b, st_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

(** Counted runs: [c ->> n / c'] is busycoq's [multistep], exactly [n] steps. *)

Lemma ms_trans : forall tm n m k c c' c'', c -[ tm ]->> n / c' -> c' -[ tm ]->> m / c'' -> k = (n + m)%nat ->
  c -[ tm ]->> k / c''.
Proof. intros. subst. eapply multistep_trans; eassumption. Qed.

Lemma ms_eq : forall tm n m c c', c -[ tm ]->> n / c' -> n = m -> c -[ tm ]->> m / c'.
Proof. intros. subst. assumption. Qed.

Lemma ms_conf : forall tm n c c1 c2, c -[ tm ]->> n / c1 -> c1 = c2 -> c -[ tm ]->> n / c2.
Proof. intros. subst. assumption. Qed.

Lemma ms_refl : forall tm c, c -[ tm ]->> 0 / c.
Proof. intros. constructor. Qed.

Lemma ms_refl' : forall tm c c' n, c = c' -> n = O -> c -[ tm ]->> n / c'.
Proof. intros. subst. constructor. Qed.

Section Generic.
Variable T : TM.

(** The head works on the word [r] (cells already passed in [l], nearest first) until it leaves it on the far
    side, and counts its steps; [None] if it leaves on the near side, halts, or the fuel runs out. *)
Fixpoint segRun (fuel : nat) (l r : list Sym) (q : Q) : option (list Sym * Q * N) :=
  match fuel with
  | O => None
  | S fuel' =>
    match r with
    | [] => Some (l, q, 0%N)
    | s :: r' =>
      match T (q, s) with
      | None => None
      | Some (s', R, q') =>
        match segRun fuel' (s' :: l) r' q' with Some (a, b, k) => Some (a, b, N.succ k) | None => None end
      | Some (s', L, q') =>
        match l with
        | [] => None
        | y :: l' =>
          match segRun fuel' l' (y :: s' :: r') q' with Some (a, b, k) => Some (a, b, N.succ k) | None => None end
        end
      end
    end
  end.

Lemma segRun_sound : forall fuel l r q l' q' k, segRun fuel l r q = Some (l', q', k) ->
  forall L R, (l *> L) {{q}}> (r *> R) -[ T ]->> N.to_nat k / (l' *> L) {{q'}}> R.
Proof.
  induction fuel as [|fuel IH]; intros l r q l' q' k H L R; simpl in H; [discriminate|].
  destruct r as [|s r'].
  - inversion H; subst. constructor.
  - revert H. destruct (T (q, s)) as [[[s' []] q1]|] eqn:E; intro H; try discriminate.
    + destruct l as [|y l0]; [discriminate|].
      destruct (segRun fuel l0 (y :: s' :: r') q1) as [[[a b] k0]|] eqn:E2; inversion H; subst.
      rewrite N2Nat.inj_succ. econstructor.
      * simpl. eapply step_left. exact E.
      * apply (IH _ _ _ _ _ _ E2 L R).
    + destruct (segRun fuel (s' :: l) r' q1) as [[[a b] k0]|] eqn:E2; inversion H; subst.
      rewrite N2Nat.inj_succ. econstructor.
      * simpl. eapply step_right. exact E.
      * apply (IH _ _ _ _ _ _ E2 L R).
Qed.

Definition cross (q : Q) (w : list Sym) : option (list Sym * N) :=
  match segRun 200 [] w q with
  | Some (w', q', k) => if st_eqb q' q then Some (w', k) else None
  | None => None
  end.

Lemma cross_sound1 : forall q w w' k, cross q w = Some (w', k) ->
  forall L R, L {{q}}> (w *> R) -[ T ]->> N.to_nat k / (w' *> L) {{q}}> R.
Proof.
  unfold cross. intros q w w' k H L R.
  destruct (segRun 200 [] w q) as [[[res q'] k0]|] eqn:E; try discriminate.
  destruct (st_eqb q' q) eqn:Eq; try discriminate.
  apply st_eqb_eq in Eq. inversion H; subst.
  exact (segRun_sound _ _ _ _ _ _ _ E L R).
Qed.

Lemma cross_sound : forall q w w' k, cross q w = Some (w', k) ->
  forall n L R, L {{q}}> (w ^^ n *> R) -[ T ]->> (n * N.to_nat k) / (w' ^^ n *> L) {{q}}> R.
Proof.
  intros q w w' k H n. induction n as [|n IH]; intros L R.
  - constructor.
  - replace (w' ^^ S n *> L) with (w' ^^ n *> w' *> L)
      by (simpl lpow; rewrite Str_app_assoc, lpow_shift'; reflexivity).
    simpl lpow. rewrite Str_app_assoc.
    eapply ms_trans.
    + apply (cross_sound1 _ _ _ _ H L).
    + apply IH.
    + lia.
Qed.

(** ** One round of the generic simulator, head moving right in the frame of [T], with its step count *)

Inductive res :=
  | Halt                                              (* the halting transition *)
  | Same (f b : list item) (q : Q) (k : N)            (* same direction, after k steps *)
  | Turn (f b : list item) (q : Q).                   (* one step, and the head turned: front and back exchanged *)

Definition unpack (w : list Sym) (n : positive) (f : list item) : list item :=
  List.map Bit w ++ (match n with xH => f | _ => Run w (Pos.pred n) :: f end).

Lemma den_unpack : forall w n f t, den (unpack w n f) t = den (Run w n :: f) t.
Proof.
  intros w n f t. unfold unpack. rewrite den_bits.
  destruct n as [p|p|].
  - change (den (Run w (Pos.pred p~1) :: f) t) with (w ^^ Pos.to_nat (Pos.pred p~1) *> den f t).
    change (den (Run w p~1 :: f) t) with (w ^^ Pos.to_nat p~1 *> den f t).
    replace (Pos.to_nat p~1) with (S (Pos.to_nat (Pos.pred p~1))) by lia.
    simpl lpow. rewrite Str_app_assoc. reflexivity.
  - change (den (Run w (Pos.pred p~0) :: f) t) with (w ^^ Pos.to_nat (Pos.pred p~0) *> den f t).
    change (den (Run w p~0 :: f) t) with (w ^^ Pos.to_nat p~0 *> den f t).
    replace (Pos.to_nat p~0) with (S (Pos.to_nat (Pos.pred p~0))) by lia.
    simpl lpow. rewrite Str_app_assoc. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Definition act (o : option (Sym * dir * Q)) (f' b : list item) : res :=
  match o with
  | None => Halt
  | Some (s', R, q') => Same f' (Bit s' :: b) q' 1
  | Some (s', L, q') => Turn b (Bit s' :: f') q'
  end.

Fixpoint weqb (u v : list Sym) : bool :=
  match u, v with
  | [], [] => true
  | a :: u', b :: v' => sym_eqb a b && weqb u' v'
  | _, _ => false
  end.

Lemma weqb_eq : forall u v, weqb u v = true -> u = v.
Proof.
  induction u as [|a u IH]; intros [|b v] H; simpl in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply sym_eqb_eq in H1. apply IH in H2. subst. reflexivity.
Qed.

(** Put a run on a stack, merging it with a run of the same word. *)
Definition pushRun (w : list Sym) (n : positive) (s : list item) : list item :=
  match s with
  | Run w' m :: s' => if weqb w w' then Run w (n + m) :: s' else Run w n :: s
  | _ => Run w n :: s
  end.

Lemma den_pushRun : forall w n s t, den (pushRun w n s) t = w ^^ (Pos.to_nat n) *> den s t.
Proof.
  intros w n s t. unfold pushRun.
  destruct s as [|[x|w' m] s']; try reflexivity.
  destruct (weqb w w') eqn:E; [|reflexivity].
  apply weqb_eq in E. subst w'. simpl. rewrite Pos2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma lpow_double : forall (w : list Sym) h (t : side), (w ++ w) ^^ h *> t = w ^^ (2 * h) *> t.
Proof.
  induction h as [|h IH]; intros t; [reflexivity|].
  replace (2 * S h) with (S (S (2 * h))) by lia.
  simpl lpow. rewrite !Str_app_assoc, IH. reflexivity.
Qed.

(** Two copies at once: [n = 2h] or [n = 2h + 1] copies, [h >= 1]. *)
Definition dbl (w : list Sym) (n : positive) (f b : list item) (q : Q) : option res :=
  match n with
  | xH => None
  | xO h | xI h =>
    match cross q (w ++ w) with
    | None => None
    | Some (v, k) =>
      let f' := match n with xI _ => Run w 1 :: f | _ => f end in
      let m := length w in
      let b' := if weqb (firstn m v) (skipn m v) then pushRun (firstn m v) (2 * h) b else pushRun v h b in
      Some (Same f' b' q (Npos h * k))
    end
  end.

Definition gstep (f b : list item) (q : Q) : res :=
  match f with
  | Run w n :: f' =>
    match cross q w with
    | Some (w', k) => Same f' (pushRun w' n b) q (Npos n * k)
    | None =>
      match dbl w n f' b q with
      | Some r => r
      | None => Same (unpack w n f') b q 0
      end
    end
  | _ =>
    match popc f with
    | None => Same f b q 0
    | Some (s, f') => act (T (q, s)) f' b
    end
  end.

Lemma dbl_same : forall w n f b q f2 b2 q2 k2, dbl w n f b q = Some (Same f2 b2 q2 k2) ->
  semR (Run w n :: f) b q -[ T ]->> N.to_nat k2 / semR f2 b2 q2.
Proof.
  intros w n f b q f2 b2 q2 k2 H. unfold dbl in H.
  assert (G : forall h, (n = xO h \/ n = xI h) -> forall v k, cross q (w ++ w) = Some (v, k) ->
     semR (Run w n :: f) b q -[ T ]->> N.to_nat (Npos h * k) /
     semR (match n with xI _ => Run w 1 :: f | _ => f end) (pushRun v h b) q).
  { intros h Hn v k Hc. unfold semR. rewrite den_pushRun. simpl den.
    assert (E : forall t, w ^^ Pos.to_nat n *> t = (w ++ w) ^^ Pos.to_nat h *>
               (match n with xI _ => w ^^ Pos.to_nat 1 *> t | _ => t end)).
    { intros t. rewrite lpow_double. destruct Hn as [-> | ->].
      - rewrite Pos2Nat.inj_xO. reflexivity.
      - rewrite Pos2Nat.inj_xI. change (Pos.to_nat 1) with (S O).
        replace (S (2 * Pos.to_nat h)) with (2 * Pos.to_nat h + S O)%nat by lia.
        rewrite lpow_add, Str_app_assoc. reflexivity. }
    rewrite E. rewrite N2Nat.inj_mul. change (N.to_nat (Npos h)) with (Pos.to_nat h).
    destruct Hn as [-> | ->]; simpl den; apply (cross_sound _ _ _ _ Hc). }
  destruct n as [h|h|]; [| |discriminate];
  (destruct (cross q (w ++ w)) as [[v k]|] eqn:Hc; [|discriminate]);
  inversion H; subst; clear H;
  (destruct (weqb (firstn (length w) v) (skipn (length w) v)) eqn:Ew;
   [ apply weqb_eq in Ew;
     eapply ms_conf; [apply (G h ltac:(auto) v k eq_refl)
       | unfold semR; rewrite !den_pushRun;
         rewrite <- (firstn_skipn (length w) v) at 1; rewrite Ew, Pos2Nat.inj_xO, <- lpow_double;
         reflexivity]
   | apply (G h ltac:(auto) v k eq_refl)]).
Qed.

Lemma act_same : forall q s f' b g b' q' k, act (T (q, s)) f' b = Same g b' q' k ->
  semR (Bit s :: f') b q -[ T ]->> N.to_nat k / semR g b' q'.
Proof.
  intros q s f' b g b' q' k H. unfold act in H.
  destruct (T (q, s)) as [[[s' []] q1]|] eqn:E; inversion H; subst.
  unfold semR. simpl. econstructor; [eapply step_right; exact E|]. simpl. constructor.
Qed.

Lemma act_turn : forall q s f' b g b' q', act (T (q, s)) f' b = Turn g b' q' ->
  semR (Bit s :: f') b q -[ T ]->> 1 / flip_conf (semR g b' q').
Proof.
  intros q s f' b g b' q' H. unfold act in H.
  destruct (T (q, s)) as [[[s' []] q1]|] eqn:E; inversion H; subst.
  unfold semR. simpl. econstructor; [eapply step_left; exact E|]. simpl. constructor.
Qed.

Lemma act_halt : forall q s f' b, act (T (q, s)) f' b = Halt -> halted T (semR (Bit s :: f') b q).
Proof.
  intros q s f' b H. unfold act in H.
  destruct (T (q, s)) as [[[s' []] q1]|] eqn:E; inversion H; subst.
  unfold semR, halted. simpl. exact E.
Qed.

Lemma semR_pop : forall f s f' b q, popc f = Some (s, f') -> semR f b q = semR (Bit s :: f') b q.
Proof. intros. unfold semR. simpl. rewrite (popc_den _ _ _ H). reflexivity. Qed.

Lemma gstep_same : forall f b q f' b' q' k, gstep f b q = Same f' b' q' k ->
  semR f b q -[ T ]->> N.to_nat k / semR f' b' q'.
Proof.
  intros f b q f' b' q' k H. unfold gstep in H.
  destruct f as [|[s|w n] f0].
  - rewrite (semR_pop [] S0 []) by reflexivity. apply (act_same _ _ _ _ _ _ _ _ H).
  - apply (act_same _ _ _ _ _ _ _ _ H).
  - destruct (cross q w) as [[w' k0]|] eqn:Ec.
    + injection H as H1 H2 H3 H4.
      assert (Ek : N.to_nat k = (Pos.to_nat n * N.to_nat k0)%nat) by (subst; destruct k0; simpl; lia).
      rewrite Ek. subst.
      unfold semR. rewrite den_pushRun. simpl. apply (cross_sound _ _ _ _ Ec).
    + destruct (dbl w n f0 b q) as [r|] eqn:Ed.
      * subst r. apply (dbl_same _ _ _ _ _ _ _ _ _ Ed).
      * inversion H; subst. unfold semR. rewrite den_unpack. constructor.
Qed.

Lemma gstep_turn : forall f b q f' b' q', gstep f b q = Turn f' b' q' ->
  semR f b q -[ T ]->> 1 / flip_conf (semR f' b' q').
Proof.
  intros f b q f' b' q' H. unfold gstep in H.
  destruct f as [|[s|w n] f0].
  - rewrite (semR_pop [] S0 []) by reflexivity. apply (act_turn _ _ _ _ _ _ _ H).
  - apply (act_turn _ _ _ _ _ _ _ H).
  - destruct (cross q w) as [[w' k0]|]; [inversion H|].
    destruct (dbl w n f0 b q) as [r|] eqn:Ed; [|inversion H].
    subst r. unfold dbl in Ed. destruct n; try discriminate;
    destruct (cross q (w ++ w)) as [[? ?]|]; inversion Ed.
Qed.

Lemma gstep_halt : forall f b q, gstep f b q = Halt -> halted T (semR f b q).
Proof.
  intros f b q H. unfold gstep in H.
  destruct f as [|[s|w n] f0].
  - rewrite (semR_pop [] S0 []) by reflexivity. apply (act_halt _ _ _ _ H).
  - apply (act_halt _ _ _ _ H).
  - destruct (cross q w) as [[? ?]|]; [inversion H|].
    destruct (dbl w n f0 b q) as [r|] eqn:Ed; [|inversion H].
    subst r. unfold dbl in Ed. destruct n; try discriminate;
    destruct (cross q (w ++ w)) as [[? ?]|]; inversion Ed.
Qed.

End Generic.

(** ** Flipping twice *)

Lemma flip_flip_apply : forall tm qs, flip (flip tm) qs = tm qs.
Proof.
  intros tm [q s]. unfold flip. destruct (tm (q, s)) as [[[s' []] q']|]; reflexivity.
Qed.

Lemma ff_step : forall tm c c', c -[ flip (flip tm) ]-> c' -> c -[ tm ]-> c'.
Proof.
  intros tm c c' H. inversion H; subst; rewrite flip_flip_apply in *.
  - apply step_left. assumption.
  - apply step_right. assumption.
Qed.

Lemma ff_multistep : forall tm n c c', c -[ flip (flip tm) ]->> n / c' -> c -[ tm ]->> n / c'.
Proof.
  intros tm n c c' H. induction H.
  - constructor.
  - econstructor; [apply ff_step; eassumption | assumption].
Qed.

Lemma ff_halted : forall tm c, halted (flip (flip tm)) c -> halted tm c.
Proof.
  intros tm [q [[l s] r]]. unfold halted. rewrite flip_flip_apply. auto.
Qed.

(** ** Both directions *)

Section Machine.
Variable tm : TM.

Definition tmd (d : bool) : TM := if d then tm else flip tm.

(** [d = true]: head moving right, [f] on the right.  [d = false]: head moving left, [f] on the left. *)
Definition sem (d : bool) (f b : list item) (q : Q) : Q * tape :=
  if d then semR f b q else flip_conf (semR f b q).

Lemma to_tm : forall d n c c', c -[ tmd d ]->> n / c' ->
  (if d then c else flip_conf c) -[ tm ]->> n / (if d then c' else flip_conf c').
Proof.
  intros [] n c c' H; cbn beta iota in *; unfold tmd in H.
  - exact H.
  - apply ff_multistep. apply flip_multistep. exact H.
Qed.

Lemma gstep_sound_same : forall d f b q f' b' q' k, gstep (tmd d) f b q = Same f' b' q' k ->
  sem d f b q -[ tm ]->> N.to_nat k / sem d f' b' q'.
Proof.
  intros d f b q f' b' q' k H. unfold sem.
  apply to_tm. apply (gstep_same _ _ _ _ _ _ _ _ H).
Qed.

Lemma gstep_sound_turn : forall d f b q f' b' q', gstep (tmd d) f b q = Turn f' b' q' ->
  sem d f b q -[ tm ]->> 1 / sem (negb d) f' b' q'.
Proof.
  intros d f b q f' b' q' H. unfold sem.
  pose proof (to_tm d _ _ _ (gstep_turn _ _ _ _ _ _ _ H)) as G.
  destruct d; cbn beta iota in *.
  - exact G.
  - rewrite flip_conf_involutive in G. exact G.
Qed.

Lemma gstep_sound_halt : forall d f b q, gstep (tmd d) f b q = Halt -> halted tm (sem d f b q).
Proof.
  intros d f b q H.
  pose proof (gstep_halt _ _ _ _ H) as G. unfold sem.
  destruct d; cbn beta iota in *; unfold tmd in G.
  - exact G.
  - apply ff_halted. apply flip_halted. exact G.
Qed.

End Machine.

(** * Mac *)

Definition tm := Eval compute in (TM_from_str "1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE"%string).
Notation "c ->> n / c'" := (c -[ tm ]->> n / c') (at level 40, n at next level).

(** One counted step. *)
Ltac cstep := eapply multistep_S; [prove_step | simpl_tape].
Ltac csteps n := replace n with (S (pred n)) by lia; cstep.

(** 011 read from its right end, and 100 read from its left end. *)
Definition W : list Sym := [1;1;0].
Definition X : list Sym := [1;0;0].

Lemma shiftD : forall k (Y r : side), (W ^^ k *> Y) <{{D}} r ->> (3 * k) / Y <{{D}} X ^^ k *> r.
Proof.
  induction k as [|k IH]; intros Y r.
  - constructor.
  - replace (3 * S k)%nat with (S (S (S (3 * k)))) by lia.
    cbn [lpow]. rewrite !Str_app_assoc. rewrite <- (lpow_shift' _ _ X).
    unfold W at 1. cbn [Str_app].
    do 3 cstep.
    apply (IH Y (X *> r)).
Qed.

Lemma shiftC : forall k (L r : side), L {{C}}> X ^^ k *> r ->> (3 * k) / (W ^^ k *> L) {{C}}> r.
Proof.
  induction k as [|k IH]; intros L r.
  - constructor.
  - replace (3 * S k)%nat with (S (S (S (3 * k)))) by lia.
    cbn [lpow]. rewrite !Str_app_assoc. rewrite <- (lpow_shift' _ _ W).
    unfold X at 1. cbn [Str_app].
    do 3 cstep.
    apply (IH (W *> L) r).
Qed.

Lemma macL_tape : forall k (Y r : side),
  D;; (0 >> W ^^ (S k) *> 1 >> Y) {{1}} r ->> (5 + 3 * k) / D;; Y {{1}} (X ^^ k *> 1 >> 0 >> 1 >> 1 >> 0 >> r).
Proof.
  intros k Y r. simpl lpow. unfold W at 1. simpl Str_app.
  do 5 cstep.
  apply (shiftD k (1 >> Y)).
Qed.

Lemma macR_tape : forall m (L r : side),
  L {{C}}> X ^^ m *> 1 >> 0 >> 1 >> 1 >> 0 >> r ->> (3 * m + 5) / (1 >> 1 >> W ^^ (S m) *> L) {{C}}> r.
Proof.
  intros m L r. eapply ms_trans; [apply shiftC| |reflexivity].
  do 5 cstep. constructor.
Qed.

(** * Zone *)

(** 101, the repeat of 011 read one cell later. *)
Definition U : list Sym := [1;0;1].

Lemma rot : forall n (s : side), W ^^ n *> 1 >> s = 1 >> U ^^ n *> s.
Proof.
  induction n as [|n IH]; intros s.
  - reflexivity.
  - simpl lpow. unfold W, U in *. simpl. rewrite IH. reflexivity.
Qed.

Lemma wrep_succ : forall n (t : side), W ^^ N.to_nat (N.succ n) *> t = W *> W ^^ N.to_nat n *> t.
Proof. intros. rewrite N2Nat.inj_succ. change (W ^^ S (N.to_nat n)) with (W ++ W ^^ N.to_nat n). apply Str_app_assoc. Qed.

Lemma wrep_succ' : forall n (t : side), W ^^ N.to_nat (N.succ n) *> t = W ^^ N.to_nat n *> W *> t.
Proof. intros. rewrite wrep_succ. symmetry. apply lpow_shift'. Qed.

Definition nb (b : bool) : Sym := if b then 0 else 1.

(** The levels: (bit, count) pairs, lowest first. *)
Fixpoint lvT (lv : list (bool * N)) (t : side) : side :=
  match lv with
  | [] => t
  | (b, n) :: r => 1 >> nb b >> W ^^ N.to_nat n *> lvT r t
  end.

Definition zoneT (n0 : N) (lv : list (bool * N)) (t : side) : side := 0 >> W ^^ N.to_nat n0 *> lvT lv t.

Definition hdb (lv : list (bool * N)) : bool :=
  match lv with [] => false | (b, _) :: _ => b end.

Fixpoint inc (lv : list (bool * N)) : option (list (bool * N)) :=
  match lv with
  | [] => None
  | (false, n) :: r => if N.eqb n 0%N then None else Some ((true, (n - 1)%N) :: r)
  | (true, n) :: r =>
    if N.eqb n 0%N then None else
    match inc r with
    | Some r' => Some ((false, if hdb r then n else (n + 1)%N) :: r')
    | None => None
    end
  end.

(** ** The pieces *)

Lemma p_start : forall T, (0 >> 1 >> T) {{A}}> 0inf ->> 6 / T {{D}}> 1 >> 1 >> 0 >> 0 >> 1 >> 0inf.
Proof. intros. do 6 cstep. constructor. Qed.

Lemma p_left : forall n L R, (U ^^ n *> L) {{D}}> 1 >> R ->> (3 * n) / L {{D}}> 1 >> X ^^ n *> R.
Proof.
  intros n L R.
  pose proof (shiftD n (1 >> L) R) as H. rewrite rot in H. exact H.
Qed.

Lemma p_pass : forall T R,
  (0 >> 1 >> 1 >> 0 >> 1 >> T) {{D}}> 1 >> R ->> 5 / T {{D}}> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> R.
Proof. intros. do 5 cstep. constructor. Qed.

Lemma p_turn : forall T R, (1 >> 1 >> T) {{D}}> 1 >> R ->> 5 / (W *> T) {{C}}> R.
Proof. intros. do 5 cstep. constructor. Qed.

Lemma p_end : forall L, L {{C}}> 1 >> 0 >> 0 >> 1 >> 0inf ->> 4 / (0 >> W *> L) {{A}}> 0inf.
Proof. intros. do 4 cstep. simpl_tape. constructor. Qed.

(** ** The carry *)

Definition ext (lv lv' : list (bool * N)) (t : side) : side :=
  if hdb lv then lvT lv' t else W *> lvT lv' t.

Lemma wN_add : forall a b (t : side), W ^^ N.to_nat (a + b) *> t = W ^^ N.to_nat a *> W ^^ N.to_nat b *> t.
Proof. intros. rewrite N2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma wN_succ_l : forall n (t : side), W ^^ N.to_nat (n + 1) *> t = W *> W ^^ N.to_nat n *> t.
Proof.
  intros. replace (n + 1)%N with (N.succ n) by lia. rewrite N2Nat.inj_succ.
  change (W ^^ S (N.to_nat n)) with (W ++ W ^^ N.to_nat n). apply Str_app_assoc.
Qed.

Lemma wN_succ_r : forall n (t : side), W ^^ N.to_nat (n + 1) *> t = W ^^ N.to_nat n *> W *> t.
Proof. intros. rewrite wN_succ_l. symmetry. apply lpow_shift'. Qed.

Lemma wN_1 : forall (t : side), W ^^ N.to_nat 1 *> t = W *> t.
Proof. intros. reflexivity. Qed.

Lemma N_succ_pred : forall n, N.eqb n 0 = false -> n = N.succ (n - 1).
Proof. intros n H. apply N.eqb_neq in H. lia. Qed.

(** The steps of the carry: 6n + 4 for each bit 1 passed (out and back), 5 for the turn. *)
Fixpoint ccnt (lv : list (bool * N)) : N :=
  match lv with
  | [] => 0%N
  | (true, n) :: r => (6 * n + 4 + ccnt r)%N
  | (false, _) :: _ => 5%N
  end.

Lemma carry : forall (t : side) lv b n r lv' R (Fn : side -> side) kF, lv = (b, n) :: r -> inc lv = Some lv' ->
  (forall L, L {{C}}> R ->> kF / (Fn L) {{A}}> 0inf) ->
  (nb b >> W ^^ N.to_nat n *> lvT r t) {{D}}> 1 >> R ->> (N.to_nat (ccnt lv) + kF) / (Fn (ext lv lv' t)) {{A}}> 0inf.
Proof.
  intros t lv. induction lv as [|p lv0 IH]; intros b n r lv' R Fn kF Heq Hinc HF; [discriminate|].
  inversion Heq; subst p lv0. clear Heq.
  destruct b.
  - (* bit 1: pass and carry on *)
    simpl in Hinc. destruct (N.eqb n 0) eqn:En; [discriminate|].
    destruct r as [|[b2 n2] r2]; [discriminate|].
    destruct (inc ((b2, n2) :: r2)) as [r'|] eqn:Ei; [|discriminate].
    inversion Hinc; subst lv'. clear Hinc.
    pose proof (N_succ_pred n En) as Hn. set (m := (n - 1)%N) in *.
    assert (Hc : (N.to_nat (ccnt ((true, n) :: (b2, n2) :: r2)) + kF)%nat =
       (5 + (3 * N.to_nat m + (N.to_nat (ccnt ((b2, n2) :: r2)) + (3 * N.to_nat m + 5 + kF))))%nat).
    { cbn [ccnt]. rewrite Hn. lia. }
    rewrite Hc. rewrite Hn. clear Hc.
    rewrite (wrep_succ m). simpl lvT. unfold W at 1. simpl Str_app. rewrite rot.
    eapply ms_trans; [apply p_pass| |reflexivity].
    eapply ms_trans; [apply p_left| |reflexivity].
    eapply ms_conf.
    + apply (IH b2 n2 r2 r' (X ^^ N.to_nat m *> 1 >> 0 >> 1 >> 1 >> 0 >> R)
        (fun L => Fn (1 >> 1 >> W ^^ S (N.to_nat m) *> L)) (3 * N.to_nat m + 5 + kF)%nat eq_refl eq_refl).
      intros L. eapply ms_trans; [apply macR_tape| apply HF |reflexivity].
    + unfold ext. simpl hdb. simpl lvT. simpl nb.
      destruct b2; simpl hdb.
      * rewrite N2Nat.inj_succ. reflexivity.
      * replace (N.succ m + 1)%N with (N.succ (N.succ m)) by lia. rewrite !N2Nat.inj_succ.
        rewrite lpow_shift'. change (W ^^ S (S (N.to_nat m))) with (W ++ W ^^ S (N.to_nat m)).
        rewrite Str_app_assoc. reflexivity.
  - (* bit 0: turn *)
    simpl in Hinc. destruct (N.eqb n 0) eqn:En; [discriminate|].
    inversion Hinc; subst lv'. clear Hinc.
    cbn [ccnt]. change (N.to_nat 5) with 5%nat.
    rewrite (N_succ_pred n En) at 1. rewrite wrep_succ. simpl nb. unfold W at 1. simpl Str_app.
    eapply ms_trans; [apply p_turn| |reflexivity].
    eapply ms_conf; [apply HF|].
    unfold ext. simpl. reflexivity.
Qed.

(** The steps of a visit. *)
Definition vcnt (n0 : N) (lv : list (bool * N)) : N := (10 + 6 * n0 + ccnt lv)%N.

Theorem visit : forall n0 lv lv' t, inc lv = Some lv' ->
  (zoneT n0 lv t) {{A}}> 0inf ->> N.to_nat (vcnt n0 lv) /
  (zoneT (n0 + if hdb lv then 1 else 2)%N lv' t) {{A}}> 0inf.
Proof.
  intros n0 lv lv' t H.
  destruct lv as [|[b n] r]; [discriminate|].
  replace (N.to_nat (vcnt n0 ((b, n) :: r))) with
    (6 + (3 * N.to_nat n0 + (N.to_nat (ccnt ((b, n) :: r)) + (3 * N.to_nat n0 + 4))))%nat
    by (unfold vcnt; lia).
  unfold zoneT at 1. simpl lvT. rewrite rot.
  eapply ms_trans; [apply p_start| |reflexivity].
  eapply ms_trans; [apply p_left| |reflexivity].
  eapply ms_conf.
  - apply (carry t ((b, n) :: r) b n r lv' (X ^^ N.to_nat n0 *> 1 >> 0 >> 0 >> 1 >> 0inf)
      (fun L => 0 >> W ^^ N.to_nat (n0 + 1) *> L) _ eq_refl H).
    intros L. eapply ms_trans; [apply shiftC| |reflexivity].
    eapply ms_conf; [apply p_end|].
    rewrite wN_succ_l. reflexivity.
  - unfold ext, zoneT. simpl hdb. destruct b.
    + reflexivity.
    + replace (n0 + 2)%N with (n0 + 1 + 1)%N by lia.
      rewrite (wN_succ_r (n0 + 1)). reflexivity.
Qed.

(** * Jump *)

(** Many visits of a zone at once: a port of lean/Jump.lean, counts in [N]. *)

Definition b2n (b : bool) : N := if b then 1%N else 0%N.

(** ** Parity facts *)

Lemma d2 : forall x, x = (2 * N.div2 x + b2n (N.odd x))%N.
Proof. intros x. pose proof (N.div2_odd x). destruct (N.odd x); cbn [N.b2n b2n] in *; lia. Qed.

Lemma par_even : forall x, N.odd x = false -> N.odd (x + 1) = true /\ N.div2 (x + 1) = N.div2 x.
Proof.
  intros x H. pose proof (d2 x) as E1. pose proof (d2 (x + 1)) as E2. rewrite H in E1.
  destruct (N.odd (x + 1)); cbn [N.b2n b2n] in *; [split; [reflexivity|lia]|exfalso; lia].
Qed.

Lemma par_odd : forall x, N.odd x = true -> N.odd (x + 1) = false /\ N.div2 (x + 1) = (N.div2 x + 1)%N.
Proof.
  intros x H. pose proof (d2 x) as E1. pose proof (d2 (x + 1)) as E2. rewrite H in E1.
  destruct (N.odd (x + 1)); cbn [N.b2n b2n] in *; [exfalso; lia|split; [reflexivity|lia]].
Qed.

Lemma div2_plus2 : forall x, N.div2 (x + 2) = (N.div2 x + 1)%N.
Proof.
  intros x. pose proof (d2 x) as E1. pose proof (d2 (x + 2)) as E2.
  destruct (N.odd x), (N.odd (x + 2)); cbn [N.b2n b2n] in *; lia.
Qed.

Lemma div2_le : forall x, (N.div2 x <= x)%N.
Proof. intros x. pose proof (d2 x). destruct (N.odd x); cbn [N.b2n b2n] in *; lia. Qed.

(** ** The increment in N coordinates *)

Fixpoint incN (ps : list (bool * N)) : option (list (bool * N)) :=
  match ps with
  | [] => None
  | (false, M) :: r => Some ((true, (M - 1)%N) :: r)
  | (true, M) :: r =>
    match incN r with
    | Some r' => Some ((false, M) :: r')
    | None => None
    end
  end.

(** [V] increments at once; [c] is the number of times the bit was 1 or became 1. *)
Fixpoint addV (V : N) (ps : list (bool * N)) : list (bool * N) :=
  match ps with
  | [] => []
  | (b, M) :: r =>
    let c := (V + b2n b)%N in
    (N.odd c, (M + b2n b - N.div2 (c + 1))%N) :: addV (N.div2 c) r
  end.

Fixpoint ovf (V : N) (ps : list (bool * N)) : N :=
  match ps with
  | [] => V
  | (b, _) :: r => ovf (N.div2 (V + b2n b)) r
  end.

Definition bump (d : N) (ps : list (bool * N)) : list (bool * N) :=
  match ps with
  | [] => []
  | (b, M) :: r => (b, (M + d)%N) :: r
  end.

Lemma addV_zero : forall ps, addV 0 ps = ps.
Proof.
  induction ps as [|[b M] r IH]; [reflexivity|].
  destruct b; simpl; rewrite IH; f_equal; f_equal; lia.
Qed.

Lemma ovf_succ : forall ps V, ovf (V + 1) ps = 0%N -> ovf V ps = 0%N.
Proof.
  induction ps as [|[b M] r IH]; intros V H; simpl in *; [lia|].
  replace (V + 1 + b2n b)%N with (V + b2n b + 1)%N in H by lia.
  destruct (N.odd (V + b2n b)) eqn:Eo.
  - destruct (par_odd _ Eo) as [_ E]. rewrite E in H. apply IH. exact H.
  - destruct (par_even _ Eo) as [_ E]. rewrite E in H. exact H.
Qed.

Lemma addV_succ : forall ps V, ovf (V + 1) ps = 0%N -> incN (addV V ps) = Some (addV (V + 1) ps).
Proof.
  induction ps as [|[b M] r IH]; intros V H; simpl in *; [lia|].
  replace (V + 1 + b2n b)%N with (V + b2n b + 1)%N in * by lia.
  set (c := (V + b2n b)%N) in *.
  destruct (N.odd c) eqn:Eo.
  - destruct (par_odd _ Eo) as [Eo' E]. rewrite E in *. rewrite Eo'.
    rewrite (IH _ H).
    replace (c + 1 + 1)%N with (c + 2)%N by lia. rewrite div2_plus2. reflexivity.
  - destruct (par_even _ Eo) as [Eo' E]. rewrite E in *. rewrite Eo'.
    replace (c + 1 + 1)%N with (c + 2)%N by lia. rewrite div2_plus2.
    f_equal. f_equal. f_equal. lia.
Qed.

(** ** Back to the tape *)

Fixpoint physP (ps : list (bool * N)) (top : N) : list (bool * N) :=
  match ps with
  | [] => []
  | [(b, _)] => [(b, (top - b2n b)%N)]
  | (b, _) :: ((b', M') :: _) as rest => (b, (M' + b2n b' - b2n b)%N) :: physP rest top
  end.

Definition n0of (ps : list (bool * N)) : N :=
  match ps with [] => 0%N | (b, M) :: _ => (M + b2n b)%N end.

Fixpoint goodAll (ps : list (bool * N)) : bool :=
  match ps with [] => true | (_, M) :: r => N.leb 2 M && goodAll r end.

Definition goodN (ps : list (bool * N)) (top : N) : bool :=
  match ps with [] => false | _ :: r => goodAll r && N.leb 2 top end.

Lemma hd_physP : forall ps top, hdb (physP ps top) = hdb ps.
Proof. intros [|[b M] [|[b' M'] r]] top; reflexivity. Qed.

Lemma physP_bump : forall d ps top, physP (bump d ps) top = physP ps top.
Proof. intros d [|[b M] [|[b' M'] r]] top; reflexivity. Qed.

Lemma hd_incN : forall ps ps', incN ps = Some ps' -> hdb ps' = negb (hdb ps).
Proof.
  intros [|[[] M] r] ps' H; simpl in H; try discriminate.
  - destruct (incN r); inversion H; reflexivity.
  - inversion H; reflexivity.
Qed.

Lemma incN_nil : forall ps, incN ps = Some [] -> False.
Proof.
  intros [|[[] M] r] H; simpl in H; try discriminate.
  revert H. destruct (incN r); intro H; discriminate.
Qed.

Lemma inc_physP : forall top, (2 <= top)%N -> forall ps ps',
  goodAll (List.tl ps) = true -> incN ps = Some ps' -> inc (physP ps top) = Some (physP ps' top).
Proof.
  intros top Htop ps. induction ps as [|[b M] r IH]; intros ps' Hg H; [discriminate|].
  destruct r as [|[b' M'] rest].
  - destruct b; simpl in H; [discriminate|]. inversion H; subst. simpl.
    rewrite N.sub_0_r. destruct (N.eqb_spec top 0); [lia|reflexivity].
  - simpl in Hg. apply andb_true_iff in Hg. destruct Hg as [HM' Hg]. apply N.leb_le in HM'.
    destruct b.
    + change (match incN ((b', M') :: rest) with Some r' => Some ((false, M) :: r') | None => None end
        = Some ps') in H.
      revert H. destruct (incN ((b', M') :: rest)) as [q|] eqn:Eq; intro H; [|discriminate].
      inversion H; subst ps'. clear H.
      assert (IHq : inc (physP ((b', M') :: rest) top) = Some (physP q top)).
      { apply IH; [destruct rest as [|[]]; simpl; auto|reflexivity]. }
      pose proof (hd_incN _ _ Eq) as Hq. simpl in Hq.
      change (inc ((true, (M' + b2n b' - b2n true)%N) :: physP ((b', M') :: rest) top) =
              Some (physP ((false, M) :: q) top)).
      assert (Hh : hdb (physP ((b', M') :: rest) top) = b') by (rewrite hd_physP; reflexivity).
      remember (physP ((b', M') :: rest) top) as P eqn:HP. clear HP.
      cbn [inc]. rewrite Hh.
      destruct (N.eqb (M' + b2n b' - b2n true) 0) eqn:E0.
      { apply N.eqb_eq in E0. destruct b'; simpl in E0; lia. }
      rewrite IHq.
      destruct q as [|[b'' M''] q']; [exfalso; exact (incN_nil _ Eq)|].
      simpl in Hq. subst b''.
      destruct b'; simpl in Eq.
      * revert Eq. destruct (incN rest) as [z|]; intro Eq; inversion Eq; subst. simpl.
        destruct q' as [|[]]; simpl; f_equal; f_equal; f_equal; lia.
      * inversion Eq; subst. simpl.
        destruct q' as [|[]]; simpl; f_equal; f_equal; f_equal; lia.
    + simpl in H. inversion H; subst ps'. clear H.
      simpl. destruct (N.eqb (M' + b2n b' - 0) 0) eqn:E0.
      { apply N.eqb_eq in E0. destruct b'; simpl in E0; lia. }
      destruct rest as [|[]]; simpl; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Lemma goodAll_incN : forall ps ps', incN ps = Some ps' -> goodAll ps' = true -> goodAll ps = true.
Proof.
  induction ps as [|[[] M] r IH]; intros ps' H Hg; simpl in H; try discriminate.
  - destruct (incN r) as [r'|] eqn:E; inversion H; subst. simpl in *.
    apply andb_true_iff in Hg. destruct Hg as [H1 H2]. rewrite H1. simpl. apply (IH r' eq_refl H2).
  - inversion H; subst. simpl in *.
    apply andb_true_iff in Hg. destruct Hg as [H1 H2]. apply N.leb_le in H1.
    rewrite H2. apply andb_true_iff. split; [apply N.leb_le; lia|reflexivity].
Qed.

Lemma goodN_incN : forall top ps ps', incN ps = Some ps' -> goodN ps' top = true -> goodN ps top = true.
Proof.
  intros top [|[[] M] r] ps' H Hg; simpl in H; try discriminate.
  - destruct (incN r) as [r'|] eqn:E; inversion H; subst. simpl in *.
    apply andb_true_iff in Hg. destruct Hg as [H1 H2]. rewrite (goodAll_incN _ _ E H1). exact H2.
  - inversion H; subst. exact Hg.
Qed.

Definition zoneN (ps : list (bool * N)) (top : N) (t : side) : side := zoneT (n0of ps) (physP ps top) t.

Lemma incN_bump : forall d ps x, incN (bump d ps) = Some x -> exists y, incN ps = Some y.
Proof.
  intros d [|[[] M] r] x H; simpl in H; try discriminate.
  - destruct (incN r) as [r'|] eqn:E; [|discriminate]. exists ((false, M) :: r'). simpl. rewrite E. reflexivity.
  - eexists. reflexivity.
Qed.

(** The steps of a visit in the coordinates N_j: 6 N_j + 4 for every level the carry reaches, and 11. *)
Fixpoint chain (ps : list (bool * N)) : N :=
  match ps with
  | [] => 0%N
  | (b, M) :: r => (6 * M + 4 + if b then chain r else 0)%N
  end.

Lemma chain_vcnt : forall top ps y, goodAll (List.tl ps) = true -> incN ps = Some y ->
  vcnt (n0of ps) (physP ps top) = (11 + chain ps)%N.
Proof.
  intros top ps. induction ps as [|[b M] r IH]; intros y Hg H; [discriminate|].
  destruct b.
  - destruct r as [|[b' M'] rest]; [discriminate|].
    change (match incN ((b', M') :: rest) with Some r' => Some ((false, M) :: r') | None => None end
      = Some y) in H.
    destruct (incN ((b', M') :: rest)) as [z|] eqn:Ez; [|discriminate].
    cbn [List.tl goodAll] in Hg. apply andb_prop in Hg. destruct Hg as [HM Hg]. apply N.leb_le in HM.
    assert (Hg' : goodAll (List.tl ((b', M') :: rest)) = true) by exact Hg.
    assert (IHr := IH z Hg' eq_refl).
    unfold vcnt in *. cbn [physP n0of ccnt chain b2n] in *.
    destruct rest as [|p rest']; cbn [physP ccnt] in *; destruct b'; cbn [b2n] in *; lia.
  - unfold vcnt. destruct r as [|[b' M'] rest]; cbn [physP n0of ccnt chain b2n]; lia.
Qed.

Lemma visitN : forall ps ps' top t, goodN ps top = true -> incN (bump 2 ps) = Some ps' ->
  (zoneN ps top t) {{A}}> 0inf ->> N.to_nat (11 + chain ps) / (zoneN ps' top t) {{A}}> 0inf.
Proof.
  intros ps ps' top t Hg H.
  destruct ps as [|[b M] r]; [discriminate|].
  destruct (incN_bump _ _ _ H) as [y Hy].
  simpl in Hg. apply andb_true_iff in Hg. destruct Hg as [Hg Ht]. apply N.leb_le in Ht.
  rewrite <- (chain_vcnt top ((b, M) :: r) y Hg Hy).
  pose proof (inc_physP top Ht (bump 2 ((b, M) :: r)) ps' Hg H) as Hi.
  rewrite physP_bump in Hi.
  pose proof (visit (n0of ((b, M) :: r)) _ _ t Hi) as Hv.
  unfold zoneN. rewrite hd_physP in Hv.
  replace (n0of ps') with (n0of ((b, M) :: r) + (if hdb ((b, M) :: r) then 1 else 2))%N; [exact Hv|].
  destruct b; simpl in H.
  - destruct (incN r); inversion H; subst. simpl. lia.
  - inversion H; subst. simpl. lia.
Qed.

Lemma ovf_bump : forall d V ps, ovf V (bump d ps) = ovf V ps.
Proof. intros d V [|[b M] r]; reflexivity. Qed.

Lemma bump_addV : forall V d ps,
  bump 2 (addV V (bump (2 * V + d) ps)) = addV V (bump (2 * V + d + 2) ps).
Proof.
  intros V d [|[b M] r]; [reflexivity|]. cbn [bump addV].
  pose proof (div2_le (V + b2n b + 1)). f_equal. f_equal. lia.
Qed.

Lemma goodN_bump : forall d top ps, goodN (bump d ps) top = goodN ps top.
Proof. intros d top [|[b M] r]; reflexivity. Qed.

Definition after (V : N) (ps : list (bool * N)) : list (bool * N) := addV V (bump (2 * V) ps).

Lemma after_zero : forall ps, after 0 ps = ps.
Proof.
  intros ps. unfold after. rewrite addV_zero. destruct ps as [|[b M] r]; [reflexivity|].
  simpl. f_equal. f_equal. lia.
Qed.


(** ** The number of steps of V visits, in closed form *)

(** [Qz n] is the sum of [div2 x] for [x < n]. *)
Definition Qz (n : N) : Z :=
  let m := Z.of_N (N.div2 n) in if N.odd n then (m * m)%Z else (m * (m - 1))%Z.

Lemma Qz_succ : forall n, Qz (n + 1) = (Qz n + Z.of_N (N.div2 n))%Z.
Proof.
  intros n. unfold Qz. destruct (N.odd n) eqn:E.
  - destruct (par_odd n E) as [E1 E2]. rewrite E1, E2. rewrite N2Z.inj_add. lia.
  - destruct (par_even n E) as [E1 E2]. rewrite E1, E2. lia.
Qed.

Fixpoint Gt (V : N) (ps : list (bool * N)) : Z :=
  match ps with
  | [] => 0%Z
  | (b, M) :: r =>
    (Z.of_N V * (6 * Z.of_N (M + b2n b) + 4) - 6 * Qz (V + b2n b + 1) + Gt (N.div2 (V + b2n b)) r)%Z
  end.

(** No count of a level would go below 0 (checked by the simulator). *)
Fixpoint ntr (V : N) (ps : list (bool * N)) : bool :=
  match ps with
  | [] => true
  | (b, M) :: r => andb (N.leb (N.div2 (V + b2n b + 1)) (M + b2n b)) (ntr (N.div2 (V + b2n b)) r)
  end.

Definition ntrT (V : N) (ps : list (bool * N)) : bool :=
  match ps with [] => true | (b, _) :: r => ntr (N.div2 (V + b2n b)) r end.

Lemma div2_mono : forall x y, (x <= y)%N -> (N.div2 x <= N.div2 y)%N.
Proof. intros x y H. pose proof (d2 x). pose proof (d2 y). destruct (N.odd x), (N.odd y); cbn [b2n] in *; lia. Qed.

Lemma ntr_mono : forall ps V W, ntr V ps = true -> (W <= V)%N -> ntr W ps = true.
Proof.
  induction ps as [|[b M] r IH]; intros V W H Hle; [reflexivity|].
  cbn [ntr] in *. apply andb_prop in H. destruct H as [H1 H2]. apply N.leb_le in H1.
  apply andb_true_intro. split.
  - apply N.leb_le. pose proof (div2_mono (W + b2n b + 1) (V + b2n b + 1) ltac:(lia)). lia.
  - apply (IH _ _ H2). apply div2_mono. lia.
Qed.

Lemma ntrT_mono : forall ps V W, ntrT V ps = true -> (W <= V)%N -> ntrT W ps = true.
Proof.
  intros [|[b M] r] V W H Hle; [reflexivity|]. cbn [ntrT] in *.
  apply (ntr_mono _ _ _ H). apply div2_mono. lia.
Qed.

Lemma chain_addV : forall ps V, ntr V ps = true ->
  Z.of_N (chain (addV V ps)) = (Gt (V + 1) ps - Gt V ps)%Z.
Proof.
  induction ps as [|[b M] r IH]; intros V H; [reflexivity|].
  cbn [ntr] in H. apply andb_prop in H. destruct H as [H1 H2]. apply N.leb_le in H1.
  cbn [addV chain Gt].
  replace (V + 1 + b2n b)%N with (V + b2n b + 1)%N by lia.
  replace (V + b2n b + 1 + 1)%N with ((V + b2n b + 1) + 1)%N by lia.
  rewrite (Qz_succ (V + b2n b + 1)).
  remember (V + b2n b)%N as c eqn:Hc.
  destruct (N.odd c) eqn:Eo.
  - destruct (par_odd c Eo) as [_ E2]. rewrite E2.
    rewrite N2Z.inj_add, N2Z.inj_add, N2Z.inj_mul, N2Z.inj_sub by lia.
    rewrite (IH (N.div2 c) H2). rewrite Hc in *. rewrite !N2Z.inj_add. lia.
  - destruct (par_even c Eo) as [_ E2]. rewrite E2.
    rewrite N2Z.inj_add, N2Z.inj_add, N2Z.inj_mul, N2Z.inj_sub by lia.
    rewrite Hc in *. rewrite !N2Z.inj_add. lia.
Qed.

Lemma Gt_bump : forall W d ps, ps <> [] -> Gt W (bump d ps) = (Gt W ps + 6 * Z.of_N W * Z.of_N d)%Z.
Proof. intros W d [|[b M] r] H; [congruence|]. cbn [bump Gt]. rewrite !N2Z.inj_add. ring. Qed.

Lemma ntr_bump : forall V ps, ntrT V ps = true -> ntr V (bump (2 * V) ps) = true.
Proof.
  intros V [|[b M] r] H; [reflexivity|]. cbn [ntrT] in H. cbn [bump ntr].
  rewrite H. rewrite andb_true_r. apply N.leb_le.
  pose proof (d2 (V + b2n b + 1)). destruct (N.odd (V + b2n b + 1)), b; cbn [b2n] in *; lia.
Qed.

Lemma Gt_zero : forall ps, Gt 0 ps = 0%Z.
Proof.
  induction ps as [|[b M] r IH]; [reflexivity|]. cbn [Gt].
  destruct b; cbn [b2n]; simpl N.add; simpl N.div2; rewrite IH; reflexivity.
Qed.

(** The steps of [V] visits from [ps]. *)
Definition Jz (V : N) (ps : list (bool * N)) : Z :=
  (11 * Z.of_N V + 6 * Z.of_N V * (Z.of_N V - 1) + Gt V ps)%Z.

Lemma Jz_succ : forall V ps, ps <> [] -> ntrT V ps = true ->
  Jz (V + 1) ps = (Jz V ps + Z.of_N (11 + chain (after V ps)))%Z.
Proof.
  intros V ps Hp H. unfold Jz, after.
  rewrite !N2Z.inj_add. rewrite (chain_addV _ _ (ntr_bump V ps H)). rewrite !Gt_bump by exact Hp.
  rewrite !N2Z.inj_add, !N2Z.inj_mul. ring.
Qed.

Lemma Jz_nonneg : forall V ps, ps <> [] -> ntrT V ps = true -> (0 <= Jz V ps)%Z.
Proof.
  intros V ps Hp. induction V as [|V IH] using N.peano_ind; intros H.
  - unfold Jz. rewrite Gt_zero. lia.
  - rewrite <- N.add_1_r in *. rewrite (Jz_succ V ps Hp (ntrT_mono ps (V + 1) V H ltac:(lia))).
    pose proof (IH (ntrT_mono ps (V + 1) V H ltac:(lia))). lia.
Qed.

Theorem jump : forall ps top t V, ovf V ps = 0%N -> goodN (after V ps) top = true -> ntrT V ps = true ->
  (zoneN ps top t) {{A}}> 0inf ->> Z.to_nat (Jz V ps) / (zoneN (after V ps) top t) {{A}}> 0inf.
Proof.
  intros ps top t V. induction V as [|V IH] using N.peano_ind; intros Ho Hg Hn.
  - rewrite after_zero. unfold Jz. rewrite Gt_zero. constructor.
  - rewrite <- N.add_1_r in *.
    pose proof (ovf_succ _ _ Ho) as Ho'.
    assert (Hn' : ntrT V ps = true) by (apply (ntrT_mono _ _ _ Hn); lia).
    assert (Hs : incN (bump 2 (after V ps)) = Some (after (V + 1) ps)).
    { unfold after. pose proof (bump_addV V 0 ps) as E. rewrite N.add_0_r in E. rewrite E.
      replace (2 * (V + 1))%N with (2 * V + 2)%N by lia.
      apply addV_succ. rewrite ovf_bump. exact Ho. }
    assert (Hg' : goodN (after V ps) top = true).
    { pose proof (goodN_incN _ _ _ Hs Hg) as G. rewrite goodN_bump in G. exact G. }
    assert (Hp : ps <> []) by (intro; subst; discriminate).
    rewrite (Jz_succ V ps Hp Hn'). pose proof (Jz_nonneg V ps Hp Hn').
    eapply ms_trans; [apply (IH Ho' Hg' Hn')|apply (visitN _ _ _ _ Hg' Hs)|lia].
Qed.

(** The same sum with one multiplication per level, for the evaluation. *)
Fixpoint Gf (V : N) (ps : list (bool * N)) : Z :=
  match ps with
  | [] => 0%Z
  | (b, M) :: r =>
    let c := (V + b2n b)%N in
    let m := Z.of_N (N.div2 (c + 1)) in
    let e := if N.odd c then 1%Z else 0%Z in
    let a := (6 * Z.of_N (M + b2n b) + 4)%Z in
    (m * (2 * a - 6 * (m - e)) - (e + Z.of_N (b2n b)) * a + Gf (N.div2 c) r)%Z
  end.

Lemma Gf_Gt : forall ps V, Gf V ps = Gt V ps.
Proof.
  induction ps as [|[b M] r IH]; intros V; [reflexivity|]. cbn [Gf Gt]. rewrite IH.
  unfold Qz. replace (V + b2n b + 1 + 1)%N with (V + b2n b + 1 + 1)%N by reflexivity.
  remember (V + b2n b)%N as c eqn:Hc.
  pose proof (d2 c) as Ec. pose proof (d2 (c + 1)) as Ec1.
  destruct (N.odd c) eqn:Eo.
  - destruct (par_odd c Eo) as [E1 E2]. rewrite E1. rewrite E2 in *. cbn [b2n] in *.
    assert (Hv : Z.of_N V = (Z.of_N c - Z.of_N (b2n b))%Z) by (subst c; rewrite N2Z.inj_add; lia).
    rewrite Hv. rewrite N2Z.inj_add. replace (Z.of_N c) with (2 * Z.of_N (N.div2 c) + 1)%Z by lia. ring.
  - destruct (par_even c Eo) as [E1 E2]. rewrite E1. rewrite E2 in *. cbn [b2n] in *.
    assert (Hv : Z.of_N V = (Z.of_N c - Z.of_N (b2n b))%Z) by (subst c; rewrite N2Z.inj_add; lia).
    rewrite Hv. replace (Z.of_N c) with (2 * Z.of_N (N.div2 c))%Z by lia. ring.
Qed.

Definition Jf (V : N) (ps : list (bool * N)) : Z :=
  let v := Z.of_N V in (v * (6 * v + 5) + Gf V ps)%Z.

Lemma Jf_Jz : forall V ps, Jf V ps = Jz V ps.
Proof. intros. unfold Jf, Jz. rewrite Gf_Gt. ring. Qed.

(** * Run *)

(** The simulator with level macros and jumps, its soundness, and the run from blank tape. *)

(** ** One phase for the runs (port of [canonL] in lean/Run.lean) *)

Definition is1 (s : Sym) : bool := match s with S1 => true | S0 => false end.
Definition is0 (s : Sym) : bool := match s with S0 => true | S1 => false end.

Lemma is1_eq : forall s, is1 s = true -> s = 1. Proof. destruct s; simpl; intro H; congruence. Qed.
Lemma is0_eq : forall s, is0 s = true -> s = 0. Proof. destruct s; simpl; intro H; congruence. Qed.

Definition cbit (s : Sym) (out : list item) : list item :=
  match s, out with
  | S1, Bit S1 :: Bit S0 :: Run w m :: rest => if weqb w W then Run W (m + 1) :: rest else Bit s :: out
  | S1, Bit S1 :: Bit S0 :: Bit S1 :: Bit S1 :: Bit S0 :: rest => pushRun W 2 rest
  | _, _ => Bit s :: out
  end.

Lemma den_cbit : forall s out t, den (cbit s out) t = s >> den out t.
Proof.
  intros s out t. unfold cbit.
  destruct s; [reflexivity|].
  destruct out as [|[[]|] [|[[]|] [|[[]|w m] rest]]]; try reflexivity.
  - (* 1 1 0 1 1 0 *)
    destruct rest as [|[[]|] [|[[]|] [|[[]|] rest]]]; try reflexivity.
    rewrite den_pushRun. reflexivity.
  - destruct (weqb w W) eqn:E; [|reflexivity].
    apply weqb_eq in E. subst w. simpl den. rewrite Pos2Nat.inj_add, Nat.add_comm. reflexivity.
Qed.

Fixpoint crun (n : positive) (out : list item) : list item :=
  match out with
  | Bit S1 :: Bit S1 :: Bit S0 :: rest => crun (n + 1) rest
  | Run w m :: rest => if weqb w W then Run W (n + m) :: rest else Run W n :: out
  | _ => Run W n :: out
  end.

Lemma den_crun : forall out n t, den (crun n out) t = W ^^ Pos.to_nat n *> den out t.
Proof.
  fix IH 1. intros out n t.
  destruct out as [|[[]|w m] rest]; try reflexivity.
  - destruct rest as [|[[]|] [|[[]|] rest]]; try reflexivity.
    simpl crun. rewrite IH. rewrite Pos2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity.
  - simpl crun. destruct (weqb w W) eqn:E; [|reflexivity].
    apply weqb_eq in E. subst w. simpl. rewrite Pos2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity.
Qed.

Definition crun0 (n : N) (out : list item) : list item :=
  match n with N0 => out | Npos p => crun p out end.

Lemma den_crun0 : forall n out t, den (crun0 n out) t = W ^^ N.to_nat n *> den out t.
Proof. intros [|p] out t; [reflexivity|]. apply den_crun. Qed.

Definition W110 : list Sym := [0;1;1].
Definition W101 : list Sym := [1;0;1].

Lemma rotg : forall (x y : list Sym) m (s : side), (x ++ y) ^^ S m *> s = x *> (y ++ x) ^^ m *> y *> s.
Proof.
  intros x y m. induction m as [|m IH]; intros s.
  - simpl lpow. rewrite app_nil_r, Str_app_assoc. reflexivity.
  - change ((x ++ y) ^^ S (S m)) with ((x ++ y) ++ (x ++ y) ^^ S m).
    rewrite Str_app_assoc, IH, !Str_app_assoc.
    change ((y ++ x) ^^ S m) with ((y ++ x) ++ (y ++ x) ^^ m).
    rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma rot110 : forall m (s : side), W110 ^^ S m *> s = 0 >> W ^^ m *> 1 >> 1 >> s.
Proof. intros m s. change W110 with ([0] ++ [1;1]). rewrite rotg. reflexivity. Qed.

Lemma rot101 : forall m (s : side), W101 ^^ S m *> s = 1 >> 0 >> W ^^ m *> 1 >> s.
Proof. intros m s. change W101 with ([1;0] ++ [1]). rewrite rotg. reflexivity. Qed.

Definition emit (x : item) (out : list item) : list item :=
  match x with
  | Bit s => cbit s out
  | Run w n =>
    if weqb w W then crun n out
    else if weqb w W110 then cbit 0 (crun0 (Npos n - 1) (cbit 1 (cbit 1 out)))
    else if weqb w W101 then cbit 1 (cbit 0 (crun0 (Npos n - 1) (cbit 1 out)))
    else Run w n :: out
  end.

Lemma pos_pred_N : forall p, Pos.to_nat p = S (N.to_nat (Npos p - 1)).
Proof. intros p. lia. Qed.

Lemma den_emit : forall x out t, den (emit x out) t = den [x] (den out t).
Proof.
  intros [s|w n] out t; cbn [emit].
  - apply den_cbit.
  - destruct (weqb w W) eqn:E1; [apply weqb_eq in E1; subst w; apply den_crun|].
    destruct (weqb w W110) eqn:E2.
    + apply weqb_eq in E2. subst w.
      rewrite den_cbit, den_crun0, den_cbit, den_cbit. simpl den. rewrite pos_pred_N, rot110. reflexivity.
    + destruct (weqb w W101) eqn:E3; [|reflexivity].
      apply weqb_eq in E3. subst w.
      rewrite den_cbit, den_cbit, den_crun0, den_cbit. simpl den. rewrite pos_pred_N, rot101. reflexivity.
Qed.

Fixpoint canonL (s : list item) : list item :=
  match s with [] => [] | x :: s' => emit x (canonL s') end.

Lemma den_canonL : forall s t, den (canonL s) t = den s t.
Proof.
  induction s as [|x s IH]; intros t; [reflexivity|].
  simpl canonL. rewrite den_emit, IH. destruct x; reflexivity.
Qed.

(** ** Reading and writing a zone *)

Definition wrun (n : N) (rest : list item) : list item :=
  match n with N0 => rest | Npos p => Run W p :: rest end.

Lemma den_wrun : forall n rest t, den (wrun n rest) t = W ^^ N.to_nat n *> den rest t.
Proof. intros [|p] rest t; reflexivity. Qed.

Fixpoint encLv (lv : list (bool * N)) (rest : list item) : list item :=
  match lv with
  | [] => rest
  | (b, n) :: r => Bit 1 :: Bit (nb b) :: wrun n (encLv r rest)
  end.

Definition encZone (n0 : N) (lv : list (bool * N)) (rest : list item) : list item :=
  Bit 0 :: wrun n0 (encLv lv rest).

Lemma den_encLv : forall lv rest t, den (encLv lv rest) t = lvT lv (den rest t).
Proof.
  induction lv as [|[b n] r IH]; intros rest t; [reflexivity|].
  simpl. rewrite den_wrun, IH. reflexivity.
Qed.

Lemma den_encZone : forall n0 lv rest t, den (encZone n0 lv rest) t = zoneT n0 lv (den rest t).
Proof. intros. unfold encZone, zoneT. simpl. rewrite den_wrun, den_encLv. reflexivity. Qed.

(** Untrusted: the parse is checked by encoding it again. *)
Fixpoint parseLv (s : list item) : list (bool * N) * list item :=
  match s with
  | Bit S1 :: Bit x :: Run w n :: s' =>
    if andb (weqb w W) (Pos.leb 7 n) then
      let p := parseLv s' in ((is0 x, Npos n) :: fst p, snd p)
    else ([], s)
  | _ => ([], s)
  end.

Definition parseZone (s : list item) : option (N * (list (bool * N) * list item)) :=
  match s with
  | Bit S0 :: Run w n0 :: s' => if weqb w W then Some (Npos n0, parseLv s') else None
  | _ => None
  end.

Fixpoint toNaux (b : bool) (n : N) (lv : list (bool * N)) : list (bool * N) * N :=
  match lv with
  | [] => ([], (n + b2n b)%N)
  | (b', n') :: r => let p := toNaux b' n' r in ((b', (n + b2n b - b2n b')%N) :: fst p, snd p)
  end.

Definition toN (n0 : N) (lv : list (bool * N)) : list (bool * N) * N :=
  match lv with
  | [] => ([], 0%N)
  | (b1, n1) :: r => let p := toNaux b1 n1 r in ((b1, (n0 - b2n b1)%N) :: fst p, snd p)
  end.

Fixpoint chooseAux (ps : list (bool * N)) (pw blow : N) (lim : option N) : N :=
  match ps with
  | [] =>
    let v0 := (pw - 1 - blow)%N in
    match lim with None => v0 | Some l => N.min v0 l end
  | (b, M) :: r =>
    if N.ltb M 6 then 0%N else
    let l := (pw * (2 * (M - 6) + b2n b + 1) - 1 - blow)%N in
    let lim' := match lim with None => Some l | Some l0 => Some (N.min l0 l) end in
    chooseAux r (2 * pw) (blow + b2n b * pw) lim'
  end.

Definition chooseV (ps : list (bool * N)) : N :=
  match ps with [] => 0%N | (b, _) :: r => chooseAux r 2 (b2n b) None end.

(** Equality of stacks. *)
Definition item_eqb (x y : item) : bool :=
  match x, y with
  | Bit a, Bit b => sym_eqb a b
  | Run u m, Run v n => andb (weqb u v) (Pos.eqb m n)
  | _, _ => false
  end.

Fixpoint items_eqb (s t : list item) : bool :=
  match s, t with
  | [], [] => true
  | x :: s', y :: t' => andb (item_eqb x y) (items_eqb s' t')
  | _, _ => false
  end.

Lemma items_eqb_eq : forall s t, items_eqb s t = true -> s = t.
Proof.
  induction s as [|x s IH]; intros [|y t] H; simpl in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply IH in H2. subst t. f_equal.
  destruct x as [a|u m], y as [b|v n]; simpl in H1; try discriminate.
  - apply sym_eqb_eq in H1. subst. reflexivity.
  - apply andb_true_iff in H1. destruct H1 as [H1 H3]. apply weqb_eq in H1. apply Pos.eqb_eq in H3. subst.
    reflexivity.
Qed.

Fixpoint lv_eqb (u v : list (bool * N)) : bool :=
  match u, v with
  | [], [] => true
  | (a, m) :: u', (b, n) :: v' => andb (andb (Bool.eqb a b) (N.eqb m n)) (lv_eqb u' v')
  | _, _ => false
  end.

Lemma lv_eqb_eq : forall u v, lv_eqb u v = true -> u = v.
Proof.
  induction u as [|[a m] u IH]; intros [|[b n] v] H; simpl in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H H2]. apply andb_true_iff in H. destruct H as [H H1].
  apply Bool.eqb_prop in H. apply N.eqb_eq in H1. apply IH in H2. subst. reflexivity.
Qed.

(** At a visit, the back stack in canonical phase, and the zone [V] visits later if [jump] applies, with the
    number of steps of the [V] visits. *)
Definition tryJump (b : list item) : option (list item * N) :=
  let cb := canonL b in
  match parseZone cb with
  | None => None
  | Some (n0, (lv, rest)) =>
    let p := toN n0 lv in
    let ps := fst p in
    let top := snd p in
    let V := chooseV ps in
    let ps' := after V ps in
    if andb (andb (andb (andb (andb (andb (N.leb 8 V) (N.eqb (ovf V ps) 0)) (goodN ps' top)) (N.eqb (n0of ps) n0))
       (lv_eqb (physP ps top) lv)) (items_eqb (encZone n0 lv rest) cb)) (ntrT V ps)
    then Some (encZone (n0of ps') (physP ps' top) rest, Z.to_N (Jf V ps))
    else None
  end.

Lemma tryJump_sound : forall b b' k, tryJump b = Some (b', k) ->
  (den b 0inf) {{A}}> 0inf ->> N.to_nat k / (den b' 0inf) {{A}}> 0inf.
Proof.
  intros b b' k H. unfold tryJump in H.
  destruct (parseZone (canonL b)) as [[n0 [lv rest]]|]; [|discriminate].
  set (ps := fst (toN n0 lv)) in *. set (top := snd (toN n0 lv)) in *.
  set (V := chooseV ps) in *. clearbody ps top V.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec end; [|discriminate].
  inversion H; subst b' k. clear H.
  apply andb_true_iff in Ec. destruct Ec as [Ec Ht].
  apply andb_true_iff in Ec. destruct Ec as [Ec He].
  apply andb_true_iff in Ec. destruct Ec as [Ec Hl].
  apply andb_true_iff in Ec. destruct Ec as [Ec Hn].
  apply andb_true_iff in Ec. destruct Ec as [Ec Hg].
  apply andb_true_iff in Ec. destruct Ec as [_ Hv].
  apply N.eqb_eq in Hv. apply N.eqb_eq in Hn. apply lv_eqb_eq in Hl. apply items_eqb_eq in He.
  rewrite <- (den_canonL b). rewrite <- He.
  rewrite !den_encZone. subst n0 lv. rewrite Z_N_nat, Jf_Jz.
  apply (jump ps top (den rest 0inf) V Hv Hg Ht).
Qed.

(** ** The level macros *)

Definition xrun (m : N) (b : list item) : list item :=
  match m with N0 => b | Npos p => Run X p :: b end.

Lemma den_xrun : forall m b t, den (xrun m b) t = X ^^ N.to_nat m *> den b t.
Proof. intros [|p] b t; reflexivity. Qed.

Definition predN (k : positive) : N := (Npos k - 1)%N.
Lemma predN_eq : forall k, predN k = (Npos k - 1)%N. Proof. reflexivity. Qed.
Global Opaque predN.

(** D moving left, front [1 0 (011)^k 1 ...]. *)
Definition macL (f b : list item) : option (list item * list item * N) :=
  match f with
  | Bit S1 :: Bit S0 :: Run w k :: Bit S1 :: Y =>
    if weqb w W then Some (Bit 1 :: Y, xrun (predN k) (Bit 1 :: Bit 0 :: Bit 1 :: Bit 1 :: Bit 0 :: b),
                           (5 + 3 * predN k)%N)
    else None
  | _ => None
  end.

Lemma macL_sound : forall f b f' b' k, macL f b = Some (f', b', k) ->
  sem false f b D -[ tm ]->> N.to_nat k / sem false f' b' D.
Proof.
  intros f b f' b' k H. unfold macL in H.
  destruct f as [|[[]|] [|[[]|] [|[[]|w k0] [|[[]|] Y]]]]; try discriminate.
  destruct (weqb w W) eqn:E; [|discriminate]. apply weqb_eq in E. subst w.
  assert (Ek : k = (5 + 3 * predN k0)%N) by congruence.
  assert (Ek' : N.to_nat k = (5 + 3 * N.to_nat (predN k0))%nat) by (rewrite Ek; lia).
  rewrite Ek'. clear Ek Ek'. inversion H; subst.
  unfold sem, semR. simpl den. rewrite den_xrun. simpl. rewrite predN_eq.
  rewrite pos_pred_N. apply macL_tape.
Qed.

(** C moving right, front [(100)^m 1 0 1 1 0 ...]. *)
Definition macR (f b : list item) : option (list item * list item * N) :=
  match f with
  | Run w m :: Bit S1 :: Bit S0 :: Bit S1 :: Bit S1 :: Bit S0 :: f' =>
    if weqb w X then Some (f', Bit 1 :: Bit 1 :: Run W (m + 1) :: b, (3 * Npos m + 5)%N) else None
  | Bit S1 :: Bit S0 :: Bit S1 :: Bit S1 :: Bit S0 :: f' => Some (f', Bit 1 :: Bit 1 :: Run W 1 :: b, 5%N)
  | _ => None
  end.

Lemma macR_sound : forall f b f' b' k, macR f b = Some (f', b', k) ->
  sem true f b C -[ tm ]->> N.to_nat k / sem true f' b' C.
Proof.
  intros f b f' b' k H. unfold macR in H.
  destruct f as [|[[]|w m] f]; try discriminate.
  - destruct f as [|[[]|] [|[[]|] [|[[]|] [|[[]|] f]]]]; try discriminate.
    inversion H; subst. unfold sem, semR. simpl den.
    apply (macR_tape 0).
  - destruct f as [|[[]|] [|[[]|] [|[[]|] [|[[]|] [|[[]|] f]]]]]; try discriminate.
    destruct (weqb w X) eqn:E; [|discriminate]. apply weqb_eq in E. subst w.
    assert (Ek : k = (3 * Npos m + 5)%N) by congruence.
    assert (Ek' : N.to_nat k = (3 * Pos.to_nat m + 5)%nat) by (rewrite Ek; lia).
    rewrite Ek'. clear Ek Ek'. inversion H; subst.
    unfold sem, semR. simpl den.
    rewrite Pos2Nat.inj_add. change (Pos.to_nat 1) with (S O). rewrite Nat.add_1_r.
    apply macR_tape.
Qed.

(** ** One round, counting steps *)

Record mc := MC { dir : bool; fr : list item; bk : list item; stt : Q; cnt : N }.

Definition semc (c : mc) : Q * tape := sem (dir c) (fr c) (bk c) (stt c).

(** [c'] is reached from [c] in [cnt c' - cnt c] steps. *)
Definition reach (c c' : mc) : Prop :=
  (cnt c <= cnt c')%N /\ semc c -[ tm ]->> (N.to_nat (cnt c') - N.to_nat (cnt c)) / semc c'.

Lemma reach_refl : forall c, reach c c.
Proof. intros c. split; [lia|]. rewrite Nat.sub_diag. constructor. Qed.

Lemma reach_trans : forall c1 c2 c3, reach c1 c2 -> reach c2 c3 -> reach c1 c3.
Proof.
  intros c1 c2 c3 [H1 G1] [H2 G2]. split; [lia|].
  eapply ms_trans; [exact G1|exact G2|lia].
Qed.

Lemma reach_add : forall c c' k, cnt c' = (cnt c + k)%N -> semc c -[ tm ]->> N.to_nat k / semc c' -> reach c c'.
Proof.
  intros c c' k E H. split; [lia|]. rewrite E. eapply ms_eq; [exact H|lia].
Qed.

(** The machine halts [cnt] steps after the configuration [c] was counted. *)
Definition hreach (c : mc) (n : N) : Prop :=
  (cnt c <= n)%N /\ exists ch, semc c -[ tm ]->> (N.to_nat n - N.to_nat (cnt c)) / ch /\ halted tm ch.

Lemma hreach_trans : forall c c' n, reach c c' -> hreach c' n -> hreach c n.
Proof.
  intros c c' n [H1 G1] [H2 [ch [G2 Hh]]]. split; [lia|]. exists ch. split; [|exact Hh].
  eapply ms_trans; [exact G1|exact G2|lia].
Qed.

Inductive rr := RHalt (n : N) | RNext (c : mc).

Definition isA (q : Q) : bool := match q with A => true | _ => false end.
Definition isC (q : Q) : bool := match q with C => true | _ => false end.
Definition isD (q : Q) : bool := match q with D => true | _ => false end.

(** At a visit: canonical phase, then a jump if one applies. *)
Definition atVisit (c : mc) : mc :=
  match c with
  | MC true [] b A n =>
    match tryJump b with
    | Some (b', k) => MC true [] b' A (n + k)
    | None => MC true [] (canonL b) A n
    end
  | _ => c
  end.

Lemma atVisit_sound : forall c, reach c (atVisit c).
Proof.
  intros [[] [|x f] b [] n]; try apply reach_refl.
  unfold atVisit. destruct (tryJump b) as [[b' k]|] eqn:E.
  - apply (reach_add (MC true [] b A n) (MC true [] b' A (n + k)) k eq_refl).
    unfold semc, sem, semR. simpl. apply (tryJump_sound _ _ _ E).
  - apply (reach_add (MC true [] b A n) (MC true [] (canonL b) A n) 0 ltac:(simpl; lia)). unfold semc, sem, semR. simpl. rewrite den_canonL. constructor.
Qed.

Definition macros (c : mc) : option mc :=
  match c with
  | MC false f b D n => match macL f b with Some (f', b', k) => Some (MC false f' b' D (n + k)) | None => None end
  | MC true f b C n => match macR f b with Some (f', b', k) => Some (MC true f' b' C (n + k)) | None => None end
  | _ => None
  end.

Lemma macros_sound : forall c c', macros c = Some c' -> reach c c'.
Proof.
  intros [[] f b [] n] c' H; simpl in H; try discriminate.
  - destruct (macR f b) as [[[f' b'] k]|] eqn:E; inversion H; subst.
    apply (reach_add (MC true f b C n) (MC true f' b' C (n + k)) k eq_refl). apply (macR_sound _ _ _ _ _ E).
  - destruct (macL f b) as [[[f' b'] k]|] eqn:E; inversion H; subst.
    apply (reach_add (MC false f b D n) (MC false f' b' D (n + k)) k eq_refl). apply (macL_sound _ _ _ _ _ E).
Qed.

Definition round (c : mc) : rr :=
  let c1 := atVisit c in
  match macros c1 with
  | Some c2 => RNext c2
  | None =>
    match gstep (tmd tm (dir c1)) (fr c1) (bk c1) (stt c1) with
    | Halt => RHalt (cnt c1)
    | Same f b q k => RNext (MC (dir c1) f b q (cnt c1 + k))
    | Turn f b q => RNext (MC (negb (dir c1)) f b q (cnt c1 + 1))
    end
  end.

Definition rsound (c : mc) (r : rr) : Prop :=
  match r with RHalt n => hreach c n | RNext c' => reach c c' end.

Lemma round_sound : forall c, rsound c (round c).
Proof.
  intros c. unfold round.
  pose proof (atVisit_sound c) as Hv.
  destruct (macros (atVisit c)) as [c2|] eqn:Em.
  - simpl. eapply reach_trans; [exact Hv|]. apply macros_sound. exact Em.
  - destruct (atVisit c) as [d f b q n] eqn:Ea. cbn [dir fr bk stt cnt].
    destruct (gstep (tmd tm d) f b q) as [|f' b' q' k|f' b' q'] eqn:Eg; simpl.
    + eapply hreach_trans; [exact Hv|]. split; [simpl; lia|].
      exists (semc (MC d f b q n)). split.
      * simpl. rewrite Nat.sub_diag. constructor.
      * apply (gstep_sound_halt tm _ _ _ _ Eg).
    + eapply reach_trans; [exact Hv|].
      apply (reach_add (MC d f b q n) (MC d f' b' q' (n + k)) k eq_refl). apply (gstep_sound_same tm _ _ _ _ _ _ _ _ Eg).
    + eapply reach_trans; [exact Hv|].
      apply (reach_add (MC d f b q n) (MC (negb d) f' b' q' (n + 1)) 1 eq_refl). apply (gstep_sound_turn tm _ _ _ _ _ _ _ Eg).
Qed.

(** [p] rounds. *)
Fixpoint run (p : positive) (c : mc) : rr :=
  match p with
  | xH => round c
  | xO p' => match run p' c with RHalt n => RHalt n | RNext c1 => run p' c1 end
  | xI p' =>
    match run p' c with
    | RHalt n => RHalt n
    | RNext c1 => match run p' c1 with RHalt n => RHalt n | RNext c2 => round c2 end
    end
  end.

Lemma seq_sound : forall c r, rsound c r -> forall (g : mc -> rr), (forall c1, rsound c1 (g c1)) ->
  rsound c (match r with RHalt n => RHalt n | RNext c1 => g c1 end).
Proof.
  intros c [n|c1] H g G; [exact H|].
  specialize (G c1). simpl in H. destruct (g c1) as [n|c2]; simpl in *.
  - eapply hreach_trans; [exact H|exact G].
  - eapply reach_trans; [exact H|exact G].
Qed.

Lemma run_sound : forall p c, rsound c (run p c).
Proof.
  induction p as [p IH|p IH|]; intros c; simpl.
  - apply (seq_sound c (run p c) (IH c) (fun c1 => match run p c1 with RHalt n => RHalt n | RNext c2 => round c2 end)).
    intros c1. apply (seq_sound c1 (run p c1) (IH c1) round round_sound).
  - apply (seq_sound c (run p c) (IH c) (run p) IH).
  - apply round_sound.
Qed.

Definition start : mc := MC true [] [] A 0.

Lemma semc_start : semc start = c0.
Proof. reflexivity. Qed.

(** If the run from blank tape halts with count [n], the machine halts after exactly [n] steps (the halting
    transition not counted: [halts_in] counts the steps to the halting configuration). *)
Lemma run_halts_in : forall p n, run p start = RHalt n -> halts_in tm c0 (N.to_nat n).
Proof.
  intros p n H. pose proof (run_sound p start) as G. rewrite H in G.
  destruct G as [_ [ch [G Hh]]]. rewrite semc_start in G. simpl in G.
  exists ch. split; [|exact Hh]. eapply ms_eq; [exact G|lia].
Qed.

(** * Halt *)

(** Splitting a counted run, and the uniqueness of the halting time. *)
Lemma ms_split : forall tm n d c c'', c -[ tm ]->> (n + d) / c'' -> exists c', c -[ tm ]->> n / c' /\ c' -[ tm ]->> d / c''.
Proof.
  intros tm n. induction n as [|n IH]; intros d c c'' H.
  - exists c. split; [constructor|exact H].
  - simpl in H. inversion H as [|k1 x1 c1 x2 Hs Hr]; subst.
    destruct (IH d c1 c'' Hr) as [c' [H1 H2]]. exists c'. split; [econstructor; eassumption|exact H2].
Qed.

Lemma halted_stuck : forall tm c c', halted tm c -> ~ (c -[ tm ]-> c').
Proof.
  intros tm [q [[l s] r]] c' Hh Hs. unfold halted in Hh.
  inversion Hs; subst; congruence.
Qed.

Lemma halts_in_le : forall tm c n m, halts_in tm c n -> halts_in tm c m -> (n <= m)%nat -> n = m.
Proof.
  intros tm c n m [ch1 [H1 Hh1]] [ch2 [H2 Hh2]] Hle.
  destruct (ms_split tm n (m - n) c ch2 ltac:(replace (n + (m - n))%nat with m by lia; exact H2)) as [c' [G1 G2]].
  pose proof (multistep_deterministic _ _ _ _ _ H1 G1) as E. subst c'.
  destruct (m - n)%nat eqn:Ed; [lia|].
  inversion G2 as [|k1 x1 c1 x2 Hs Hr]; subst. exfalso. exact (halted_stuck _ _ _ Hh1 Hs).
Qed.

Lemma halts_in_unique : forall tm c n m, halts_in tm c n -> halts_in tm c m -> n = m.
Proof.
  intros tm c n m H1 H2. destruct (Nat.le_ge_cases n m).
  - exact (halts_in_le _ _ _ _ H1 H2 H).
  - symmetry. exact (halts_in_le _ _ _ _ H2 H1 H).
Qed.

(** The number of steps to the halting configuration (the halting transition, the bbchallenge convention,
    adds one: 853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808111420498351739937140047615589683). *)
Definition K : N := 853177647932005270554892218084645935472995035642746848454477793277027802995098762076895667304703808111420498351739937140047615589682%N.

Lemma run_halts : run 33554432%positive start = RHalt K.
Proof. vm_cast_no_check (eq_refl (RHalt K)). Time Qed.

Theorem halts_172044 : halts tm c0.
Proof. exists (N.to_nat K). exact (run_halts_in _ _ run_halts). Qed.

(** The machine reaches its halting configuration after exactly K steps, and only then. *)
Theorem steps_172044 : halts_in tm c0 (N.to_nat K) /\ forall n, halts_in tm c0 n -> n = N.to_nat K.
Proof.
  pose proof (run_halts_in _ _ run_halts) as H. split; [exact H|].
  intros n Hn. exact (halts_in_unique _ _ _ _ Hn H).
Qed.

End M172044.

Print Assumptions M172044.halts_172044.
Print Assumptions M172044.steps_172044.
