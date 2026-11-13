(** * 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC--- (bbchallenge 32641) never halts

    From blank tape the machine reaches [Cyc X 7 = 0^inf A> 0 (1010001000100)^7 X 0^inf], where [X] is the tape
    right of the seven blocks at that moment (222,182 cells and some blanks; step 16,730,681,219).  From there
    [Cyc X (n+1) -->+ Cyc X (n+2)] for every [n] ([H32641_Period.period]), so it never halts.

    Computed here by [vm_compute]: the five facts [L_blank], [R_blocks], [exc1_end], [exc2_end], [exc_close]
    about the last macro configuration and about the two excursions into [X] (window runs of 1,517,479 and
    1,511,551 machine steps).  The reach itself is [H32641_Reach.reach]. *)

From Coq Require Import Lists.List PArith. Import ListNotations.
From BusyCoq Require Import H32641_Period H32641_Reach.
Set Default Goal Selector "!".

(** The cells of a list of blocks. *)
Fixpoint cells (bs : list positive) : list sym :=
  match bs with [] => [] | b :: bs => dec b ++ cells bs end.
Lemma decs_cells : forall bs, decs bs = cells bs *> const 0.
Proof.
  induction bs as [| b bs IH]; cbn [decs cells]; [reflexivity |].
  rewrite Str_app_assoc, IH. reflexivity.
Qed.

Definition is0 (s : sym) : bool := match s with 0 => true | 1 => false end.

(** A macro configuration that faces left in state A, with blanks on the left and [k] blocks first on the right,
    is [Cyc X k], [X] being the rest of its right side. *)
Lemma final_cfg : forall c n k, mf c = false -> mq c = A -> forallb is0 (cells (mL c)) = true ->
  firstn n (cells (mR c)) = accb ^^ k -> msem c = Cyc (skipn n (cells (mR c))) k.
Proof.
  intros [Ls Rs q f] n k Hf Hq HL HR. cbn [mf mq mL mR] in *. subst f q.
  unfold msem, Cyc. cbn [mf mq mL mR]. rewrite !decs_cells, (zeros_const _ HL).
  set (X := skipn n (cells Rs)).
  assert (E : cells Rs = accb ^^ k ++ X) by (rewrite <- HR; symmetry; apply firstn_skipn).
  rewrite E, Str_app_assoc. reflexivity.
Qed.

(** Equality of cell lists, as a computation. *)
Fixpoint leqb (a b : list sym) : bool :=
  match a, b with
  | [], [] => true
  | 0 :: a, 0 :: b => leqb a b
  | 1 :: a, 1 :: b => leqb a b
  | _, _ => false
  end.
Lemma leqb_ok : forall a b, leqb a b = true -> a = b.
Proof.
  induction a as [| x a IH]; intros [| y b] H; cbn [leqb] in H; try discriminate; [reflexivity | | ].
  - destruct x; discriminate.
  - destruct x, y; try discriminate; f_equal; apply IH; exact H.
Qed.

Lemma start_cfg : msem cfg0 = c0.
Proof.
  unfold msem, cfg0. cbn [mf mq mL mR decs]. rewrite (zeros_const (dec 64) eq_refl). reflexivity.
Qed.

(** The stretch: the right side of the last macro configuration after its first 7 * 13 cells. *)
Notation X := (skipn 91 (cells (mR cfg16))).
Notation n1 := 1517479%positive.
Notation n2 := 1511551%positive.

Lemma L_blank : forallb is0 (cells (mL cfg16)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma R_blocks : firstn 91 (cells (mR cfg16)) = accb ^^ 7.
Proof. apply leqb_ok. vm_cast_no_check (eq_refl true). Qed.

Lemma exc1_end : (wl (exc1 X 32 n1), wq (exc1 X 32 n1), wf (exc1 X 32 n1)) = ([0], E, false).
Proof. vm_cast_no_check (eq_refl ([0], E, false)). Qed.

Lemma exc2_end : (wl (exc2 X 32 n1 n2), wq (exc2 X 32 n1 n2), wf (exc2 X 32 n1 n2)) = ([0], E, false).
Proof. vm_cast_no_check (eq_refl ([0], E, false)). Qed.

Lemma exc_close : [1;0] ++ wr (exc2 X 32 n1 n2) = accb ++ X ++ repeat 0 23.
Proof. apply leqb_ok. vm_cast_no_check (eq_refl true). Qed.

Theorem cycle : forall n, Cyc X (S n) -->+ Cyc X (S (S n)).
Proof. exact (period X 32 23 n1 n2 exc1_end exc2_end exc_close). Qed.

Theorem reach_cycle : c0 -->* Cyc X 7.
Proof.
  rewrite <- start_cfg, <- (final_cfg cfg16 91 7 eq_refl eq_refl L_blank R_blocks). exact reach.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt tm c0 (Cyc X 7) reach_cycle).
  apply (progress_nonhalt_simple tm nat (fun i => Cyc X (S i)) 6).
  intros i. exists (S i). apply cycle.
Qed.

Print Assumptions nonhalt.
