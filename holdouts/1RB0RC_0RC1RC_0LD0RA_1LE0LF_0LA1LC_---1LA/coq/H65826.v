(** * 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA (bbchallenge 65826) does not halt

    The machine goes from blank tape to [Cyc 16797709], and from [Cyc (65 + 2 x)] to
    [Cyc (65 + 2 (x + 160521464))] for every [x], where

      [Cyc r = E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r]

    (blank on both sides, the head on the first cell written).  Both facts are runs of the verified symbolic
    executor of [SymExecN.v] ([arrive_run]: 5,037,044 moves; [period_run]: 5,581,714 moves with the count of the
    last block [65 + 2 x], [x] free), evaluated by [vm_compute] and turned into statements about the machine by
    the soundness theorem of the executor.  The tables of the executor (31 shift rules, 12 cycle rules) are
    checked in [H65826_Data.v] and [H65826_Rules.v]. *)

From Coq Require Import Lists.List NArith Lia. Import ListNotations.
From BusyCoq Require Import H65826_Rules H65826_Arrive H65826_Period.
Set Default Goal Selector "!".
Local Open Scope N_scope.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** [E> 0 (1011001)^59 1011 00000 1101100110110 (011)^16 001101100110 (011)^r] *)
Definition Cyc (r : N) : Q * tape :=
  const S0 {{E}}>
    [S0] *> [S1; S0; S1; S1; S0; S0; S1] ^^ 59 *> [S1; S0; S1; S1] *> [S0; S0; S0; S0; S0] *>
    [S1; S1; S0; S1; S1; S0; S0; S1; S1; S0; S1; S1; S0] *> [S0; S1; S1] ^^ 16 *>
    [S0; S0; S1; S1; S0; S1; S1; S0; S0; S1; S1; S0] *> [S0; S1; S1] ^^ N.to_nat r *> const S0.

(** The tokens of [cycToks n] stand for [Cyc], with [n] copies of 011 in the last block. *)
Lemma den_cyc : forall rho n, den rho (mkSC [] (cycToks n) E) = Cyc (ev rho n).
Proof.
  intros rho n. unfold den, conf, Cyc, cycToks. cbn [sl sr sq dn]. unfold rep.
  rewrite <- (const_unfold _ S0). reflexivity.
Qed.

Global Opaque Cyc.

(** The run from blank tape reaches [Cyc 16797709]. *)
Lemma reach : c0 -->* Cyc 16797709.
Proof.
  pose proof (runTo_sound tm E thr stratMin T T_ok _ _ _ arrive_run (fun _ => 0)) as H.
  rewrite den_cyc in H. change (ev (fun _ => 0) (mkC 16797709 [])) with (16797709 + 0) in H.
  rewrite N.add_0_r in H. exact H.
Qed.

(** One period of the growth cycle, for every value of the free count. *)
Lemma grow : forall x, Cyc (65 + 2 * x) -->+ Cyc (65 + 2 * (x + 160521464)).
Proof.
  intros x. pose proof (runTo1_sound tm E thr stratMin T T_ok _ _ _ period_run (fun _ => x)) as H.
  rewrite !den_cyc in H.
  replace (ev (fun _ => x) (mkC 65 [2])) with (65 + 2 * x) in H by (unfold ev; cbn [cc ca dot]; lia).
  replace (ev (fun _ => x) (mkC 321042993 [2])) with (65 + 2 * (x + 160521464)) in H
    by (unfold ev; cbn [cc ca dot]; lia).
  exact H.
Qed.

(** The machine does not halt from blank tape. *)
Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (multistep_nonhalt _ _ _ reach).
  change 16797709 with (65 + 2 * 8398822).
  apply (progress_nonhalt_simple tm N (fun x => Cyc (65 + 2 * x))).
  intros x. exists (x + 160521464). apply grow.
Qed.

Print Assumptions nonhalt.
