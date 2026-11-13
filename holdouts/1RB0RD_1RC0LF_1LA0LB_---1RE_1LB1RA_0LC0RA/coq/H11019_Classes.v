(** * 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA (bbchallenge 11019): the machine, round ends and their classes

    A round end is the configuration [node B T = A> 01001000 (01)^B T] (blank on both sides, the head on the
    first cell written).  A class [c : Cls] is the set of round ends [node (r0 c + m c * x) (tail c)], [x >= 0].
    [clsRun T c] runs the executor of [SymExecN.v] from that node with [x] free and tests that it ends at
    [node (k c + c c * x) (to c)]; [covers cs c] tests that every [k c + c c * x] lies in a class of the list
    [cs] with tail [to c].  Both tests are proved sound here, so a list of classes that passes them is closed
    under "next round end" ([closed_of_checks]). *)

From Coq Require Import Lists.List NArith Lia Bool String Ascii. Import ListNotations.
From BusyCoq Require Export SymExecN.
Set Default Goal Selector "!".
Local Open Scope N_scope.

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, S0 => Some (S1, R, B)  | A, S1 => Some (S0, R, D)
  | B, S0 => Some (S1, R, C)  | B, S1 => Some (S0, L, F)
  | C, S0 => Some (S1, L, A)  | C, S1 => Some (S0, L, B)
  | D, S0 => None             | D, S1 => Some (S1, R, E)
  | E, S0 => Some (S1, L, B)  | E, S1 => Some (S1, R, A)
  | F, S0 => Some (S0, L, C)  | F, S1 => Some (S0, R, A)
  end.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** The executor for this machine: events are state A at the left end of the tape; blocks of fewer than 4 copies
    are written out; a cycle rule is applied a number of times that may have a variable. *)
Definition thr : N := 4.
Notation TOK := (TblOK tm A).
Notation RUN := (run tm A thr stratLin).
Notation MOVES := (moveS tm A thr stratLin).

(** A word written as a string of 0s and 1s. *)
Fixpoint bits (s : string) : list sym :=
  match s with
  | EmptyString => []
  | String c s' => (if Ascii.eqb c "1"%char then S1 else S0) :: bits s'
  end.

Definition pre : list sym := [S0; S1; S0; S0; S1; S0; S0; S0].

(** A round end: [A> 01001000 (01)^B T]. *)
Definition node (B : N) (T : list sym) : Q * tape :=
  const S0 {{A}}> pre *> [S0; S1] ^^ N.to_nat B *> T *> const S0.

(** The same as a configuration of the executor, the count of the big block a count with variables. *)
Definition nodeS (n : Cnt) (T : list sym) : SCfg :=
  mkSC [] (List.map cell pre ++ blk [S0; S1] n :: List.map cell T) A.

Lemma dn_cells' : forall rho w, dn rho (List.map cell w) = w *> const S0.
Proof. intros. rewrite <- (app_nil_r (List.map cell w)), dn_cells. reflexivity. Qed.

Lemma den_nodeS : forall rho n T, den rho (nodeS n T) = node (ev rho n) T.
Proof.
  intros. unfold den, nodeS, node, conf. cbn [sl sr sq]. rewrite dn_cells. cbn [dn]. rewrite dn_cells'.
  reflexivity.
Qed.

(** The configuration is the round end [node n T] (compared in the form [canon]). *)
Definition atNode (X : SCfg) (n : Cnt) (T : list sym) : bool :=
  andb (isNil (sl X)) (andb (qeqb (sq X) A) (tokseqb (canon thr (sr X)) (canon thr (sr (nodeS n T))))).

Lemma atNode_spec : forall X n T, atNode X n T = true -> forall rho, den rho X = node (ev rho n) T.
Proof.
  intros [l r q] n T H rho. unfold atNode in H. cbn [sl sr sq] in H.
  apply andb_true_iff in H. destruct H as [Hl H]. apply andb_true_iff in H. destruct H as [Hq Hr].
  destruct l; [|discriminate]. apply qeqb_eq in Hq. apply tokseqb_eq in Hr. subst q.
  rewrite <- den_nodeS. unfold den. cbn [sl sr sq]. f_equal.
  rewrite <- (canon_spec thr rho r), Hr, canon_spec. reflexivity.
Qed.

(** A class of round ends and what one round does to it: the tail; the big block has [r0 + m x] words; the round
    takes one machine step and [K] more moves of the executor; the next round end has tail [to] and [k + c x]
    words in the big block. *)
Record Cls := mkCls { tail : list sym; r0 : N; m : N; K : N; to : list sym; k : N; c : N }.

(** One round from the class, the count of the big block free: the executor ends at the announced round end. *)
Definition clsRun (T : Tbl) (d : Cls) : bool :=
  match MOVES T (nodeS (mkC (r0 d) [m d]) (tail d)) with
  | Some X =>
    match RUN T (K d) X with
    | Some Y => atNode Y (mkC (k d) [c d]) (to d)
    | None => false
    end
  | None => false
  end.

Lemma ev1 : forall a b x, ev (fun _ => x) (mkC a [b]) = a + b * x.
Proof. intros. unfold ev. cbn [cc ca dot]. lia. Qed.

Lemma clsRun_sound : forall T, TOK T -> forall d, clsRun T d = true ->
  forall x, node (r0 d + m d * x) (tail d) -->+ node (k d + c d * x) (to d).
Proof.
  intros T HT d H x. unfold clsRun in H.
  destruct (MOVES T (nodeS (mkC (r0 d) [m d]) (tail d))) as [X|] eqn:Hm; [|discriminate].
  destruct (RUN T (K d) X) as [Y|] eqn:Hr; [|discriminate].
  pose proof (moveS_sound tm A thr stratLin (fun _ => x) _ _ _ HT Hm) as h1.
  pose proof (run_sound tm A thr stratLin T HT _ _ _ Hr (fun _ => x)) as h2.
  rewrite den_nodeS, ev1 in h1. rewrite (atNode_spec _ _ _ H), ev1 in h2.
  eapply progress_evstep_trans; eassumption.
Qed.

(** The round ends of a list of classes. *)
Definition InSet (cs : list Cls) (B : N) (T : list sym) : Prop :=
  exists d, In d cs /\ exists x, T = tail d /\ B = r0 d + m d * x.

Lemma exists_mul : forall a b M, 0 < M -> b <= a -> a mod M = b mod M -> exists x, a = b + M * x.
Proof.
  intros a b M HM Hle H. exists ((a - b) / M). rewrite (divsub M a b HM H Hle). lia.
Qed.

(** The classes with a given tail. *)
Definition cands (cs : list Cls) (T : list sym) : list Cls := filter (fun d => weqb (tail d) T) cs.

(** A common multiple of their moduli. *)
Definition period (l : list Cls) : N := fold_left (fun a d => N.lcm a (m d)) l 1.

Definition fits (d : Cls) (B : N) : bool :=
  andb (0 <? m d) (andb (r0 d <=? B) (B mod m d =? r0 d mod m d)).

Lemma fits_spec : forall d B, fits d B = true -> exists x, B = r0 d + m d * x.
Proof.
  intros d B H. apply andb_true_iff in H. destruct H as [H0 H]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply N.ltb_lt in H0. apply N.leb_le in H1. apply N.eqb_eq in H2. exact (exists_mul _ _ _ H0 H1 H2).
Qed.

(** [B] words with tail [T] is a round end of the list. *)
Definition inSetB (cs : list Cls) (B : N) (T : list sym) : bool := existsb (fun d => fits d B) (cands cs T).

Lemma cands_in : forall cs T d, In d (cands cs T) -> In d cs /\ T = tail d.
Proof.
  intros cs T d H. apply filter_In in H. destruct H as [H1 H2]. apply weqb_eq in H2. auto.
Qed.

Lemma inSetB_sound : forall cs B T, inSetB cs B T = true -> InSet cs B T.
Proof.
  intros cs B T H. apply existsb_exists in H. destruct H as [d [Hd Hf]].
  destruct (cands_in _ _ _ Hd) as [H1 H2]. destruct (fits_spec _ _ Hf) as [x Hx].
  exists d. split; [exact H1|]. exists x. auto.
Qed.

(** Every [k + c x] is in a class of [cs] with tail [to]: tested for [x] below a period [P], each class used
    having a modulus that divides [c * P]. *)
Definition covers (cs : list Cls) (d : Cls) : bool :=
  let l := cands cs (to d) in
  let P := period l in
  andb (0 <? P)
    (forallb (fun j => existsb (fun e => andb (fits e (k d + c d * j)) ((c d * P) mod m e =? 0)) l)
       (List.map N.of_nat (seq 0 (N.to_nat P)))).

Lemma covers_sound : forall cs d, covers cs d = true -> forall x, InSet cs (k d + c d * x) (to d).
Proof.
  intros cs d H x. unfold covers in H. cbv zeta in H. set (P := period (cands cs (to d))) in H.
  apply andb_true_iff in H. destruct H as [HP H]. apply N.ltb_lt in HP.
  pose proof (N.div_mod' x P) as Ex. assert (Hj : x mod P < P) by (apply N.mod_lt; lia).
  assert (Hin : In (x mod P) (List.map N.of_nat (seq 0 (N.to_nat P)))).
  { apply in_map_iff. exists (N.to_nat (x mod P)). split; [apply N2Nat.id|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as He. cbv beta in He.
  apply existsb_exists in He. destruct He as [e [He Hc]]. apply andb_true_iff in Hc. destruct Hc as [Hf Hd].
  destruct (cands_in _ _ _ He) as [H1 H2]. apply N.eqb_eq in Hd.
  apply andb_true_iff in Hf. destruct Hf as [H0 Hf]. apply andb_true_iff in Hf. destruct Hf as [Hle Hmod].
  apply N.ltb_lt in H0. apply N.leb_le in Hle. apply N.eqb_eq in Hmod.
  pose proof (N.div_mod' (c d * P) (m e)) as Ec. rewrite Hd, N.add_0_r in Ec.
  assert (E : k d + c d * x = k d + c d * (x mod P) + (c d * P / m e * (x / P)) * m e) by nia.
  assert (Hx : exists y, k d + c d * x = r0 e + m e * y).
  { assert (Hm : c d * (x mod P) <= c d * x) by (apply N.mul_le_mono_l, N.Div0.mod_le).
    apply exists_mul; [exact H0 | lia |]. rewrite E, N.Div0.mod_add. exact Hmod. }
  destruct Hx as [y Hy]. exists e. split; [exact H1|]. exists y. auto.
Qed.

(** A list of classes that passes both tests is closed under "next round end". *)
Theorem closed_of_checks : forall T, TOK T -> forall cs,
  forallb (fun d => andb (clsRun T d) (covers cs d)) cs = true ->
  forall B Tl, InSet cs B Tl -> exists B' Tl', InSet cs B' Tl' /\ node B Tl -->+ node B' Tl'.
Proof.
  intros T HT cs H B Tl [d [Hd [x [-> ->]]]].
  pose proof (proj1 (forallb_forall _ _) H d Hd) as Hc. cbv beta in Hc.
  apply andb_true_iff in Hc. destruct Hc as [Hr Hc].
  exists (k d + c d * x), (to d). split; [exact (covers_sound _ _ Hc x) | exact (clsRun_sound T HT d Hr x)].
Qed.

(** The run from blank tape reaches a round end, in [K] moves of the executor. *)
Definition arrives (T : Tbl) (K B : N) (Tl : list sym) : bool :=
  match RUN T K (mkSC [] [] A) with
  | Some X => atNode X (mkC B []) Tl
  | None => false
  end.

Lemma arrives_sound : forall T, TOK T -> forall K B Tl, arrives T K B Tl = true -> c0 -->* node B Tl.
Proof.
  intros T HT K B Tl H. unfold arrives in H. destruct (RUN T K (mkSC [] [] A)) as [X|] eqn:Hr; [|discriminate].
  pose proof (run_sound tm A thr stratLin T HT _ _ _ Hr (fun _ => 0)) as h.
  rewrite (atNode_spec _ _ _ H) in h. unfold ev in h. cbn [cc ca dot] in h. rewrite N.add_0_r in h. exact h.
Qed.

(** The set of round ends of a closed list of classes is never left, so the machine does not halt from any
    configuration that reaches it. *)
Theorem nonhalt_of_closed : forall T, TOK T -> forall cs,
  forallb (fun d => andb (clsRun T d) (covers cs d)) cs = true ->
  forall KA B Tl, arrives T KA B Tl = true -> inSetB cs B Tl = true -> ~ halts tm c0.
Proof.
  intros T HT cs H KA B Tl Ha Hs.
  apply (multistep_nonhalt _ _ _ (arrives_sound T HT _ _ _ Ha)).
  apply (progress_nonhalt tm (fun cf => exists B' Tl', InSet cs B' Tl' /\ cf = node B' Tl')).
  - intros cf [B1 [T1 [Hin ->]]]. destruct (closed_of_checks T HT cs H _ _ Hin) as [B2 [T2 [Hin2 Hstep]]].
    exists (node B2 T2). split; [|exact Hstep]. exists B2, T2. auto.
  - exists B, Tl. split; [exact (inSetB_sound _ _ _ Hs) | reflexivity].
Qed.
