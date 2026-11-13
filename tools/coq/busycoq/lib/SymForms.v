(** * SymForms: phase forms as token templates, and rules checked by [auto]

    A form is a configuration template [m : MC] whose run counts are linear in the form's own variables; its value
    at numbers [x] is [cden x m].  A rule from [m1] at arguments [s1] to [m2] at arguments [s2] (lists of linear
    expressions in the rule's variables) is checked by running [auto] from [m1] with its counts substituted. *)

From Coq Require Import Lists.List Lia PeanoNat Bool. Import ListNotations.
From BusyCoq Require Export SymRun.
Set Default Goal Selector "!".
Local Open Scope nat_scope.
Local Notation "a && b" := (andb a b).
Local Notation "a || b" := (orb a b).

Definition substTok (s : list Lin) (t : Tok) : Tok :=
  match t with TB v => TB v | TR w n => TR w (lsubst n s) end.
Definition substT (s : list Lin) (ts : list Tok) : list Tok := List.map (substTok s) ts.
Definition substMC (s : list Lin) (c : MC) : MC := mkMC (substT s (ml c)) (substT s (mr c)) (mst c).
Definition evs (s : list Lin) (x : list nat) : list nat := List.map (fun e => eval e x) s.

Lemma den_subst : forall s x ts t, den x (substT s ts) t = den (evs s x) ts t.
Proof.
  intros s x. induction ts as [| [v | w n] ts IH]; intros t; cbn [substT List.map substTok den].
  - reflexivity.
  - rewrite <- IH. reflexivity.
  - rewrite <- IH, eval_lsubst. reflexivity.
Qed.

Lemma cden_subst : forall s x c, cden x (substMC s c) = cden (evs s x) c.
Proof. intros s x [l r q]. unfold cden, substMC. cbn [ml mr mst]. rewrite !den_subst. reflexivity. Qed.

Section Rules.
Variable tm : TM.
Variable K : nat.
Variable nf : list Tok -> list Tok.
Hypothesis nf_den : forall x ts, den x (nf ts) blank = den x ts blank.

Definition ruleL (f : nat) (m1 : MC) (s1 : list Lin) (m2 : MC) (s2 : list Lin) : bool :=
  match ml m2 with
  | [] => auto tm K nf (mst m2) true (nf (substT s2 (mr m2))) f false (substMC s1 m1)
  | _ => false
  end.
Definition ruleR (f : nat) (m1 : MC) (s1 : list Lin) (m2 : MC) (s2 : list Lin) : bool :=
  match mr m2 with
  | [] => auto tm K nf (mst m2) false (nf (substT s2 (ml m2))) f false (substMC s1 m1)
  | _ => false
  end.
Definition rule (f : nat) (m1 : MC) (s1 : list Lin) (m2 : MC) (s2 : list Lin) : bool :=
  ruleL f m1 s1 m2 s2 || ruleR f m1 s1 m2 s2.

Theorem rule_sound : forall f m1 s1 m2 s2, rule f m1 s1 m2 s2 = true ->
  forall x, cden (evs s1 x) m1 -[ tm ]->+ cden (evs s2 x) m2.
Proof.
  intros f m1 s1 m2 s2 H x. rewrite <- cden_subst.
  unfold rule in H. apply orb_true_iff in H as [H | H].
  - unfold ruleL in H. destruct m2 as [l2 r2 q2]. cbn [ml mr mst] in H. destruct l2; [| discriminate].
    pose proof (auto_reach tm K nf nf_den _ _ _ _ _ H x) as R.
    replace (cden (evs s2 x) (mkMC [] r2 q2)) with (cden x (tgt q2 true (nf (substT s2 r2)))); [exact R |].
    unfold tgt, cden. cbn [ml mr mst den]. rewrite nf_den, den_subst. reflexivity.
  - unfold ruleR in H. destruct m2 as [l2 r2 q2]. cbn [ml mr mst] in H. destruct r2; [| discriminate].
    pose proof (auto_reach tm K nf nf_den _ _ _ _ _ H x) as R.
    replace (cden (evs s2 x) (mkMC l2 [] q2)) with (cden x (tgt q2 false (nf (substT s2 l2)))); [exact R |].
    unfold tgt, cden. cbn [ml mr mst den]. rewrite nf_den, den_subst. reflexivity.
Qed.
End Rules.

(** Turning [evs s x] into the arguments as written. *)
Ltac evs_eq := unfold evs, eval; cbn [List.map lc la dot];
  repeat (apply (f_equal2 (@cons nat)); [lia |]); reflexivity.

(** Trying the normal forms in turn. *)
Definition rules (tm : TM) (K f : nat) (m1 : MC) (s1 : list Lin) (m2 : MC) (s2 : list Lin) : bool :=
  rule tm K normS f m1 s1 m2 s2 || rule tm K normL f m1 s1 m2 s2 || rule tm K normG f m1 s1 m2 s2.
Theorem rules_sound : forall tm K f m1 s1 m2 s2, rules tm K f m1 s1 m2 s2 = true ->
  forall x, cden (evs s1 x) m1 -[ tm ]->+ cden (evs s2 x) m2.
Proof.
  intros tm K f m1 s1 m2 s2 H. unfold rules in H.
  apply orb_true_iff in H as [H | H]; [apply orb_true_iff in H as [H | H] |].
  - exact (rule_sound tm K normS normS_den f m1 s1 m2 s2 H).
  - exact (rule_sound tm K normL normL_den f m1 s1 m2 s2 H).
  - exact (rule_sound tm K normG normG_den f m1 s1 m2 s2 H).
Qed.

(** ** Equal forms

    Two forms are equal when, after writing each run of a repeated word [u^k] as a run of [u] and normalizing,
    they are the same token lists. *)
Fixpoint rootFrom (d : nat) (fuel : nat) (w : list sym) : option (list sym * nat) :=
  match fuel with
  | 0 => None
  | S fuel =>
    if Nat.leb (length w) d then None else
    if (Nat.eqb (length w mod d) 0 && w_eqb (firstn d w ^^ (length w / d)) w)%bool
    then Some (firstn d w, length w / d) else rootFrom (S d) fuel w
  end.
Lemma rootFrom_eq : forall fuel d w u k, rootFrom d fuel w = Some (u, k) -> w = u ^^ k.
Proof.
  induction fuel as [| fuel IH]; intros d w u k H; [discriminate |]. cbn [rootFrom] in H.
  destruct (Nat.leb (length w) d); [discriminate |].
  destruct (Nat.eqb (length w mod d) 0 && w_eqb (firstn d w ^^ (length w / d)) w)%bool eqn:E.
  - inversion H. subst. apply andb_true_iff in E as [_ E]. apply w_eqb_eq in E. symmetry. exact E.
  - eapply IH. exact H.
Qed.

Definition rootTok (t : Tok) : Tok :=
  match t with
  | TR w n => match rootFrom 1 (length w) w with Some (u, k) => TR u (lscale k n) | None => t end
  | _ => t
  end.
Lemma rootTok_den : forall x t r, den x [rootTok t] r = den x [t] r.
Proof.
  intros x [v | w n] r; [reflexivity |]. unfold rootTok.
  destruct (rootFrom 1 (length w) w) as [[u k] |] eqn:E; [| reflexivity].
  apply rootFrom_eq in E. subst w. cbn [den]. rewrite eval_lscale, lpow_mul. reflexivity.
Qed.
Lemma rootT_den : forall x ts r, den x (List.map rootTok ts) r = den x ts r.
Proof.
  induction ts as [| t ts IH]; intros r; [reflexivity |].
  cbn [List.map]. rewrite den_cons, IH, rootTok_den, <- den_cons. reflexivity.
Qed.

Definition nfR (ts : list Tok) : list Tok := normS (List.map rootTok ts).
Lemma nfR_den : forall x ts, den x (nfR ts) blank = den x ts blank.
Proof. intros. unfold nfR. rewrite normS_den, rootT_den. reflexivity. Qed.

Definition formeq (m1 : MC) (s1 : list Lin) (m2 : MC) (s2 : list Lin) : bool :=
  st_eqb (mst m1) (mst m2) && toks_eqb (nfR (substT s1 (ml m1))) (nfR (substT s2 (ml m2)))
  && toks_eqb (nfR (substT s1 (mr m1))) (nfR (substT s2 (mr m2))).
Theorem formeq_sound : forall m1 s1 m2 s2, formeq m1 s1 m2 s2 = true ->
  forall x, cden (evs s1 x) m1 = cden (evs s2 x) m2.
Proof.
  intros m1 s1 m2 s2 H x. unfold formeq in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply st_eqb_eq in H1. apply toks_eqb_eq in H2, H3.
  rewrite <- !cden_subst. unfold cden, substMC. cbn [ml mr mst].
  rewrite <- (nfR_den x (substT s1 (ml m1))), <- (nfR_den x (substT s1 (mr m1))), H2, H3, nfR_den, nfR_den, H1.
  reflexivity.
Qed.
