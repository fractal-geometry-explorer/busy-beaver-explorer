(** Segmented replay of a visit map: the part that does not depend on the machine.

    A machine supplies a map [opz] on a specification state (integers in [Z]) and a fast version of it on
    63-bit machine integers.  This file gives the runner that follows the fast version for a given number of
    visits, proves that what it returns is the iterate of [opz], and gives the lemmas that chain segments.
    Nothing here uses [native_compute]; only the segment files of a particular machine do. *)
From Coq Require Import ZArith Lia Uint63 Bool PArith.
Local Open Scope Z_scope.
Notation "'φ' x" := (Uint63.to_Z x) (at level 0).

(** int comparisons as Z comparisons *)
Lemma eqb_Z x y : (x =? y)%uint63 = (φ x =? φ y).
Proof.
  destruct (x =? y)%uint63 eqn:E; symmetry.
  - apply Uint63.eqb_spec in E. subst. apply Z.eqb_refl.
  - apply Z.eqb_neq. intro H. apply to_Z_inj in H. subst.
    rewrite (proj2 (Uint63.eqb_spec y y) eq_refl) in E. discriminate.
Qed.
Lemma ltb_Z x y : (x <? y)%uint63 = (φ x <? φ y).
Proof.
  destruct (x <? y)%uint63 eqn:E; symmetry;
    [apply Z.ltb_lt, ltb_spec, E|apply Z.ltb_ge; rewrite <- Z.nlt_ge, <- ltb_spec, E; discriminate].
Qed.
Lemma leb_Z x y : (x <=? y)%uint63 = (φ x <=? φ y).
Proof.
  destruct (x <=? y)%uint63 eqn:E; symmetry;
    [apply Z.leb_le, leb_spec, E|apply Z.leb_gt; rewrite <- Z.nle_gt, <- leb_spec, E; discriminate].
Qed.

Section Iter.
  Context {ZS : Type} (opz : ZS -> ZS).

  (** [zit k z]: k visits from z. *)
  Fixpoint zit (k : nat) (z : ZS) : ZS := match k with O => z | S k => zit k (opz z) end.

  Lemma zit_add m n z : zit (m + n) z = zit n (zit m z).
  Proof. revert z. induction m as [|m IH]; intros z; [reflexivity|]. apply IH. Qed.

  (** Chaining two segments. *)
  Lemma zit_chain {x y z : ZS} {k1 k2 : nat} : zit k1 x = y -> zit k2 y = z -> zit (k1 + k2) x = z.
  Proof. intros H1 H2. rewrite zit_add, H1. exact H2. Qed.

  (** A fixed point of the map (the halted state) stays put. *)
  Lemma zit_fix k z : opz z = z -> zit k z = z.
  Proof. intros H. induction k as [|k IH]; [reflexivity|]. cbn. rewrite H. exact IH. Qed.
End Iter.

Section Runner.
  Context {St ZS : Type} (zs : St -> ZS) (opz : ZS -> ZS).

  (** [one n i s] advances from visit i (i < n) by some number of visits, never past n.  It may return
      (i, s) unchanged when it cannot go on (a value too large for the machine arithmetic); the segment check
      then fails, it never succeeds wrongly.  A machine may put any accelerated step here, as long as it
      proves [one_ok] for it. *)
  Context (one : int -> int -> St -> int * St).
  Definition one_spec : Prop := forall n i s, φ i < φ n ->
    φ i <= φ (fst (one n i s)) <= φ n /\
    zs (snd (one n i s)) = zit opz (Z.to_nat (φ (fst (one n i s)) - φ i)) (zs s).
  Context (one_ok : one_spec).

  Fixpoint run (p : positive) (n i : int) (s : St) : int * St :=
    if (i =? n)%uint63 then (i, s) else
    match p with
    | xH => one n i s
    | xO p => let '(i, s) := run p n i s in run p n i s
    | xI p => let '(i, s) := run p n i s in let '(i, s) := run p n i s in
              if (i =? n)%uint63 then (i, s) else one n i s
    end.

  Definition good (n i0 : int) (s0 : St) (t : int * St) : Prop :=
    φ i0 <= φ (fst t) <= φ n /\ zs (snd t) = zit opz (Z.to_nat (φ (fst t) - φ i0)) (zs s0).

  Lemma good_refl n i s : φ i <= φ n -> good n i s (i, s).
  Proof. intros H. split; cbn [fst snd]; [lia|]. rewrite Z.sub_diag. reflexivity. Qed.

  Lemma good_trans n i0 s0 i1 s1 t : good n i0 s0 (i1, s1) -> good n i1 s1 t -> good n i0 s0 t.
  Proof.
    intros [B1 E1] [B2 E2]. cbn [fst snd] in *. split; [lia|].
    replace (Z.to_nat (φ (fst t) - φ i0)) with (Z.to_nat (φ i1 - φ i0) + Z.to_nat (φ (fst t) - φ i1))%nat by lia.
    rewrite zit_add, <- E1. exact E2.
  Qed.

  Lemma one_good n i s : φ i <= φ n -> good n i s (if (i =? n)%uint63 then (i, s) else one n i s).
  Proof.
    intros H. rewrite eqb_Z. destruct (Z.eqb_spec φ i φ n); [apply good_refl; exact H|].
    apply one_ok. lia.
  Qed.

  Lemma run_good p : forall n i s, φ i <= φ n -> good n i s (run p n i s).
  Proof.
    induction p as [p IH|p IH|]; intros n i s H; cbn [run].
    - rewrite eqb_Z. destruct (Z.eqb_spec φ i φ n); [apply good_refl; exact H|].
      pose proof (IH n i s H) as G1. destruct (run p n i s) as [i1 s1].
      pose proof (IH n i1 s1 ltac:(apply G1)) as G2. destruct (run p n i1 s1) as [i2 s2].
      apply (good_trans n i s i1 s1); [exact G1|]. apply (good_trans n i1 s1 i2 s2); [exact G2|].
      apply one_good. apply G2.
    - rewrite eqb_Z. destruct (Z.eqb_spec φ i φ n); [apply good_refl; exact H|].
      pose proof (IH n i s H) as G1. destruct (run p n i s) as [i1 s1].
      apply (good_trans n i s i1 s1); [exact G1|]. apply IH. apply G1.
    - rewrite eqb_Z. destruct (Z.eqb_spec φ i φ n); [apply good_refl; exact H|].
      apply one_ok. lia.
  Qed.

  (** The segment check: n visits from s end at s'.  [eqs] is any test that implies equal specification
      states. *)
  Context (eqs : St -> St -> bool) (eqs_ok : forall s t, eqs s t = true -> zs s = zs t).

  Definition seg (p : positive) (n : int) (s s' : St) : bool :=
    let '(i, t) := run p n 0 s in (i =? n)%uint63 && eqs t s'.

  Theorem seg_ok p n s s' : seg p n s s' = true -> zit opz (Z.to_nat φ n) (zs s) = zs s'.
  Proof.
    unfold seg. pose proof (run_good p n 0%uint63 s ltac:(apply to_Z_bounded)) as [B E].
    destruct (run p n 0 s) as [i t]. cbn [fst snd] in *. intros H. apply andb_prop in H as [H1 H2].
    rewrite eqb_Z in H1. apply Z.eqb_eq in H1. apply eqs_ok in H2. rewrite <- H2, E, H1.
    change (φ 0) with 0. rewrite Z.sub_0_r. reflexivity.
  Qed.
End Runner.

(** The plain runner: one visit at a time. *)
Section Single.
  Context {St ZS : Type} (zs : St -> ZS) (opz : ZS -> ZS).
  Context (ex1 : St -> St) (bnd : St -> bool).
  Context (ex1_ok : forall s, bnd s = true -> zs (ex1 s) = opz (zs s)).

  Definition one1 (n i : int) (s : St) : int * St := if bnd s then ((i + 1)%uint63, ex1 s) else (i, s).

  Lemma one1_ok : one_spec zs opz one1.
  Proof.
    intros n i s H. unfold one1. pose proof (to_Z_bounded i). pose proof (to_Z_bounded n).
    destruct (bnd s) eqn:B; cbn [fst snd].
    - assert (E : φ (i + 1) = φ i + 1).
      { rewrite add_spec. change (φ 1) with 1. apply Z.mod_small. lia. }
      rewrite E. split; [lia|]. replace (φ i + 1 - φ i) with 1 by lia. change (Z.to_nat 1) with 1%nat. cbn [zit]. apply ex1_ok, B.
    - split; [lia|]. rewrite Z.sub_diag. reflexivity.
  Qed.
End Single.

(** The same, 256 visits per call when that many remain (less bookkeeping per visit). *)
Section Batch.
  Context {St ZS : Type} (zs : St -> ZS) (opz : ZS -> ZS).
  Context (ex1 : St -> St) (bnd : St -> bool).
  Context (ex1_ok : forall s, bnd s = true -> zs (ex1 s) = opz (zs s)).

  Fixpoint exk (k : nat) (i : int) (s : St) : int * St :=
    match k with
    | O => (i, s)
    | S k => if bnd s then exk k (i + 1)%uint63 (ex1 s) else (i, s)
    end.

  Lemma exk_ok k : forall i s, φ i + Z.of_nat k < wB ->
    φ i <= φ (fst (exk k i s)) <= φ i + Z.of_nat k /\
    zs (snd (exk k i s)) = zit opz (Z.to_nat (φ (fst (exk k i s)) - φ i)) (zs s).
  Proof.
    induction k as [|k IH]; intros i s H; cbn [exk].
    - cbn [fst snd]. split; [lia|]. rewrite Z.sub_diag. reflexivity.
    - pose proof (to_Z_bounded i). destruct (bnd s) eqn:B.
      + assert (E : φ (i + 1) = φ i + 1).
        { rewrite add_spec. change (φ 1) with 1. apply Z.mod_small. lia. }
        destruct (IH (i + 1)%uint63 (ex1 s) ltac:(lia)) as [B1 E1]. split; [lia|].
        rewrite E1, E, (ex1_ok s B).
        replace (Z.to_nat (φ (fst (exk k (i + 1) (ex1 s))) - φ i))
          with (S (Z.to_nat (φ (fst (exk k (i + 1) (ex1 s))) - (φ i + 1)))) by lia.
        reflexivity.
      + cbn [fst snd]. split; [lia|]. rewrite Z.sub_diag. reflexivity.
  Qed.

  Definition oneB (n i : int) (s : St) : int * St :=
    if (n - i <? 256)%uint63 then one1 ex1 bnd n i s else exk 256 i s.

  Lemma oneB_ok : one_spec zs opz oneB.
  Proof.
    intros n i s H. unfold oneB. pose proof (to_Z_bounded i). pose proof (to_Z_bounded n).
    assert (E : φ (n - i) = φ n - φ i) by (rewrite sub_spec; apply Z.mod_small; lia).
    rewrite ltb_Z, E. change (φ 256) with 256. destruct (Z.ltb_spec (φ n - φ i) 256).
    - apply (one1_ok zs opz ex1 bnd ex1_ok). exact H.
    - destruct (exk_ok 256 i s ltac:(change (Z.of_nat 256) with 256; lia)) as [B1 E1].
      change (Z.of_nat 256) with 256 in B1. split; [lia|exact E1].
  Qed.
End Batch.
