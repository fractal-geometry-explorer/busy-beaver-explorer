From BusyCoq Require Import Helper TM Individual62 BinaryCounter_v2 SimplTape ES_v2 Eqv_WordPairs SOC25_Iter.
Require Import Lia PeanoNat.
Close Scope sym. Open Scope nat_scope.

(* The marker lemma for the round map F of SOC25_Iter.v (PR 40).

   Write the round value X (odd) as X = 2*m + 1. F reads the zero gaps of m from the
   low end; it stops at the first even gap, and if every gap is odd it runs out and
   returns an even X'. A gap is even exactly when the 1 bit that closes it sits at an
   even position of m. So:

   - if m has a 1 bit at an even position ("marked m"), F(L, X) is defined and odd;
   - F(L, X) = None needs X even;
   - hence a halting orbit that starts at an odd X must pass a round whose X is odd
     and unmarked: every 1 bit of X sits at an even position, i.e. X written in base 4
     uses only the digits 0 and 1 (halt_needs_unmarked).

   This is the analogue, for this map, of the wall marker of PR 58 (a 1 digit at a
   position of a fixed parity). What is not proved is that the marker survives every
   round. *)

Module SOC25Marker.
Import IterHalts SOC25Model SOC25Iter.

Definition marked (m : nat) := exists j, Nat.testbit m (2*j) = true.

Lemma not_marked_0 : ~ marked 0.
Proof. intros [j H]. rewrite Nat.bits_0 in H. discriminate. Qed.

Fixpoint mk_upto (m n : nat) : bool :=
  match n with
  | O => Nat.testbit m 0
  | S n' => Nat.testbit m (2*n) || mk_upto m n'
  end.

Lemma mk_upto_spec m n : mk_upto m n = true <-> exists j, j <= n /\ Nat.testbit m (2*j) = true.
Proof.
  induction n as [|n IH]; cbn [mk_upto].
  - split; [intros H; exists 0; split; [lia|exact H]|].
    intros [j [Hj H]]. replace j with 0 in H by lia. exact H.
  - rewrite Bool.orb_true_iff, IH. split.
    + intros [H|[j [Hj H]]]; [exists (S n); split; [lia|exact H]|exists j; split; [lia|exact H]].
    + intros [j [Hj H]]. destruct (Nat.eq_dec j (S n)) as [->|Hne]; [left; exact H|].
      right. exists j. split; [lia|exact H].
Qed.

Lemma classic_marked m : marked m \/ ~ marked m.
Proof.
  destruct (mk_upto m m) eqn:E.
  - left. apply mk_upto_spec in E as [j [_ H]]. exists j. exact H.
  - right. intros [j H]. destruct (Nat.le_gt_cases j m) as [Hle|Hgt].
    + assert (mk_upto m m = true) by (apply mk_upto_spec; exists j; split; assumption).
      congruence.
    + destruct (Nat.eq_dec m 0) as [->|Hm]; [rewrite Nat.bits_0 in H; discriminate|].
      pose proof (Nat.log2_lt_lin m ltac:(lia)).
      rewrite Nat.bits_above_log2 in H by lia. discriminate.
Qed.

Lemma testbit_block x i p :
  Nat.testbit ((x*2+1)*2^i) p =
  if p <? i then false else if p =? i then true else Nat.testbit x (p-i-1).
Proof.
  rewrite <- Nat.shiftl_mul_pow2.
  destruct (Nat.ltb_spec p i) as [Hlt|Hge].
  - apply Nat.shiftl_spec_low. exact Hlt.
  - rewrite (Nat.shiftl_spec_high' _ _ _ Hge).
    destruct (Nat.eqb_spec p i) as [->|Hne].
    + rewrite Nat.sub_diag. replace (x*2+1) with (2*x+1) by lia.
      apply Nat.testbit_odd_0.
    + assert (Hpi : p - i = S (p - i - 1)) by lia. rewrite Hpi at 1.
      replace (x*2+1) with (2*x+1) by lia.
      apply Nat.testbit_odd_succ; lia.
Qed.

Lemma marked_block_even x i : Nat.even i = true -> marked ((x*2+1)*2^i).
Proof.
  intros Hi. apply Nat.even_spec in Hi as [j Hj]. exists j.
  rewrite testbit_block. subst i.
  replace (2*j <? 2*j) with false by (symmetry; apply Nat.ltb_irrefl).
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma marked_block_odd x i : Nat.even i = false -> marked ((x*2+1)*2^i) -> marked x.
Proof.
  intros Hi [j Hj]. rewrite testbit_block in Hj.
  assert (Hodd : exists c, i = 2*c+1).
  { destruct (Nat.Even_or_Odd i) as [He|Ho].
    - apply Nat.even_spec in He. congruence.
    - exact Ho. }
  destruct Hodd as [c ->].
  destruct (Nat.ltb_spec (2*j) (2*c+1)); [discriminate|].
  destruct (Nat.eqb_spec (2*j) (2*c+1)); [lia|].
  exists (j - c - 1). replace (2*(j-c-1)) with (2*j-(2*c+1)-1) by lia. exact Hj.
Qed.

Lemma odd_2k1 k : Nat.odd (2*k+1) = true.
Proof. apply Nat.odd_spec. exists k. reflexivity. Qed.

(* The closed-form loop G_loop returns an odd value as soon as the block is marked. *)
Lemma G_loop_odd fuel : forall Lp u g m, m < fuel -> marked ((m*2+1)*2^g) ->
  Nat.odd (snd (G_loop fuel Lp u g m)) = true.
Proof.
  induction fuel as [|fuel IH]; intros Lp u g m Hm Hk; [lia|].
  cbn [G_loop]. destruct (Nat.even g) eqn:Eg.
  - cbn [snd]. rewrite Nat.pow_add_r. cbn [Nat.pow].
    replace (u * (2 ^ (Nat.div2 g * 5) * (2*1)) + (m*2+1))
      with (2 * (u * 2 ^ (Nat.div2 g * 5) + m) + 1) by lia.
    apply odd_2k1.
  - pose proof (marked_block_odd m g Eg Hk) as Hm'.
    destruct (Nat.eqb_spec m 0) as [->|Hne]; [exfalso; exact (not_marked_0 Hm')|].
    destruct (split_lowbit m) as [m' g'] eqn:Es.
    pose proof (split_lowbit_spec m Hne) as Hs. rewrite Es in Hs.
    apply IH.
    + pose proof (split_lowbit_lt m m' g' Hne Es). lia.
    + rewrite <- Hs. exact Hm'.
Qed.

Lemma div2_pred_odd X : Nat.odd X = true -> Nat.div2 (X-1) = Nat.div2 X.
Proof.
  intros Ho. apply Nat.odd_spec in Ho as [k ->].
  replace (2*k+1-1) with (2*k) by lia. rewrite Nat.div2_double.
  replace (2*k+1) with (S (2*k)) by lia. rewrite Nat.div2_succ_double. reflexivity.
Qed.

(* A marked odd round value: F is defined and returns an odd value. *)
Lemma F_marker L X : Nat.odd X = true -> marked (Nat.div2 X) -> P (cfgL L 0 X) ->
  exists L' X', F (L, X) = Some (L', X') /\ Nat.odd X' = true.
Proof.
  intros Ho Hk HP.
  assert (HL : X <> 2^L).
  { intros ->. destruct L as [|L].
    - cbn in Hk. exact (not_marked_0 Hk).
    - rewrite Nat.pow_succ_r' in Ho.
      rewrite <- Nat.negb_even, Nat.even_mul in Ho. discriminate. }
  rewrite (F_G L X Ho HL HP).
  exists (fst (G (L, X))), (snd (G (L, X))). split; [destruct (G (L, X)); reflexivity|].
  unfold G. rewrite (div2_pred_odd X Ho).
  assert (Hne : Nat.div2 X <> 0) by (intros E; rewrite E in Hk; exact (not_marked_0 Hk)).
  destruct (split_lowbit (Nat.div2 X)) as [m g] eqn:Es.
  pose proof (split_lowbit_spec _ Hne) as Hs. rewrite Es in Hs.
  apply G_loop_odd; [lia|]. rewrite <- Hs. exact Hk.
Qed.

(* F halts only on an even round value. *)
Lemma F_None_even L X : F (L, X) = None -> Nat.even X = true.
Proof.
  intros HF. destruct (Nat.even X) eqn:Ev; [reflexivity|].
  assert (Ho : Nat.odd X = true) by (rewrite <- Nat.negb_even, Ev; reflexivity).
  exfalso. revert HF. cbn [F].
  destruct (Nat.eqb X (2^L)).
  - destruct (Nat.even (L-1)); discriminate.
  - rewrite (split_lowbit_odd X Ho). cbn [Nat.even negb].
    destruct (Nat.eqb (Nat.div2 (X-1)) 0); [discriminate|].
    destruct (split_lowbit (Nat.div2 (X-1))). discriminate.
Qed.

(* A halting orbit from an odd round value passes an odd round value with no marker. *)
Theorem halt_needs_unmarked p0 :
  P (cfgL (fst p0) 0 (snd p0)) -> Nat.odd (snd p0) = true -> iter_halts F p0 ->
  exists n L X, iter_n F n p0 = Some (L, X) /\ Nat.odd X = true /\ ~ marked (Nat.div2 X).
Proof.
  intros HP Ho H. revert HP Ho. induction H as [[L X] HN|[L X] p1 HS _ IH]; intros HP Ho;
    cbn [fst snd] in HP, Ho.
  - apply F_None_even in HN. rewrite <- Nat.negb_odd, Ho in HN. discriminate.
  - destruct (classic_marked (Nat.div2 X)) as [Hk|Hk].
    + destruct (F_marker L X Ho Hk HP) as [L' [X' [E Ho']]].
      rewrite E in HS. injection HS as <-.
      pose proof (F_spec L X HP) as Hsp. rewrite E in Hsp. destruct Hsp as [_ HP'].
      destruct (IH HP' Ho') as [n [L2 [X2 [Hn R]]]].
      exists (S n), L2, X2. split; [|exact R]. cbn [iter_n]. rewrite E. exact Hn.
    + exists 0, L, X. split; [reflexivity|]. split; assumption.
Qed.
End SOC25Marker.


(* The two holdouts of the family that the SOC25 model covers. *)
Module Holdouts.
Import IterHalts SOC25Iter SOC25Marker.

(* 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- is TM93.tm' = TM93.machine true. *)
Theorem M1c_needs_unmarked :
  halts TM93.tm' c0 ->
  exists n L X, iter_n F n (8, 145) = Some (L, X) /\ Nat.odd X = true /\ ~ marked (Nat.div2 X).
Proof.
  intros H. change (halts (TM93.machine true) c0) in H.
  rewrite TM93_iter.eqv_F in H.
  assert (E : F (2, 4) = Some (8, 145)) by reflexivity.
  rewrite (iter_halts_step F _ _ E) in H.
  apply halt_needs_unmarked; [cbn [fst snd SOC25Model.P]; cbn; lia|reflexivity|exact H].
Qed.

(* 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF1RC_1RA--- is TM97.tm' = TM97.machine true. *)
Theorem M1d_needs_unmarked :
  halts TM97.tm' c0 ->
  exists n L X, iter_n F n (1, 3) = Some (L, X) /\ Nat.odd X = true /\ ~ marked (Nat.div2 X).
Proof.
  intros H. change (halts (TM97.machine true) c0) in H.
  rewrite TM97_iter.eqv_F in H.
  apply halt_needs_unmarked; [cbn [fst snd SOC25Model.P]; cbn; lia|reflexivity|exact H].
Qed.
End Holdouts.

Print Assumptions SOC25Marker.F_marker.
Print Assumptions SOC25Marker.halt_needs_unmarked.
Print Assumptions Holdouts.M1c_needs_unmarked.
Print Assumptions Holdouts.M1d_needs_unmarked.
