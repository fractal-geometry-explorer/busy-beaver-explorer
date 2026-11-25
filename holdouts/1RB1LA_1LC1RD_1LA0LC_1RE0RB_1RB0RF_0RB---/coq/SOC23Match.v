From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 SOC23Model SOC23_Holdouts SOC23Corner.
Require Import ZifyNat Lia PeanoNat String.

(* The second-overflow cascade, and the one way it can make a corner.

   For  1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---  and  1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---.

   After the left counter overflows (LC_Ov), the right counter is read as a cascade of second
   overflows (busycoq's ROv2 position; rules R1 to R5 of SOC23Model.v). The cascade ends when it
   enters the plain counter phase cfgR, and from there the round is a fixed countdown to
   cfgL len 0 (k+n+1). Call a configuration *doomed* when that countdown ends at a corner:
     cfgL len k n with k+n = 2^len,  cfgR len k n with k+n+1 = 2^len.

   Lemma doom_step: the only step that makes a doomed configuration out of one that is not doomed
   is rule R5 (RS1_Ov_1, a shifted counter RS1 with an odd number h = 2a+1 of digits running out),
   and only when the unread rest m of the right counter satisfies
       m + 1 = (2*D + 1) * 2^(3a+3),    D = 2^len - 1 - k   (the left counter's deficit).
   The three blank ends (R1, R2, R3 with nothing left to read) never make one: the new left counter
   is (2k+1)*2^s - 1 or (2k+1)*2^s, and an odd number times 2^s is not a power of two, except in
   the one case cfgS0 len (2^len-1) 0 0 0, which no step reaches from cfgL 2 0 5 (Lemma bad0_step).

   Theorem halts_iff_r5_match: each machine halts from blank tape iff the model orbit from
   cfgL 2 0 5 meets an R5 configuration cfgS1 len k (2a+1) 0 m with that equation. *)

Module SOC23Match.
Import SOC23Model SOC23Holdouts SOC23Corner SOC23CornerHoldouts.
Local Close Scope sym.
Local Open Scope nat_scope.

Definition doomed x := match x with
| cfgL len k n => k + n = 2^len
| cfgR len k n => k + n + 1 = 2^len
| _ => False
end.

Definition r5match x := match x with
| cfgS1 len k h 0 m => Nat.odd h = true /\ m + 1 = (2*(2^len-1-k)+1) * 2^(Nat.div2 h*3+3)
| _ => False
end.

Definition bad0 x := match x with
| cfgS0 len k 0 0 0 => k = 2^len - 1
| _ => False
end.

(* an odd number times 2^s is a power of two only for s = the exponent and odd = 1 *)
Lemma odd_pow_ne len k s : k < 2^len -> (2*k+1) * 2^s <> 2^(len+1+s).
Proof.
  intros Hk E. rewrite !Nat.pow_add_r in E.
  assert (Hs : 2^s <> 0) by (apply Nat.pow_nonzero; lia).
  assert (E2 : 2*k+1 = 2^len*2^1) by (apply (Nat.mul_cancel_r _ _ (2^s)); auto; nia).
  cbn [Nat.pow] in E2. lia.
Qed.

Lemma odd_pow_ne1 len k a : k < 2^len -> (2*k+1) * 2^(S a) + 1 <> 2^(len+1+S a).
Proof.
  intros Hk E. rewrite Nat.pow_succ_r' in E.
  replace (len+1+S a) with (S (len+1+a)) in E by lia. rewrite Nat.pow_succ_r' in E. lia.
Qed.

Lemma pow_pos n : 1 <= 2^n.
Proof. pose proof (Nat.pow_nonzero 2 n). lia. Qed.

Ltac split_eq m x i Hm Es Hs :=
  destruct (split_lowbit m) as [x i] eqn:Es;
  pose proof (split_lowbit_spec m Hm) as Hs; rewrite Es in Hs.

(* the step lemma: a step that creates a doomed configuration is an R5 match *)
Lemma doom_step x y : P x -> ~ bad0 x -> f x = Some y -> doomed y -> doomed x \/ r5match x.
Proof.
  intros HP Hb Hf Hd.
  destruct x as [len k m|len k m|len k h n m|len k h n m]; cbn [P] in HP; cbn [f] in Hf.
  - destruct k as [|k].
    + destruct (Nat.eqb m (2^len)); [discriminate|].
      destruct (split_lowbit m); injection Hf as <-; contradiction.
    + injection Hf as <-. left. cbn [doomed] in *. lia.
  - injection Hf as <-. left. cbn [doomed] in *. lia.
  - destruct n as [|n].
    2: { injection Hf as <-. contradiction. }
    destruct (Nat.even h) eqn:Eh; destruct (Nat.eqb_spec m 0) as [Em|Em].
    + injection Hf as <-. cbn [doomed] in Hd. exfalso.
      destruct (Nat.div2 h) as [|a] eqn:Ea.
      * assert (h = 0).
        { pose proof (Nat.div2_odd h) as Hh. rewrite <- Nat.negb_even, Eh in Hh.
          cbn in Hh. lia. }
        subst h m. apply Hb. cbn [bad0]. cbn in Hd. replace (len+1+0) with (S len) in Hd by lia.
        rewrite Nat.pow_succ_r' in Hd. pose proof (pow_pos len). lia.
      * apply (odd_pow_ne1 len k (a*3+2)); [lia|].
        replace (S a * 3) with (S (a*3+2)) in Hd by lia.
        pose proof (pow_pos (S (a*3+2))). lia.
    + destruct (split_lowbit m); injection Hf as <-; contradiction.
    + injection Hf as <-. cbn [doomed] in Hd. exfalso.
      apply (odd_pow_ne len k (Nat.div2 h*3+2)); [lia|].
      pose proof (pow_pos (Nat.div2 h*3+2)). lia.
    + destruct (split_lowbit m); injection Hf as <-; contradiction.
  - destruct n as [|n].
    2: { injection Hf as <-. contradiction. }
    destruct (Nat.even h) eqn:Eh.
    + destruct (Nat.eqb_spec m 0) as [Em|Em].
      * injection Hf as <-. cbn [doomed] in Hd. exfalso.
        apply (odd_pow_ne len k (Nat.div2 h*3+2)); [lia|].
        pose proof (pow_pos (Nat.div2 h*3+2)). lia.
      * destruct (Nat.even m); [destruct (split_lowbit (Nat.div2 m))|destruct (split_lowbit (m+1))];
          injection Hf as <-; contradiction.
    + injection Hf as <-. cbn [doomed] in Hd. right. cbn [r5match].
      split; [rewrite <- Nat.negb_even, Eh; reflexivity|].
      set (s := Nat.div2 h*3+3) in *.
      rewrite !Nat.pow_add_r in Hd. cbn [Nat.pow] in Hd.
      replace (2*(2^len-1-k)+1) with (2^len*2 - (2*k+1)) by lia. nia.
Qed.

Lemma bad0_inv x : bad0 x -> exists len, x = cfgS0 len (2^len-1) 0 0 0.
Proof.
  destruct x as [? ? ?|? ? ?|len k [|h] [|n] [|m]|? ? ? ? ?]; cbn [bad0]; try tauto.
  intros ->. eauto.
Qed.

(* no step from a configuration satisfying P reaches the exceptional cfgS0 len (2^len-1) 0 0 0 *)
Lemma bad0_step x y : P x -> f x = Some y -> ~ bad0 y.
Proof.
  intros HP Hf Hb. apply bad0_inv in Hb as [l ->].
  destruct x as [len k m|len k m|len k h n m|len k h n m]; cbn [P] in HP; cbn [f] in Hf.
  - destruct k as [|k]; [|discriminate].
    destruct (Nat.eqb_spec m (2^len)) as [E|E]; [discriminate|].
    assert (Hm : m <> 0) by lia. split_eq m x i Hm Es Hs.
    injection Hf; intros; subst; cbn in *; lia.
  - discriminate.
  - destruct n as [|n].
    + destruct (Nat.even h); destruct (Nat.eqb m 0); try discriminate;
        destruct (split_lowbit m); try discriminate.
      injection Hf; intros. lia.
    + injection Hf; intros; subst. lia.
  - destruct n as [|n]; [|discriminate].
    destruct (Nat.even h); [|discriminate].
    destruct (Nat.eqb_spec m 0) as [Em|Em]; [discriminate|].
    destruct (Nat.even m).
    + destruct (split_lowbit (Nat.div2 m)); discriminate.
    + assert (Hm1 : m+1 <> 0) by lia. split_eq (m+1) x j Hm1 Es Hs.
      injection Hf; intros; subst; cbn in *; lia.
Qed.

Lemma iter_n_add a b x :
  iter_n (a+b) x = match iter_n a x with Some y => iter_n b y | None => None end.
Proof.
  revert x. induction a as [|a IH]; intros x; [reflexivity|].
  cbn [iter_n Nat.add]. destruct (f x); [apply IH|reflexivity].
Qed.

(* backwards along the orbit: a doomed configuration is reached only through an R5 match *)
Lemma doom_back j : forall x z, P x -> ~ bad0 x -> iter_n j x = Some z -> doomed z ->
  doomed x \/ exists i w, iter_n i x = Some w /\ r5match w.
Proof.
  induction j as [|j IH]; intros x z HP Hb H Hd; cbn [iter_n] in H.
  - injection H as ->. left. exact Hd.
  - pose proof (f_spec (model false) x HP) as Hs. destruct (f x) as [y|] eqn:E; [|discriminate].
    destruct Hs as [_ Hy].
    destruct (IH y z Hy (bad0_step x y HP E) H Hd) as [Hdy|[i [w [Hw Hr]]]].
    + destruct (doom_step x y HP Hb E Hdy) as [Hdx|Hr]; [left; exact Hdx|].
      right. exists 0, x. split; [reflexivity|exact Hr].
    + right. exists (S i), w. cbn [iter_n]. rewrite E. split; assumption.
Qed.

(* forwards: a doomed cfgR runs straight into its corner *)
Lemma doomed_R k : forall len n, k + n + 1 = 2^len ->
  iter_n (k*2+1) (cfgR len k n) = Some (cfgL len 0 (2^len)).
Proof.
  induction k as [|k IH]; intros len n H.
  - change (0*2+1) with 1. cbn [iter_n f]. do 3 f_equal. lia.
  - replace (S k * 2 + 1) with (S (S (k*2+1))) by lia. cbn [iter_n f].
    apply IH. lia.
Qed.

Lemma r5_corner x : P x -> r5match x -> exists j len, iter_n j x = Some (cfgL len 0 (2^len)).
Proof.
  destruct x as [? ? ?|? ? ?|? ? ? ? ?|len k h [|n] m]; cbn [r5match P]; try contradiction.
  intros HP [Ho Hm].
  assert (Eh : Nat.even h = false) by (rewrite <- Nat.negb_odd, Ho; reflexivity).
  exists (S (((k*2+1)*2^(Nat.div2 h*3+3))*2+1)), (len+1+(Nat.div2 h*3+3)).
  cbn [iter_n f]. rewrite Eh.
  apply doomed_R. set (s := Nat.div2 h*3+3) in *.
  rewrite !Nat.pow_add_r. cbn [Nat.pow].
  replace (2*(2^len-1-k)+1) with (2^len*2 - (2*k+1)) in Hm by (pose proof (pow_pos len); lia).
  pose proof (pow_pos s). nia.
Qed.

(* the cascade criterion *)
Theorem halts_iff_r5_match bb :
  halts (machine bb) c0 <->
  exists j x, iter_n j (cfgL 2 0 5) = Some x /\ r5match x.
Proof.
  rewrite halts_iff_corner. split.
  - intros [j [len H]].
    destruct (doom_back j (cfgL 2 0 5) _ ltac:(cbn [P]; cbn; lia) ltac:(cbn; tauto) H
      ltac:(cbn [doomed]; lia)) as [Hd|[i [w [Hw Hr]]]].
    + cbn in Hd. lia.
    + exists i, w. split; assumption.
  - intros [j [x [Hx Hr]]].
    destruct (iter_reach (model false) j (cfgL 2 0 5) x ltac:(cbn [P]; cbn; lia) Hx) as [_ HP].
    destruct (r5_corner x HP Hr) as [i [len Hi]].
    exists (j+i), len. rewrite iter_n_add, Hx. exact Hi.
Qed.

End SOC23Match.

Print Assumptions SOC23Match.halts_iff_r5_match.
