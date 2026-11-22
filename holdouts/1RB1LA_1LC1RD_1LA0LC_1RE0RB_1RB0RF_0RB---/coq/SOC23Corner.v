From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 SOC23Model.
Require Import ZifyNat Lia PeanoNat String.

(* Every corner halts, for every length.
   A corner is the model configuration cfgL len 0 (2^len) of SOC23Model.v. From it the machine
     1. overflows the left counter (LC_Ov) into a right counter RS0 len (2^(len+1)-2) 0 that is
        twice too large, and counts the left counter all the way down: 2^len-1 pairs;
     2. overflows the left counter a second time while RS0 still holds 2^len-1 - 1; the extra 1 cell
        that this overflow leaves joins the pad cell of RS0 and the left counter gains one digit
        (rule E1), so the tape is LC (len+1) full |> a right counter of len-1 digits 100/000 ended
        by 0011;
     3. counts that right counter up twice through its len-1 digits (2*(2^(len-1)-1) pairs and one
        carry into the end marker, which turns 0011 into 1011);
     4. halts from LC (len+1) (2^len) |> 100^(len-1) 1011 (rule Hend).
   E1 and Hend are two tape rules with free parameters, proved by symbolic execution for both
   machines in SOC23_Corner_Holdouts below. *)

Module SOC23Corner.
Import SOC23Model.
Open Scope sym.
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Section Corner.
Variable b : Machine.
Notation "c -->* c'" := (c -[machine b]->* c') (at level 40).
Notation "c -->+ c'" := (c -[machine b]->+ c') (at level 40).
Notation "l <| r" := (l <{{qL b}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{qR b}}> r) (at level 30).

Hypothesis E1 : forall l r, l |> [1;1] *> r -->+ (l <* [0;1]) |> r.
Hypothesis Hend : forall n m,
  halts (machine b) ((ldh <* ld0 <* ld1^^n) |> rd1^^m *> [1;0;1;1] *> 0inf).

(* countdown of the left counter against a shifted right counter RS0 *)
Lemma count_S0 len h m j : forall k n, j+k < 2^len -> j+n < 2^(h+1) ->
  LC len (j+k) |> RS0 h (j+n) m -->* LC len k |> RS0 h n m.
Proof.
  induction j as [|j IH]; intros k n Hk Hn; [apply evstep_refl|].
  eapply evstep_trans; [|apply IH; lia].
  apply progress_evstep.
  eapply progress_trans.
  - replace (S j + n) with (1+(j+n)) by lia. apply RS0_Inc. lia.
  - replace (S j + k) with (1+(j+k)) by lia. apply LC_Inc. lia.
Qed.

(* the right counter of phase 3: len digits 100 (one) / 000 (zero), any end marker *)
Definition RD len v r := BinDec rd0 rd1 len v r.

Lemma RD_Inc len n l r: 1+n<2^len -> l |> RD len (1+n) r -->+ l <| RD len n r.
Proof.
  intros H. unfold RD. apply RBinDec_spec; [|lia].
  intros l' r' n'. epose proof (raw_RInc b l' ([0;0] *> r') n') as HX.
  cbn [Str_app] in *. exact HX.
Qed.

Lemma count_RD len len' r j : forall k n, j+k < 2^len -> j+n < 2^len' ->
  LC len (j+k) |> RD len' (j+n) r -->* LC len k |> RD len' n r.
Proof.
  induction j as [|j IH]; intros k n Hk Hn; [apply evstep_refl|].
  eapply evstep_trans; [|apply IH; lia].
  apply progress_evstep.
  eapply progress_trans.
  - replace (S j + n) with (1+(j+n)) by lia. apply RD_Inc. lia.
  - replace (S j + k) with (1+(j+k)) by lia. apply LC_Inc. lia.
Qed.

Theorem corner_halts len : 1 <= len -> halts (machine b) (to_config b (cfgL len 0 (2^len))).
Proof.
  intros Hlen. destruct len as [|l]; [lia|]. clear Hlen.
  cbn [to_config].
  (* 1. first overflow and full countdown *)
  eapply halts_evstep; [|apply progress_evstep; replace (2^S l) with ((0*2+1)*2^(S l)) by lia; apply LC_Ov].
  pose proof (count_S0 (S l) (S l) 0 (2^S l - 1) 0 (2^S l - 1)) as HC.
  rewrite Nat.add_0_r in HC.
  replace (2^S l - 1 + (2^S l - 1)) with ((2^S l - 1)*2) in HC by lia.
  eapply halts_evstep; [|apply HC; arith]. clear HC.
  pose proof (RS0_Inc b (S l) (2^S l - 2) 0 (LC (S l) 0)) as HC.
  replace (1 + (2^S l - 2)) with (2^S l - 1) in HC by arith.
  eapply halts_evstep; [|apply progress_evstep, HC; arith]. clear HC.
  (* 2. second overflow, E1 *)
  eapply halts_evstep; [|apply progress_evstep; unfold LC; rewrite BinDec_O; apply (raw_LOv b)].
  unfold RS0. replace (2^S l - 2) with ((2^l - 1)*2) by arith.
  rewrite BinDec2_mul2 by arith.
  eapply halts_evstep; [|apply progress_evstep; apply (E1 _ (BinDec _ _ _ _ _))].
  assert (Er : BinDec ([0;0]++[0]) ([0;0]++[1]) (S l) (2^l - 1) (rd1 *> RC 0) =
    RD l (2^l-1) ([0;0;1;1] *> 0inf)).
  { replace (S l) with (1+l) by lia. replace (2^l-1) with ((0+1)*2^l-1) at 1 by lia.
    rewrite BinDec_mulpow2sub1' by arith. rewrite BinDec_O. unfold RC; rewrite BinInc_O.
    unfold RD. replace ((0+1)*2^l-1) with (2^l-1) by lia. rewrite BinDec_full.
    cbn. do 2 rewrite <-(const_unfold _ 0). reflexivity. }
  match goal with |- context [BinDec ?a ?bb (S l) ?d ?e] =>
    replace (BinDec a bb (S l) d e) with (RD l (2^l-1) ([0;0;1;1] *> 0inf)) by (symmetry; exact Er) end.
  clear Er.
  (* 3. two runs of the right counter RD l, with the carry into the end marker between them *)
  assert (HL : ld0 *> ld0^^S l *> ldh = LC (S (S l)) (2^S (S l) - 1)).
  { unfold LC. rewrite BinDec_full. reflexivity. }
  rewrite HL. clear HL.
  pose proof (count_RD (S (S l)) l ([0;0;1;1] *> 0inf) (2^l-1) (2^S (S l) - 2^l) 0) as HC.
  rewrite Nat.add_0_r in HC.
  replace (2^l - 1 + (2^S (S l) - 2^l)) with (2^S (S l) - 1) in HC by arith.
  eapply halts_evstep; [|apply HC; arith]. clear HC.
  unfold RD; rewrite BinDec_O.
  eapply halts_evstep; [|apply progress_evstep;
    exact (raw_RInc b (LC (S (S l)) (2^S (S l) - 2^l)) ([0;1;1] *> 0inf) l)].
  rewrite <-(BinDec_full rd0 rd1 l). fold (RD l (2^l-1) ([1;0;1;1] *> 0inf)).
  pose proof (LC_Inc b (S (S l)) (2^S (S l) - 2^l - 1)) as HC.
  replace (1 + (2^S (S l) - 2^l - 1)) with (2^S (S l) - 2^l) in HC by arith.
  eapply halts_evstep; [|apply progress_evstep, HC; arith]. clear HC.
  pose proof (count_RD (S (S l)) l ([1;0;1;1] *> 0inf) (2^l-1) (2^S l) 0) as HC.
  rewrite Nat.add_0_r in HC.
  replace (2^l - 1 + 2^S l) with (2^S (S l) - 2^l - 1) in HC by arith.
  eapply halts_evstep; [|apply HC; arith]. clear HC.
  (* 4. the end *)
  unfold RD, LC; rewrite BinDec_O.
  replace (S (S l)) with (1+S l) by lia. replace (2^S l) with (1*2^S l) by lia.
  rewrite BinDec_mulpow2 by arith.
  change (BinDec ld0 ld1 1 1 ldh) with (BinDec ld0 ld1 1 (2^1-1) ldh). rewrite BinDec_full.
  exact (Hend (S l) l).
Qed.
End Corner.
End SOC23Corner.

(* Both machines: the two extra rules, and halting is now equivalent to the model orbit
   from cfgL 2 0 5 reaching a corner. *)
From BusyCoq Require Import SOC23_Holdouts.
Module SOC23CornerHoldouts.
Import SOC23Model SOC23Holdouts SOC23Corner.
Open Scope sym.

Lemma E1_model bb l r :
  l <* [0;1] {{qR (model bb)}}> [1;1] *> r -[machine bb]->+ l <* [0;1] <* [0;1] {{qR (model bb)}}> r.
Proof. destruct bb; cbn; es. Qed.

Lemma Hend_model bb n m :
  halts (machine bb) ((ldh <* ld0 <* ld1^^n) <* [0;1] {{qR (model bb)}}> rd1^^m *> [1;0;1;1] *> 0inf).
Proof. destruct bb; cbn; esx. Qed.

Lemma iter_reach (b : SOC23Model.Machine) j : forall x y, P x -> iter_n j x = Some y ->
  to_config b x -[SOC23Model.machine b]->* to_config b y /\ P y.
Proof.
  induction j as [|j IH]; intros x y HP H; cbn [iter_n] in H.
  - injection H as <-. split; [apply evstep_refl|exact HP].
  - pose proof (f_spec b x HP) as Hs. destruct (f x) as [z|] eqn:E; [|discriminate].
    destruct Hs as [Hxz Hz]. destruct (IH z y Hz H) as [Hzy Hy].
    split; [|exact Hy]. eapply evstep_trans; [apply progress_evstep, Hxz|exact Hzy].
Qed.

Theorem halts_iff_corner bb :
  halts (machine bb) c0 <->
  exists j len, iter_n j (cfgL 2 0 5) = Some (cfgL len 0 (2^len)).
Proof.
  split; [apply halts_needs_corner|].
  intros [j [len H]].
  destruct (iter_reach (model bb) j (cfgL 2 0 5) _ ltac:(cbn [P]; cbn; lia) H) as [Hr HP].
  cbn [P] in HP.
  eapply halts_evstep; [|apply (init bb)].
  eapply halts_evstep; [|exact Hr].
  apply (corner_halts (model bb) (E1_model bb) (Hend_model bb) len). lia.
Qed.
End SOC23CornerHoldouts.

Print Assumptions SOC23CornerHoldouts.halts_iff_corner.
