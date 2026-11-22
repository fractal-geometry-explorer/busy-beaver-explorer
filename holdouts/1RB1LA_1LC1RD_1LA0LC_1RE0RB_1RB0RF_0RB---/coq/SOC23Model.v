From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* A closed counter model for the two holdouts
     1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---   and
     1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---
   in the style of SOC25Model (Eqv_WordPairs.v), with right digits of three cells
   (rd1 = 100, rd0 = 000) instead of five.

   The left counter LC len k (digits 11 / 10) counts down, the right counter RC n
   (digits 100 / 000) counts up. When the left counter overflows, the right counter
   is re-read one cell shifted (RS0, RS1: digits 001 / 000 behind a pad of 0 or 1
   cells) and counted down; its overflow appends digits to the left counter.
   Eight tape rules, all proved by symbolic execution, drive every step.

   closed: every configuration satisfying P either steps (in at least one machine
   step) to another one, or is a corner cfgL len 0 (2^len). So the machines can halt
   only after reaching a corner. *)

Module SOC23Model.
Open Scope sym.
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Record Machine := {
  machine : TM;
  qL : Q;
  qR : Q;
  raw_LInc : forall l r n,
    l <* ld0 <* ld1^^n <{{qL}} [1;1] *> r -[machine]->+ l <* ld1 <* ld0^^n <* [0;1] {{qR}}> r;
  raw_RInc : forall l r n,
    l <* [0;1] {{qR}}> rd1^^n *> [0] *> r -[machine]->+ l <{{qL}} [1;1] *> rd0^^n *> [1] *> r;
  raw_LOv : forall r n,
    ldh <* ld1^^n <{{qL}} [1;1] *> r -[machine]->+ ldh <* ld0^^n <* [0;1] {{qR}}> [1] *> r;
  raw_R1 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2) *> [1;1;0;0] *> r -[machine]->+
    l <* ld1 <* ld0^^(n*3) <* [0;1] {{qR}}> [1;0] *> r;
  raw_R2 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2+1) *> [1;1;0;0] *> r -[machine]->+
    l <* ld1 <* ld0^^(n*3+2) <* [0;1] {{qR}}> [0] *> r;
  raw_R3 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2) *> [1;0;1;0;0;0;0;0] *> r -[machine]->+
    l <* ld1 <* ld0^^(n*3+2) <* [0;1] {{qR}}> [0;0] *> r;
  raw_R4 : forall l r n t,
    l <* [0;1] {{qR}}> rd1^^(n*2) *> [1;0;1;0;0;1;0;0] *> rd1^^t *> [0] *> r -[machine]->+
    l <* ld1 <* ld0^^(n*3+1) <* [0;1] {{qR}}> [1;0;0;0] *> rd0^^t *> [1] *> r;
  raw_R5 : forall l r n,
    l <* [0;1] {{qR}}> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -[machine]->+
    l <* ld0 <* ld1^^(n*3+3) <* [0;1] {{qR}}> r
}.

Section Rules.
Variable b:Machine.
Notation "c -->* c'" := (c -[machine b]->* c') (at level 40).
Notation "c -->+ c'" := (c -[machine b]->+ c') (at level 40).
Notation "l <| r" := (l <{{qL b}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{qR b}}> r) (at level 30).

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RS0 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> RC m).
Definition RS1 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> RC m).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RS0,RS1,RC;
  rw_Bin; try solve[solve_pow2_lt]; follow_rule H.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule (raw_LInc b). Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule (raw_RInc b). Qed.
Lemma RS0_Inc len n m l: 1+n<2^(len+1) -> l |> RS0 len (1+n) m -->+ l <| RS0 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule (raw_RInc b). Qed.
Lemma RS1_Inc len n m l: 1+n<2^(len+1) -> l |> RS1 len (1+n) m -->+ l <| RS1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule (raw_RInc b). Qed.
Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RS0 i ((2^i-1)*2) m.
Proof. solve_rule (raw_LOv b). Qed.
Lemma RS0_Ov_0 len k a i m: k<2^len ->
  LC len k |> RS0 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RS1 i ((2^i-1)*2) m.
Proof. solve_rule (raw_R1 b). Qed.
Lemma RS0_Ov_0_blank len k a: k<2^len ->
  LC len k |> RS0 (a*2) 0 0 -->+ LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC 1.
Proof. epose proof ((raw_R1 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RS0_Ov_1 len k a i m: k<2^len ->
  LC len k |> RS0 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RS0 i ((2^i-1)*2+1) m.
Proof. solve_rule (raw_R2 b). Qed.
Lemma RS0_Ov_1_blank len k a: k<2^len ->
  LC len k |> RS0 (a*2+1) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof ((raw_R2 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RS1_Ov_0_even len k a i m: k<2^len ->
  LC len k |> RS1 (a*2) 0 ((m*2+1)*2^i*2) -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RS1 i ((2^i-1)*2+1) m.
Proof. solve_rule (raw_R3 b). Qed.
Lemma RS1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RS1 (a*2) 0 0 -->+ LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> RC 0.
Proof. epose proof ((raw_R3 b) _ 0inf a) as H; solve_rule H. Qed.
Lemma RS1_Ov_0_odd len k a i m: k<2^len ->
  LC len k |> RS1 (a*2) 0 ((m*2+1)*2^(i+1)-1) -->+
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) |> RS0 (i+1) ((2^(i+1)-1)*2) m.
Proof.
  intros; unfold LC,RS0,RS1,RC; rw_Bin; try solve[solve_pow2_lt].
  replace (i+1) with (S i) by lia. cbn [lpow]. rewrite Str_app_assoc.
  unfold BinaryCounter.d0; cbn [length List.repeat].
  follow_rule (raw_R4 b).
Qed.
Lemma RS1_Ov_1 len k a m: k<2^len ->
  LC len k |> RS1 (a*2+1) 0 m -->+
  LC (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) |> RC m.
Proof. solve_rule (raw_R5 b). Qed.
End Rules.

Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgS0 (len k h n m:nat) | cfgS1 (len k h n m:nat).
Definition to_config b x := match x with
| cfgL len k n => LC len k <{{qL b}} [1;1] *> RC n
| cfgR len k n => LC len k <* [0;1] {{qR b}}> RC n
| cfgS0 len k h n m => LC len k <* [0;1] {{qR b}}> RS0 h n m
| cfgS1 len k h n m => LC len k <* [0;1] {{qR b}}> RS1 h n m
end.
Close Scope sym.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 2<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 2<=k+n+1<2^len*2
| cfgS0 len k h n m | cfgS1 len k h n m => 1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
end.
(* The only configurations without a proved successor. *)
Definition corner x := match x with
| cfgL len 0 n => n = 2^len
| _ => False
end.

(* Odd part and 2-adic valuation, m = (x*2+1)*2^i (as in SOC25_Iter.v of busycoq PR 40). *)
Fixpoint split_go (fuel n i : nat) : nat * nat :=
  match fuel with
  | O => (0, 0)
  | S fuel' => if Nat.even n then split_go fuel' (Nat.div2 n) (S i) else (Nat.div2 n, i)
  end.
Definition split_lowbit (m : nat) : nat * nat := split_go m m 0.

Lemma split_go_spec fuel : forall n i, n <> 0 -> n <= fuel ->
  let (x, j) := split_go fuel n i in n * 2^i = (x*2+1)*2^j.
Proof.
  induction fuel as [|fuel IH]; intros n i Hn Hf; [lia|].
  simpl. destruct (Nat.even n) eqn:E.
  - apply Nat.even_spec in E. destruct E as [k Hk]. subst n.
    rewrite Nat.div2_double. specialize (IH k (S i)).
    destruct (split_go fuel k (S i)) as [x j].
    rewrite Nat.pow_succ_r' in IH. rewrite <- IH by lia. lia.
  - destruct (Nat.Even_or_Odd n) as [Hev|[k Hk]]; [apply Nat.even_spec in Hev; congruence|].
    subst n. replace (2*k+1) with (S (2*k)) by lia. rewrite Nat.div2_succ_double. lia.
Qed.

Lemma split_lowbit_spec m : m <> 0 -> let (x, i) := split_lowbit m in m = (x*2+1)*2^i.
Proof.
  intros Hm. unfold split_lowbit.
  pose proof (split_go_spec m m 0 Hm (le_n m)) as H.
  destruct (split_go m m 0) as [x i]. simpl in H. lia.
Qed.

(* One step of the model; None exactly at a corner. *)
Definition f (c : Config) : option Config :=
  match c with
  | cfgL len O m =>
    if Nat.eqb m (2^len) then None
    else let (x, i) := split_lowbit m in Some (cfgS0 len (2^len-1) i ((2^i-1)*2) x)
  | cfgL len (S k) m => Some (cfgR len k m)
  | cfgR len k m => Some (cfgL len k (S m))
  | cfgS0 len k h (S n) m => Some (cfgS0 len (k-1) h n m)
  | cfgS0 len k h O m =>
    let a := Nat.div2 h in
    if Nat.even h then
      if Nat.eqb m 0 then Some (cfgR (len+1+a*3) ((k*2+1)*2^(a*3)-1) 1)
      else let (x, i) := split_lowbit m in
        Some (cfgS1 (len+1+a*3) ((k*2+1)*2^(a*3)-1) i ((2^i-1)*2) x)
    else
      if Nat.eqb m 0 then Some (cfgR (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) 0)
      else let (x, i) := split_lowbit m in
        Some (cfgS0 (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) i ((2^i-1)*2+1) x)
  | cfgS1 len k h (S n) m => Some (cfgS1 len (k-1) h n m)
  | cfgS1 len k h O m =>
    let a := Nat.div2 h in
    if Nat.even h then
      if Nat.eqb m 0 then Some (cfgR (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) 0)
      else if Nat.even m then
        let (x, i) := split_lowbit (Nat.div2 m) in
        Some (cfgS1 (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) i ((2^i-1)*2+1) x)
      else
        let (x, j) := split_lowbit (m+1) in
        Some (cfgS0 (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)-1) j ((2^j-1)*2) x)
    else Some (cfgR (len+1+(a*3+3)) ((k*2+1)*2^(a*3+3)) m)
  end.

Ltac div2_cases h a Hh :=
  let Eh := fresh "Eh" in
  pose proof (Nat.div2_odd h) as Hh; destruct (Nat.even h) eqn:Eh;
  rewrite <- Nat.negb_even, Eh in Hh; cbn [negb Nat.b2n] in Hh;
  remember (Nat.div2 h) as a.
Ltac split_lowbit_cases m x i Hm :=
  let E := fresh "Es" in let Hs := fresh "Hs" in
  destruct (split_lowbit m) as [x i] eqn:E;
  pose proof (split_lowbit_spec m Hm) as Hs; rewrite E in Hs.

Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma f_spec (b : Machine) x : P x ->
  match f x with
  | Some y => to_config b x -[machine b]->+ to_config b y /\ P y
  | None => corner x
  end.
Proof.
  intros HP; destruct x as [len k m|len k m|len k h n m|len k h n m];
    cbn [P] in HP; cbn [f].
  - destruct k as [|k].
    + destruct (Nat.eqb_spec m (2^len)) as [E|E]; [cbn [corner]; exact E|].
      assert (Hm : m <> 0) by lia.
      split_lowbit_cases m x i Hm. subst m. cbn [to_config P].
      split; [apply LC_Ov|].
      pose proof (split_bound_v3 x i len ltac:(lia) E). arith.
    + cbn [to_config P]; split; [apply LC_Inc; lia|lia].
  - cbn [to_config P]; split; [apply RC_Inc|lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|]; replace (S k - 1) with k by lia.
      cbn [to_config P]; split.
      - eapply progress_evstep_trans; [apply RS0_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - lia. }
    div2_cases h a Hh; destruct (Nat.eqb_spec m 0) as [Em|Em].
    + subst m; cbn [to_config P]; replace h with (a*2) by lia.
      split; [apply RS0_Ov_0_blank; lia|].
      pose proof (append_bounds len k (a*3) ltac:(lia)); lia.
    + split_lowbit_cases m x i Em; subst m; cbn [to_config P]; replace h with (a*2) by lia.
      split; [apply RS0_Ov_0; lia|].
      pose proof (append_bounds len k (a*3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + subst m; cbn [to_config P]; replace h with (a*2+1) by lia.
      split; [apply RS0_Ov_1_blank; lia|].
      pose proof (append_bounds len k (a*3+2) ltac:(lia)); arith.
    + split_lowbit_cases m x i Em; subst m; cbn [to_config P]; replace h with (a*2+1) by lia.
      split; [apply RS0_Ov_1; lia|].
      pose proof (append_bounds len k (a*3+2) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|]; replace (S k - 1) with k by lia.
      cbn [to_config P]; split.
      - eapply progress_evstep_trans; [apply RS1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - lia. }
    div2_cases h a Hh.
    + replace h with (a*2) by lia.
      destruct (Nat.eqb_spec m 0) as [Em|Em].
      * subst m; cbn [to_config P].
        split; [apply RS1_Ov_0_blank; lia|].
        pose proof (append_bounds len k (a*3+2) ltac:(lia)); arith.
      * destruct (Nat.even m) eqn:Ev.
        -- apply Nat.even_spec in Ev as [c Hc].
           assert (Hd : Nat.div2 m = c) by (subst m; apply Nat.div2_double).
           rewrite Hd. assert (Hc0 : c <> 0) by lia.
           split_lowbit_cases c x i Hc0.
           assert (Hm : m = (x*2+1)*2^i*2) by lia. rewrite Hm. cbn [to_config P].
           split; [apply RS1_Ov_0_even; lia|].
           pose proof (append_bounds len k (a*3+2) ltac:(lia)).
           pose proof (split_bound_v2 x i); arith.
        -- assert (Hm1 : m+1 <> 0) by lia.
           split_lowbit_cases (m+1) x j Hm1.
           assert (Hj : j <> 0).
           { intros ->. assert (Nat.even (m+1) = true) as Hev.
             { rewrite Nat.even_add, Ev. reflexivity. }
             rewrite Hs in Hev. replace ((x*2+1)*2^0) with (2*x+1) in Hev by (cbn; lia).
             rewrite Nat.even_add, Nat.even_mul in Hev. discriminate. }
           assert (Hm : m = (x*2+1)*2^((j-1)+1)-1) by (replace (j-1+1) with j by lia; lia).
           rewrite Hm. replace j with ((j-1)+1) at 2 3 by lia. cbn [to_config P].
           split; [apply RS1_Ov_0_odd; lia|].
           pose proof (append_bounds len k (a*3+1) ltac:(lia)).
           pose proof (split_bound_v2 x (j-1+1)).
           replace (j-1+1) with j in * by lia. arith.
    + replace h with (a*2+1) by lia. cbn [to_config P].
      split; [apply RS1_Ov_1; lia|].
      pose proof (append_bounds len k (a*3+3) ltac:(lia)); arith.
Qed.
End SOC23Model.
