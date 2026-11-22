From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 SOC23Model.
Require Import ZifyNat Lia PeanoNat String.

(* The two machines that SOC23Model covers, and what the model gives:
   from blank tape each machine reaches cfgL 2 0 5, and if it halts, iterating the model
   step f from there reaches a corner cfgL len 0 (2^len). The two machines follow the
   same model orbit, so they reach a corner together or never. *)

Module SOC23Holdouts.
Import SOC23Model.
Open Scope sym.

Definition tm_a := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---").
Definition tm_b := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---").
Definition machine (b:bool) := if b then tm_b else tm_a.

Definition model (b:bool) : SOC23Model.Machine.
Proof.
  refine {| SOC23Model.machine := machine b; SOC23Model.qL := A; SOC23Model.qR := B |}.
  all: abstract (intros; destruct b; es).
Defined.

Lemma init b : c0 -[machine b]->* to_config (model b) (cfgL 2 0 5).
Proof. destruct b; cbn [to_config model LC RC]; esx. Qed.

Close Scope sym.
Fixpoint iter_n (n : nat) (x : Config) : option Config :=
  match n with
  | O => Some x
  | S n' => match f x with Some y => iter_n n' y | None => None end
  end.

Lemma halt_reaches_corner (b : SOC23Model.Machine) n : forall x, P x ->
  halts_in (SOC23Model.machine b) (to_config b x) n -> exists k, iter_n k x = None.
Proof.
  induction n as [n IH] using Wf_nat.lt_wf_ind; intros x HP HH.
  pose proof (f_spec b x HP) as Hs. destruct (f x) as [y|] eqn:E.
  - destruct Hs as [HS Hy].
    destruct (progress_multistep _ _ _ HS) as [k HK].
    pose proof (within_halt _ _ _ _ _ HH HK) as Hle.
    destruct (IH (n - S k) ltac:(lia) y Hy) as [k' Hk'].
    + eapply preceeds_halt; eauto.
    + exists (S k'). cbn [iter_n]. rewrite E. exact Hk'.
  - exists 1. cbn [iter_n]. rewrite E. reflexivity.
Qed.

Theorem halts_reaches_corner b :
  halts (machine b) c0 -> exists k, iter_n k (cfgL 2 0 5) = None.
Proof.
  intros H. rewrite (halts_evstep_iff _ _ _ (init b)) in H. destruct H as [n H].
  apply (halt_reaches_corner (model b) n); [cbn [P]; cbn; lia|exact H].
Qed.

(* Each None of the iteration is a corner. *)
Lemma iter_none_corner k : forall x, P x -> iter_n k x = None ->
  exists j y, iter_n j x = Some y /\ corner y.
Proof.
  induction k as [|k IH]; intros x HP H; cbn [iter_n] in H; [discriminate|].
  pose proof (f_spec (model false) x HP) as Hs. destruct (f x) as [y|] eqn:E.
  - destruct Hs as [_ Hy]. destruct (IH y Hy H) as [j [z [Hj Hz]]].
    exists (S j), z. cbn [iter_n]. rewrite E. split; assumption.
  - exists 0, x. split; [reflexivity|exact Hs].
Qed.

Theorem halts_needs_corner b :
  halts (machine b) c0 ->
  exists j len, iter_n j (cfgL 2 0 5) = Some (cfgL len 0 (2^len)).
Proof.
  intros H. destruct (halts_reaches_corner b H) as [k Hk].
  destruct (iter_none_corner k (cfgL 2 0 5) ltac:(cbn [P]; cbn; lia) Hk) as [j [y [Hj Hy]]].
  destruct y as [len [|k'] n|? ? ?|? ? ? ? ?|? ? ? ? ?]; cbn [corner] in Hy; try contradiction.
  subst n. exists j, len. exact Hj.
Qed.
End SOC23Holdouts.

Print Assumptions SOC23Holdouts.halts_needs_corner.
