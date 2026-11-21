From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RBHHH_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA.
Require Import String.
Module X := M_1RBHHH_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA.LongLoop62.TM.Enumerate.Permute.Flip.Compute.TM.
(* The proof is stated with a second instance of busycoq's TM functor on the same context BB62.
   Its step, multistep and halts are copies of Individual62's; we prove the two notions of halting agree. *)
Lemma step_to tm c c' : X.step tm c c' -> step tm c c'.
Proof. destruct 1; [eapply step_left | eapply step_right]; eassumption. Qed.
Lemma step_from tm c c' : step tm c c' -> X.step tm c c'.
Proof. destruct 1; [eapply X.step_left | eapply X.step_right]; eassumption. Qed.
Lemma ms_to tm n c c' : X.multistep tm n c c' -> multistep tm n c c'.
Proof. induction 1; econstructor; eauto using step_to. Qed.
Lemma ms_from tm n c c' : multistep tm n c c' -> X.multistep tm n c c'.
Proof. induction 1; econstructor; eauto using step_from. Qed.
Lemma halts_to tm c : X.halts tm c -> halts tm c.
Proof. intros [n [ch [H1 H2]]]. exists n, ch. split; [apply ms_to; exact H1 | exact H2]. Qed.
Lemma halts_from tm c : halts tm c -> X.halts tm c.
Proof. intros [n [ch [H1 H2]]]. exists n, ch. split; [apply ms_from; exact H1 | exact H2]. Qed.
Definition target : TM := TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA".
Lemma audit : ~ halts target c0.
Proof. intro H; apply (M_1RBHHH_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA.TM1.nonhalt); apply halts_from; exact H. Qed.
Print Assumptions audit.
