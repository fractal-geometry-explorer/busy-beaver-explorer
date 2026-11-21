From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.
Require Import String.
Definition target : TM := TM_from_str "1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA".
Lemma audit : halts target c0.
Proof. exact M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.halt. Qed.
Print Assumptions audit.
