From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LE_0RCHHH_1RD0LA_1RE0RA_0LF1LD_1LC1RF.
Require Import String.
Definition target : TM := TM_from_str "1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF".
Lemma audit : halts target c0.
Proof. exact M_1RB0LE_0RCHHH_1RD0LA_1RE0RA_0LF1LD_1LC1RF.TM1.halt. Qed.
Print Assumptions audit.
