From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---".
Lemma audit : halts target c0.
Proof. exact M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH.halts493. Qed.
Print Assumptions audit.
