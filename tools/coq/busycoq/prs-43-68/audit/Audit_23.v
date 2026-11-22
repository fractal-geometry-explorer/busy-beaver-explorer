From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LAHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LAHHH.TM1.nonhalt. Qed.
Print Assumptions audit.
