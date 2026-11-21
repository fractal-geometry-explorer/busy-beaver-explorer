From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1LC_1LA1RB_1LD0LA_1RE1RD_HHH1RF_1LB0RF.
Require Import String.
Definition target : TM := TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1LC_1LA1RB_1LD0LA_1RE1RD_HHH1RF_1LB0RF.TM1.nonhalt. Qed.
Print Assumptions audit.
