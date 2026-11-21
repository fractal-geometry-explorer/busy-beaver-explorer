From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.nonhalt. Qed.
Print Assumptions audit.
