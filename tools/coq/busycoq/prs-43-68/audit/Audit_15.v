From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.
Require Import String.
Definition target : TM := TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.nonhalt. Qed.
Print Assumptions audit.
