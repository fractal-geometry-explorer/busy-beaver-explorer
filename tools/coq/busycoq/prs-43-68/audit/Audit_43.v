From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.
Require Import String.
Definition target : TM := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.nonhalt. Qed.
Print Assumptions audit.
