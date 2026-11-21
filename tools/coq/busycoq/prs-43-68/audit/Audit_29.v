From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0RF_1LC1RA_0RD0LC_1LB1RE_HHH0RA_1RC1RA.
Require Import String.
Definition target : TM := TM_from_str "1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0RF_1LC1RA_0RD0LC_1LB1RE_HHH0RA_1RC1RA.TM2.nonhalt. Qed.
Print Assumptions audit.
