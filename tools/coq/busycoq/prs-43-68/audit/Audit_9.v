From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---".
Lemma audit : halts target c0.
Proof. exact M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.halt. Qed.
Print Assumptions audit.
