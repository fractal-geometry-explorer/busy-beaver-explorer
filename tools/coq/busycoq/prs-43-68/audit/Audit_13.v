From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---".
Lemma audit : halts target c0.
Proof. exact M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.halt. Qed.
Print Assumptions audit.
