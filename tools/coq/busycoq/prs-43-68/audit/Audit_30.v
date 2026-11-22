From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RDHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RDHHH.nonhalt. Qed.
Print Assumptions audit.
