From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF.
Require Import String.
Definition target : TM := TM_from_str "1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF.TM1.nonhalt. Qed.
Print Assumptions audit.
