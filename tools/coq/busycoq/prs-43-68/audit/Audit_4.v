From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB.
Require Import String.
Definition target : TM := TM_from_str "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB.TM1.nonhalt. Qed.
Print Assumptions audit.
