From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH.TM1.nonhalt. Qed.
Print Assumptions audit.
