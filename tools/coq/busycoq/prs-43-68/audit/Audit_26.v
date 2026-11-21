From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LD_0RCHHH_0RD0RF_1LE0LA_1LF1LE_1RA0RD.
Require Import String.
Definition target : TM := TM_from_str "1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LD_0RCHHH_0RD0RF_1LE0LA_1LF1LE_1RA0RD.TM3.nonhalt. Qed.
Print Assumptions audit.
