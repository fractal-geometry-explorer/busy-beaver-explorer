From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LD_0RCHHH_0RD0RF_1LE0LA_1LF1LE_1RA0RD.
Require Import String.
Definition target : TM := TM_from_str "1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LD_0RCHHH_0RD0RF_1LE0LA_1LF1LE_1RA0RD.TM1.nonhalt. Qed.
Print Assumptions audit.
