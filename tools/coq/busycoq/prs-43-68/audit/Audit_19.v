From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA.
Require Import String.
Definition target : TM := TM_from_str "1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA.nonhalt. Qed.
Print Assumptions audit.
