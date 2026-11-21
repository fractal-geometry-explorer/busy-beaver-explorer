From BusyCoq Require Import Individual62.
From BusyCoq Require ShiftOverflowCounter_F1C.
Require Import String.
Definition target : TM := TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC".
Lemma audit : ~ halts target c0.
Proof. exact ShiftOverflowCounter_F1C.nonhalt. Qed.
Print Assumptions audit.
