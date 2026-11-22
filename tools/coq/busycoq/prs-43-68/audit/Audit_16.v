From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.nonhalt. Qed.
Print Assumptions audit.
