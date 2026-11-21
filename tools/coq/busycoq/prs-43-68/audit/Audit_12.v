From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.
Require Import String.
Definition target : TM := TM_from_str "1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---".
Lemma audit : halts target c0.
Proof. exact M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.halt. Qed.
Print Assumptions audit.
