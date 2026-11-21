From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LF_1LC0RE_0LD1LC_1LAHHH_0RB1RA_1LC1LF.
Require Import String.
Definition target : TM := TM_from_str "1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LF_1LC0RE_0LD1LC_1LAHHH_0RB1RA_1LC1LF.nonhalt. Qed.
Print Assumptions audit.
