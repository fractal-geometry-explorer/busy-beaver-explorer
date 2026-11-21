From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB.
Require Import String.
Definition target : TM := TM_from_str "1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB.TM1.nonhalt. Qed.
Print Assumptions audit.
