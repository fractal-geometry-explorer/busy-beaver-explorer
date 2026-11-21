From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.
Require Import String.
Definition target : TM := TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.TM1.nonhalt. Qed.
Print Assumptions audit.
