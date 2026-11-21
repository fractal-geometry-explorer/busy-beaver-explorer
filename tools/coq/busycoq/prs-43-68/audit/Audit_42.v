From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.
Require Import String.
Definition target : TM := TM_from_str "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.nonhalt. Qed.
Print Assumptions audit.
