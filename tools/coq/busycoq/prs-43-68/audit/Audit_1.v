From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1LA_1LA1RC_1RD0RB_1LE1LD_HHH1LF_1RA0LF.
Require Import String.
Definition target : TM := TM_from_str "1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1LA_1LA1RC_1RD0RB_1LE1LD_HHH1LF_1RA0LF.TM1.nonhalt. Qed.
Print Assumptions audit.
