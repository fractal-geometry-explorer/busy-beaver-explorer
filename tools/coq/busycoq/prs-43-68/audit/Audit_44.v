From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA.
Require Import String.
Definition target : TM := TM_from_str "1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA.nonhalt. Qed.
Print Assumptions audit.
