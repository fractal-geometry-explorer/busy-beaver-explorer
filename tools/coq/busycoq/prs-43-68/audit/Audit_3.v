From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_HHH0LA.
Require Import String.
Definition target : TM := TM_from_str "1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_HHH0LA.TM1.nonhalt. Qed.
Print Assumptions audit.
