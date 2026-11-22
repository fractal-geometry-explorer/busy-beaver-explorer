From BusyCoq Require Import Individual62.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Final.
Require Import String.
Definition target : TM := TM_from_str "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA".
Lemma audit : halts target c0.
Proof. exact Final.bb6_holdout_halts. Qed.
Print Assumptions audit.
