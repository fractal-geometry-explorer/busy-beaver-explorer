From BusyCoq Require Import Individual62.
From BusyCoq Require Halt_1RB0RB_0LC1RA.
Require Import String.
Definition target : TM := TM_from_str "1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA".
Lemma audit : halts target c0.
Proof. exact Halt_1RB0RB_0LC1RA.halt. Qed.
Print Assumptions audit.
