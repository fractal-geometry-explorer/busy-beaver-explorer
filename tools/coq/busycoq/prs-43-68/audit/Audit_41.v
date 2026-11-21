From BusyCoq Require Import Individual62.
From BusyCoq Require Halt_1RB1LB_1RC0RD.
Require Import String.
Definition target : TM := TM_from_str "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC".
Lemma audit : halts target c0.
Proof. exact Halt_1RB1LB_1RC0RD.halt. Qed.
Print Assumptions audit.
