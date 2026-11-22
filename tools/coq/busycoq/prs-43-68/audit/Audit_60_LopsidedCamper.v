From BusyCoq Require Import Individual62.
From BusyCoq.LopsidedCamper Require Halts273.
Require Import String.
Definition target : TM := TM_from_str "1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE".
Lemma audit : halts target c0.
Proof. exact Halts273.c273_halts. Qed.
Print Assumptions audit.
