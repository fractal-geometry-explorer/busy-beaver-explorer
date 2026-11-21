From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.
Require Import String.
Definition target : TM := TM_from_str "1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.nonhalt. Qed.
Print Assumptions audit.
