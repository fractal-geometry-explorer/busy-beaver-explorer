From BusyCoq Require Import Individual62.
From BusyCoq Require M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.
Require Import String.
Definition target : TM := TM_from_str "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA".
Lemma audit : ~ halts target c0.
Proof. exact M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.nonhalt. Qed.
Print Assumptions audit.
