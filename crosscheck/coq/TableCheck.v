From BusyCoq Require Import Individual62.
Require Import String.
Open Scope string_scope.

(* 1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA *)
Definition table_0 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => None
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S1, R, F)
  | (C, S0) => Some (S0, L, E)
  | (C, S1) => Some (S0, R, D)
  | (D, S0) => Some (S0, R, B)
  | (D, S1) => Some (S0, L, C)
  | (E, S0) => Some (S1, R, D)
  | (E, S1) => Some (S0, L, D)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_0 : forall q s, TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA" (q, s) = table_0 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA *)
Definition table_1 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => None
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S1, R, F)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S0, L, B)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S0, L, D)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_1 : forall q s, TM_from_str "1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA" (q, s) = table_1 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB *)
Definition table_2 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, A)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S1, R, C)
  | (D, S0) => Some (S1, L, D)
  | (D, S1) => Some (S1, R, E)
  | (E, S0) => Some (S1, L, A)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => None
  | (F, S1) => Some (S0, R, B)
  end.
Lemma table_ok_2 : forall q s, TM_from_str "1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB" (q, s) = table_2 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD--- *)
Definition table_3 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, A)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, D)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S1, L, A)
  | (D, S0) => Some (S1, L, F)
  | (D, S1) => Some (S0, R, E)
  | (E, S0) => Some (S1, L, B)
  | (E, S1) => Some (S1, R, E)
  | (F, S0) => Some (S1, R, D)
  | (F, S1) => None
  end.
Lemma table_ok_3 : forall q s, TM_from_str "1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---" (q, s) = table_3 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA--- *)
Definition table_4 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, B)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S0, L, A)
  | (D, S1) => Some (S0, R, B)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => Some (S1, L, A)
  | (F, S1) => None
  end.
Lemma table_ok_4 : forall q s, TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---" (q, s) = table_4 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC--- *)
Definition table_5 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, B)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S0, L, A)
  | (D, S1) => Some (S0, R, F)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S0, L, C)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => None
  end.
Lemma table_ok_5 : forall q s, TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---" (q, s) = table_5 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC--- *)
Definition table_6 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, B)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S0, L, A)
  | (D, S1) => Some (S0, R, F)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S1, R, B)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => None
  end.
Lemma table_ok_6 : forall q s, TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---" (q, s) = table_6 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC--- *)
Definition table_7 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, B)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S0, L, A)
  | (D, S1) => Some (S0, R, F)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => None
  end.
Lemma table_ok_7 : forall q s, TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---" (q, s) = table_7 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE--- *)
Definition table_8 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, B)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, R, F)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, R, B)
  | (E, S0) => Some (S0, L, A)
  | (E, S1) => Some (S0, R, E)
  | (F, S0) => Some (S1, R, E)
  | (F, S1) => None
  end.
Lemma table_ok_8 : forall q s, TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---" (q, s) = table_8 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE--- *)
Definition table_9 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, B)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, R, F)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, R, B)
  | (E, S0) => Some (S0, L, A)
  | (E, S1) => Some (S1, R, B)
  | (F, S0) => Some (S1, R, E)
  | (F, S1) => None
  end.
Lemma table_ok_9 : forall q s, TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---" (q, s) = table_9 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF *)
Definition table_10 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, C)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, B)
  | (C, S0) => Some (S0, L, E)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S1, L, C)
  | (D, S1) => None
  | (E, S0) => Some (S0, R, A)
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S1, L, A)
  | (F, S1) => Some (S1, L, F)
  end.
Lemma table_ok_10 : forall q s, TM_from_str "1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF" (q, s) = table_10 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB--- *)
Definition table_11 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, C)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S1, R, F)
  | (C, S1) => Some (S1, L, D)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S0, L, B)
  | (E, S0) => Some (S1, R, D)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S1, L, B)
  | (F, S1) => None
  end.
Lemma table_ok_11 : forall q s, TM_from_str "1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---" (q, s) = table_11 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- *)
Definition table_12 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, C)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, A)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, E)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, D)
  | (E, S0) => Some (S0, R, A)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S0, L, D)
  | (F, S1) => None
  end.
Lemma table_ok_12 : forall q s, TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---" (q, s) = table_12 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC--- *)
Definition table_13 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, C)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, A)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, E)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, D)
  | (E, S0) => Some (S0, R, A)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => None
  end.
Lemma table_ok_13 : forall q s, TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---" (q, s) = table_13 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- *)
Definition table_14 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, C)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, F)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, D)
  | (E, S0) => Some (S1, R, C)
  | (E, S1) => Some (S0, L, A)
  | (F, S0) => Some (S0, L, A)
  | (F, S1) => None
  end.
Lemma table_ok_14 : forall q s, TM_from_str "1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---" (q, s) = table_14 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA *)
Definition table_15 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, D)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => None
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S0, R, F)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S1, L, D)
  | (E, S0) => Some (S0, L, A)
  | (E, S1) => Some (S0, R, D)
  | (F, S0) => Some (S0, R, B)
  | (F, S1) => Some (S1, R, A)
  end.
Lemma table_ok_15 : forall q s, TM_from_str "1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA" (q, s) = table_15 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD *)
Definition table_16 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, D)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => None
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S0, R, F)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, A)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S1, L, E)
  | (F, S0) => Some (S1, R, A)
  | (F, S1) => Some (S0, R, D)
  end.
Lemma table_ok_16 : forall q s, TM_from_str "1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD" (q, s) = table_16 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA--- *)
Definition table_17 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, D)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S1, R, A)
  | (D, S0) => Some (S0, R, E)
  | (D, S1) => Some (S1, R, F)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S0, R, C)
  | (F, S0) => Some (S0, L, A)
  | (F, S1) => None
  end.
Lemma table_ok_17 : forall q s, TM_from_str "1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---" (q, s) = table_17 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- *)
Definition table_18 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, D)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, D)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S0, L, C)
  | (D, S0) => Some (S1, R, E)
  | (D, S1) => Some (S0, L, B)
  | (E, S0) => Some (S1, R, B)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => Some (S0, L, D)
  | (F, S1) => None
  end.
Lemma table_ok_18 : forall q s, TM_from_str "1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---" (q, s) = table_18 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF *)
Definition table_19 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => None
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, L, A)
  | (D, S0) => Some (S1, R, E)
  | (D, S1) => Some (S0, R, A)
  | (E, S0) => Some (S0, L, F)
  | (E, S1) => Some (S1, L, D)
  | (F, S0) => Some (S1, L, C)
  | (F, S1) => Some (S1, R, F)
  end.
Lemma table_ok_19 : forall q s, TM_from_str "1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF" (q, s) = table_19 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB *)
Definition table_20 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => None
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S0, R, F)
  | (E, S0) => Some (S0, R, C)
  | (E, S1) => Some (S0, L, A)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => Some (S0, R, B)
  end.
Lemma table_ok_20 : forall q s, TM_from_str "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB" (q, s) = table_20 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD *)
Definition table_21 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, B)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, R, C)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, R, C)
  | (E, S0) => None
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S1, L, B)
  | (F, S1) => Some (S1, L, D)
  end.
Lemma table_ok_21 : forall q s, TM_from_str "1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD" (q, s) = table_21 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA--- *)
Definition table_22 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, A)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, E)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, D)
  | (E, S0) => Some (S1, L, D)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => None
  end.
Lemma table_ok_22 : forall q s, TM_from_str "1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---" (q, s) = table_22 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- *)
Definition table_23 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, C)
  | (E, S0) => Some (S0, L, C)
  | (E, S1) => Some (S0, L, F)
  | (F, S0) => Some (S0, R, B)
  | (F, S1) => None
  end.
Lemma table_ok_23 : forall q s, TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---" (q, s) = table_23 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA--- *)
Definition table_24 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, C)
  | (E, S0) => Some (S0, L, C)
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => None
  end.
Lemma table_ok_24 : forall q s, TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---" (q, s) = table_24 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC--- *)
Definition table_25 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, E)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, C)
  | (E, S0) => Some (S1, R, B)
  | (E, S1) => Some (S0, L, F)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => None
  end.
Lemma table_ok_25 : forall q s, TM_from_str "1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---" (q, s) = table_25 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC *)
Definition table_26 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, L, A)
  | (C, S0) => Some (S1, R, A)
  | (C, S1) => Some (S0, R, D)
  | (D, S0) => None
  | (D, S1) => Some (S1, R, E)
  | (E, S0) => Some (S1, L, A)
  | (E, S1) => Some (S1, R, C)
  | (F, S0) => Some (S0, L, B)
  | (F, S1) => Some (S0, R, C)
  end.
Lemma table_ok_26 : forall q s, TM_from_str "1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC" (q, s) = table_26 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE *)
Definition table_27 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S1, L, B)
  | (D, S0) => None
  | (D, S1) => Some (S1, R, E)
  | (E, S0) => Some (S0, R, A)
  | (E, S1) => Some (S1, R, E)
  | (F, S0) => Some (S1, L, A)
  | (F, S1) => Some (S0, L, E)
  end.
Lemma table_ok_27 : forall q s, TM_from_str "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE" (q, s) = table_27 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1LC0RD_1LA1LC_---0RE_0RB1RA_1LC1LF *)
Definition table_28 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, D)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => None
  | (D, S1) => Some (S0, R, E)
  | (E, S0) => Some (S0, R, B)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S1, L, C)
  | (F, S1) => Some (S1, L, F)
  end.
Lemma table_ok_28 : forall q s, TM_from_str "1RB0LF_1LC0RD_1LA1LC_---0RE_0RB1RA_1LC1LF" (q, s) = table_28 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF *)
Definition table_29 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => None
  | (E, S0) => Some (S0, R, B)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S0, L, E)
  | (F, S1) => Some (S1, L, F)
  end.
Lemma table_ok_29 : forall q s, TM_from_str "1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_0LE1LF" (q, s) = table_29 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF *)
Definition table_30 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => None
  | (E, S0) => Some (S0, R, B)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S1, L, C)
  | (F, S1) => Some (S1, L, F)
  end.
Lemma table_ok_30 : forall q s, TM_from_str "1RB0LF_1LC0RE_0LD1LC_1LA---_0RB1RA_1LC1LF" (q, s) = table_30 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB--- *)
Definition table_31 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, B)
  | (D, S0) => Some (S0, L, E)
  | (D, S1) => Some (S0, L, C)
  | (E, S0) => Some (S0, L, A)
  | (E, S1) => Some (S0, L, C)
  | (F, S0) => Some (S0, L, B)
  | (F, S1) => None
  end.
Lemma table_ok_31 : forall q s, TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---" (q, s) = table_31 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD--- *)
Definition table_32 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, L, F)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, R, B)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S1, L, E)
  | (D, S0) => Some (S0, L, E)
  | (D, S1) => Some (S0, R, A)
  | (E, S0) => Some (S1, L, C)
  | (E, S1) => Some (S1, L, A)
  | (F, S0) => Some (S0, L, D)
  | (F, S1) => None
  end.
Lemma table_ok_32 : forall q s, TM_from_str "1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---" (q, s) = table_32 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA *)
Definition table_33 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, A)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S1, R, F)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S1, L, D)
  | (E, S0) => Some (S1, L, B)
  | (E, S1) => Some (S1, R, E)
  | (F, S0) => None
  | (F, S1) => Some (S1, R, A)
  end.
Lemma table_ok_33 : forall q s, TM_from_str "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA" (q, s) = table_33 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB *)
Definition table_34 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, A)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, L, C)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S1, L, F)
  | (E, S0) => None
  | (E, S1) => Some (S1, L, D)
  | (F, S0) => Some (S1, L, D)
  | (F, S1) => Some (S1, L, B)
  end.
Lemma table_ok_34 : forall q s, TM_from_str "1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB" (q, s) = table_34 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA *)
Definition table_35 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, A)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, F)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, R, D)
  | (E, S0) => Some (S1, L, D)
  | (E, S1) => Some (S1, L, E)
  | (F, S0) => None
  | (F, S1) => Some (S1, R, A)
  end.
Lemma table_ok_35 : forall q s, TM_from_str "1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA" (q, s) = table_35 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC--- *)
Definition table_36 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, A)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S1, L, D)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S0, R, E)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S1, R, A)
  | (E, S1) => Some (S0, L, F)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => None
  end.
Lemma table_ok_36 : forall q s, TM_from_str "1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---" (q, s) = table_36 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- *)
Definition table_37 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, A)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, C)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S1, R, F)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S1, L, D)
  | (E, S1) => Some (S0, L, B)
  | (F, S0) => Some (S0, R, E)
  | (F, S1) => None
  end.
Lemma table_ok_37 : forall q s, TM_from_str "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---" (q, s) = table_37 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA *)
Definition table_38 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, B)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S1, R, A)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S0, L, D)
  | (F, S0) => None
  | (F, S1) => Some (S0, L, A)
  end.
Lemma table_ok_38 : forall q s, TM_from_str "1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA" (q, s) = table_38 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA--- *)
Definition table_39 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, C)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, R, A)
  | (C, S1) => Some (S0, R, D)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, R, F)
  | (E, S0) => Some (S1, L, C)
  | (E, S1) => Some (S1, L, B)
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => None
  end.
Lemma table_ok_39 : forall q s, TM_from_str "1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---" (q, s) = table_39 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA *)
Definition table_40 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, C)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S1, R, C)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, F)
  | (E, S0) => Some (S0, L, A)
  | (E, S1) => Some (S1, L, C)
  | (F, S0) => None
  | (F, S1) => Some (S1, L, A)
  end.
Lemma table_ok_40 : forall q s, TM_from_str "1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA" (q, s) = table_40 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC--- *)
Definition table_41 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, C)
  | (B, S0) => Some (S1, L, A)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, R, B)
  | (C, S1) => Some (S0, R, D)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, R, F)
  | (E, S0) => Some (S0, L, B)
  | (E, S1) => Some (S0, R, B)
  | (F, S0) => Some (S1, R, C)
  | (F, S1) => None
  end.
Lemma table_ok_41 : forall q s, TM_from_str "1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC---" (q, s) = table_41 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB *)
Definition table_42 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, C)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => None
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, D)
  | (E, S0) => Some (S1, R, A)
  | (E, S1) => Some (S0, L, F)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => Some (S0, R, B)
  end.
Lemma table_ok_42 : forall q s, TM_from_str "1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB" (q, s) = table_42 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF *)
Definition table_43 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, D)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, F)
  | (C, S0) => Some (S0, L, A)
  | (C, S1) => Some (S0, R, B)
  | (D, S0) => Some (S1, R, E)
  | (D, S1) => None
  | (E, S0) => Some (S1, L, B)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S0, L, E)
  | (F, S1) => Some (S0, L, F)
  end.
Lemma table_ok_43 : forall q s, TM_from_str "1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF" (q, s) = table_43 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA *)
Definition table_44 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, D)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, F)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S0, L, B)
  | (D, S0) => None
  | (D, S1) => Some (S1, R, E)
  | (E, S0) => Some (S1, L, B)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_44 : forall q s, TM_from_str "1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA" (q, s) = table_44 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB--- *)
Definition table_45 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, D)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S0, L, A)
  | (C, S1) => Some (S0, L, E)
  | (D, S0) => Some (S1, L, C)
  | (D, S1) => Some (S1, R, F)
  | (E, S0) => Some (S1, L, A)
  | (E, S1) => Some (S1, L, C)
  | (F, S0) => Some (S0, R, B)
  | (F, S1) => None
  end.
Lemma table_ok_45 : forall q s, TM_from_str "1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---" (q, s) = table_45 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC *)
Definition table_46 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, D)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, L, A)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, R, A)
  | (E, S0) => Some (S0, L, F)
  | (E, S1) => None
  | (F, S0) => Some (S0, L, A)
  | (F, S1) => Some (S0, L, C)
  end.
Lemma table_ok_46 : forall q s, TM_from_str "1RB0RD_1RC1RB_1LD0LA_1LE0RA_0LF---_0LA0LC" (q, s) = table_46 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD *)
Definition table_47 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, E)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, L, B)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, L, B)
  | (D, S0) => Some (S1, R, F)
  | (D, S1) => Some (S0, L, A)
  | (E, S0) => Some (S1, R, C)
  | (E, S1) => None
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => Some (S0, L, D)
  end.
Lemma table_ok_47 : forall q s, TM_from_str "1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD" (q, s) = table_47 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- *)
Definition table_48 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, E)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S1, R, E)
  | (C, S1) => Some (S1, L, D)
  | (D, S0) => Some (S0, L, B)
  | (D, S1) => Some (S0, L, F)
  | (E, S0) => Some (S1, R, A)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S0, L, D)
  | (F, S1) => None
  end.
Lemma table_ok_48 : forall q s, TM_from_str "1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---" (q, s) = table_48 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC *)
Definition table_49 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, E)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S1, R, F)
  | (C, S1) => Some (S0, R, D)
  | (D, S0) => None
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S0, L, B)
  | (E, S1) => Some (S1, L, E)
  | (F, S0) => Some (S1, L, E)
  | (F, S1) => Some (S1, R, C)
  end.
Lemma table_ok_49 : forall q s, TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC" (q, s) = table_49 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA *)
Definition table_50 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, E)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S1, L, F)
  | (C, S0) => Some (S1, R, A)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, L, A)
  | (E, S0) => Some (S1, R, B)
  | (E, S1) => Some (S1, R, C)
  | (F, S0) => None
  | (F, S1) => Some (S0, L, A)
  end.
Lemma table_ok_50 : forall q s, TM_from_str "1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA" (q, s) = table_50 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF *)
Definition table_51 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => None
  | (D, S0) => Some (S0, R, E)
  | (D, S1) => Some (S0, R, A)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S0, L, B)
  | (F, S0) => Some (S1, L, A)
  | (F, S1) => Some (S1, L, F)
  end.
Lemma table_ok_51 : forall q s, TM_from_str "1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF" (q, s) = table_51 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA--- *)
Definition table_52 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S0, L, B)
  | (D, S0) => Some (S0, L, A)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S1, L, C)
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S0, L, A)
  | (F, S1) => None
  end.
Lemma table_ok_52 : forall q s, TM_from_str "1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---" (q, s) = table_52 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA *)
Definition table_53 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, F)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S1, R, A)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S0, L, C)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, R, E)
  | (E, S0) => None
  | (E, S1) => Some (S0, R, A)
  | (F, S0) => Some (S1, R, C)
  | (F, S1) => Some (S1, R, A)
  end.
Lemma table_ok_53 : forall q s, TM_from_str "1RB0RF_1LC1RA_0RD0LC_1LB1RE_---0RA_1RC1RA" (q, s) = table_53 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD--- *)
Definition table_54 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S0, R, F)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S0, L, B)
  | (E, S1) => Some (S0, R, E)
  | (F, S0) => Some (S0, R, D)
  | (F, S1) => None
  end.
Lemma table_ok_54 : forall q s, TM_from_str "1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---" (q, s) = table_54 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF *)
Definition table_55 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, A)
  | (B, S0) => Some (S1, L, A)
  | (B, S1) => Some (S1, R, C)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, R, B)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S1, L, D)
  | (E, S0) => None
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S1, R, A)
  | (F, S1) => Some (S0, L, F)
  end.
Lemma table_ok_55 : forall q s, TM_from_str "1RB1LA_1LA1RC_1RD0RB_1LE1LD_---1LF_1RA0LF" (q, s) = table_55 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC *)
Definition table_56 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, B)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, R, D)
  | (C, S0) => Some (S0, L, A)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S0, R, F)
  | (D, S1) => Some (S1, L, C)
  | (E, S0) => Some (S1, L, A)
  | (E, S1) => Some (S0, R, B)
  | (F, S0) => None
  | (F, S1) => Some (S1, L, C)
  end.
Lemma table_ok_56 : forall q s, TM_from_str "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC" (q, s) = table_56 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC *)
Definition table_57 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, C)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, L, A)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => None
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S1, R, A)
  | (F, S0) => Some (S1, L, A)
  | (F, S1) => Some (S1, L, C)
  end.
Lemma table_ok_57 : forall q s, TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC" (q, s) = table_57 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LC_1LA0RD_1LA0LA_---1RE_1RB0RF_1RC0RA *)
Definition table_58 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, C)
  | (B, S0) => Some (S1, L, A)
  | (B, S1) => Some (S0, R, D)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S0, L, A)
  | (D, S0) => None
  | (D, S1) => Some (S1, R, E)
  | (E, S0) => Some (S1, R, B)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S1, R, C)
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_58 : forall q s, TM_from_str "1RB1LC_1LA0RD_1LA0LA_---1RE_1RB0RF_1RC0RA" (q, s) = table_58 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF *)
Definition table_59 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, C)
  | (B, S0) => Some (S1, L, A)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, L, A)
  | (D, S0) => Some (S1, R, E)
  | (D, S1) => Some (S1, R, D)
  | (E, S0) => None
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => Some (S1, L, B)
  | (F, S1) => Some (S0, R, F)
  end.
Lemma table_ok_59 : forall q s, TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF" (q, s) = table_59 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC--- *)
Definition table_60 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, C)
  | (B, S0) => Some (S1, L, A)
  | (B, S1) => Some (S1, R, F)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S1, R, D)
  | (D, S0) => Some (S0, R, A)
  | (D, S1) => Some (S0, L, E)
  | (E, S0) => Some (S1, L, A)
  | (E, S1) => Some (S0, L, E)
  | (F, S0) => Some (S0, R, C)
  | (F, S1) => None
  end.
Lemma table_ok_60 : forall q s, TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---" (q, s) = table_60 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LD_1LC0RF_0RD0LB_1LB0LE_1LA---_0RA0RF *)
Definition table_61 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, D)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, F)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S0, L, B)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S0, L, E)
  | (E, S0) => Some (S1, L, A)
  | (E, S1) => None
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => Some (S0, R, F)
  end.
Lemma table_ok_61 : forall q s, TM_from_str "1RB1LD_1LC0RF_0RD0LB_1LB0LE_1LA---_0RA0RF" (q, s) = table_61 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB *)
Definition table_62 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, E)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S1, R, E)
  | (C, S0) => None
  | (C, S1) => Some (S1, L, D)
  | (D, S0) => Some (S0, R, D)
  | (D, S1) => Some (S1, L, A)
  | (E, S0) => Some (S0, R, F)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => Some (S1, R, A)
  | (F, S1) => Some (S0, L, B)
  end.
Lemma table_ok_62 : forall q s, TM_from_str "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB" (q, s) = table_62 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA *)
Definition table_63 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, E)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S1, R, A)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S0, R, B)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, F)
  | (E, S0) => Some (S0, L, C)
  | (E, S1) => Some (S1, R, F)
  | (F, S0) => None
  | (F, S1) => Some (S0, L, A)
  end.
Lemma table_ok_63 : forall q s, TM_from_str "1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA" (q, s) = table_63 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA *)
Definition table_64 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, E)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S1, R, E)
  | (C, S0) => Some (S1, L, E)
  | (C, S1) => Some (S1, L, D)
  | (D, S0) => Some (S1, L, C)
  | (D, S1) => Some (S0, L, A)
  | (E, S0) => Some (S1, R, F)
  | (E, S1) => Some (S0, L, A)
  | (F, S0) => None
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_64 : forall q s, TM_from_str "1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA" (q, s) = table_64 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- *)
Definition table_65 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, E)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S0, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, C)
  | (D, S0) => Some (S1, L, A)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S0, L, A)
  | (F, S0) => Some (S1, L, C)
  | (F, S1) => None
  end.
Lemma table_ok_65 : forall q s, TM_from_str "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---" (q, s) = table_65 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1RD_0LD--- *)
Definition table_66 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, F)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S1, R, D)
  | (D, S0) => Some (S0, L, B)
  | (D, S1) => Some (S1, L, B)
  | (E, S0) => Some (S1, R, C)
  | (E, S1) => Some (S1, R, D)
  | (F, S0) => Some (S0, L, D)
  | (F, S1) => None
  end.
Lemma table_ok_66 : forall q s, TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1RD_0LD---" (q, s) = table_66 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- *)
Definition table_67 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, F)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, R, B)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S1, R, B)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, B)
  | (E, S0) => Some (S0, L, A)
  | (E, S1) => Some (S1, L, C)
  | (F, S0) => Some (S0, L, B)
  | (F, S1) => None
  end.
Lemma table_ok_67 : forall q s, TM_from_str "1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---" (q, s) = table_67 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA *)
Definition table_68 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, L, F)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, R, D)
  | (C, S1) => Some (S0, R, B)
  | (D, S0) => Some (S0, L, E)
  | (D, S1) => Some (S0, L, F)
  | (E, S0) => None
  | (E, S1) => Some (S1, L, D)
  | (F, S0) => Some (S0, L, E)
  | (F, S1) => Some (S1, L, A)
  end.
Lemma table_ok_68 : forall q s, TM_from_str "1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA" (q, s) = table_68 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD *)
Definition table_69 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, A)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S1, R, C)
  | (C, S1) => Some (S1, L, D)
  | (D, S0) => Some (S0, L, B)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S0, R, C)
  | (F, S0) => None
  | (F, S1) => Some (S0, L, D)
  end.
Lemma table_ok_69 : forall q s, TM_from_str "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD" (q, s) = table_69 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE *)
Definition table_70 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, A)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, D)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, L, B)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, F)
  | (E, S0) => Some (S0, R, A)
  | (E, S1) => None
  | (F, S0) => Some (S0, L, B)
  | (F, S1) => Some (S0, L, E)
  end.
Lemma table_ok_70 : forall q s, TM_from_str "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE" (q, s) = table_70 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF *)
Definition table_71 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, A)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, L, B)
  | (C, S0) => Some (S0, L, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, R, F)
  | (D, S1) => Some (S1, L, E)
  | (E, S0) => None
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S1, L, C)
  | (F, S1) => Some (S0, L, F)
  end.
Lemma table_ok_71 : forall q s, TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF" (q, s) = table_71 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD--- *)
Definition table_72 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, B)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S0, L, D)
  | (C, S0) => Some (S0, L, E)
  | (C, S1) => Some (S1, L, D)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S0, R, E)
  | (E, S0) => Some (S1, R, A)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S1, R, D)
  | (F, S1) => None
  end.
Lemma table_ok_72 : forall q s, TM_from_str "1RB1RB_0LC0LD_0LE1LD_1LB0RE_1RA0RF_1RD---" (q, s) = table_72 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF *)
Definition table_73 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, C)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S1, R, E)
  | (C, S0) => Some (S1, R, A)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S0, R, D)
  | (E, S0) => Some (S0, R, F)
  | (E, S1) => None
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => Some (S0, R, F)
  end.
Lemma table_ok_73 : forall q s, TM_from_str "1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF" (q, s) = table_73 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA *)
Definition table_74 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, C)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, L, F)
  | (C, S0) => Some (S1, R, F)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S0, R, E)
  | (D, S1) => Some (S1, L, B)
  | (E, S0) => Some (S1, R, C)
  | (E, S1) => None
  | (F, S0) => Some (S1, L, D)
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_74 : forall q s, TM_from_str "1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA" (q, s) = table_74 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC *)
Definition table_75 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, D)
  | (B, S0) => Some (S0, L, C)
  | (B, S1) => Some (S0, L, B)
  | (C, S0) => Some (S0, R, E)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S0, R, B)
  | (E, S0) => Some (S1, R, F)
  | (E, S1) => None
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => Some (S0, R, C)
  end.
Lemma table_ok_75 : forall q s, TM_from_str "1RB1RD_0LC0LB_0RE0LD_1LB0RB_1RF---_0RA0RC" (q, s) = table_75 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC--- *)
Definition table_76 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, D)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, L, E)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, L, B)
  | (D, S0) => Some (S0, R, B)
  | (D, S1) => Some (S0, R, A)
  | (E, S0) => Some (S1, R, D)
  | (E, S1) => Some (S1, L, F)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => None
  end.
Lemma table_ok_76 : forall q s, TM_from_str "1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---" (q, s) = table_76 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- *)
Definition table_77 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, D)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S0, L, B)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S0, L, C)
  | (F, S1) => None
  end.
Lemma table_ok_77 : forall q s, TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---" (q, s) = table_77 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- *)
Definition table_78 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, D)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S0, L, B)
  | (E, S0) => Some (S0, R, D)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S0, R, D)
  | (F, S1) => None
  end.
Lemma table_ok_78 : forall q s, TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---" (q, s) = table_78 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD--- *)
Definition table_79 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, D)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, L, C)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S0, L, E)
  | (E, S0) => Some (S1, L, C)
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S0, R, D)
  | (F, S1) => None
  end.
Lemma table_ok_79 : forall q s, TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---" (q, s) = table_79 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE *)
Definition table_80 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, D)
  | (B, S0) => Some (S1, R, C)
  | (B, S1) => Some (S1, R, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S0, R, A)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S0, L, E)
  | (E, S0) => Some (S1, L, F)
  | (E, S1) => Some (S0, L, C)
  | (F, S0) => None
  | (F, S1) => Some (S1, L, E)
  end.
Lemma table_ok_80 : forall q s, TM_from_str "1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE" (q, s) = table_80 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RE_0RC0RF_1LC1RD_1RA0LE_0RA0LD_0RA--- *)
Definition table_81 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, E)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, R, F)
  | (C, S0) => Some (S1, L, C)
  | (C, S1) => Some (S1, R, D)
  | (D, S0) => Some (S1, R, A)
  | (D, S1) => Some (S0, L, E)
  | (E, S0) => Some (S0, R, A)
  | (E, S1) => Some (S0, L, D)
  | (F, S0) => Some (S0, R, A)
  | (F, S1) => None
  end.
Lemma table_ok_81 : forall q s, TM_from_str "1RB1RE_0RC0RF_1LC1RD_1RA0LE_0RA0LD_0RA---" (q, s) = table_81 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- *)
Definition table_82 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, E)
  | (B, S0) => Some (S1, L, C)
  | (B, S1) => Some (S0, R, A)
  | (C, S0) => Some (S1, L, A)
  | (C, S1) => Some (S0, L, D)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S0, L, F)
  | (E, S0) => Some (S0, R, B)
  | (E, S1) => Some (S0, L, E)
  | (F, S0) => Some (S0, L, A)
  | (F, S1) => None
  end.
Lemma table_ok_82 : forall q s, TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---" (q, s) = table_82 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA *)
Definition table_83 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, F)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, L, B)
  | (C, S0) => Some (S1, L, D)
  | (C, S1) => Some (S1, R, E)
  | (D, S0) => Some (S1, L, B)
  | (D, S1) => Some (S1, R, F)
  | (E, S0) => None
  | (E, S1) => Some (S0, R, F)
  | (F, S0) => Some (S1, R, D)
  | (F, S1) => Some (S0, R, A)
  end.
Lemma table_ok_83 : forall q s, TM_from_str "1RB1RF_0RC0LB_1LD1RE_1LB1RF_---0RF_1RD0RA" (q, s) = table_83 (q, s).
Proof. intros [] []; reflexivity. Qed.

(* 1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD--- *)
Definition table_84 (qs : Q * Sym) : option (Sym * dir * Q) :=
  match qs with
  | (A, S0) => Some (S1, R, B)
  | (A, S1) => Some (S1, R, F)
  | (B, S0) => Some (S0, R, C)
  | (B, S1) => Some (S0, R, E)
  | (C, S0) => Some (S0, R, D)
  | (C, S1) => Some (S1, R, A)
  | (D, S0) => Some (S1, L, E)
  | (D, S1) => Some (S0, L, A)
  | (E, S0) => Some (S1, L, B)
  | (E, S1) => Some (S0, L, D)
  | (F, S0) => Some (S0, R, D)
  | (F, S1) => None
  end.
Lemma table_ok_84 : forall q s, TM_from_str "1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---" (q, s) = table_84 (q, s).
Proof. intros [] []; reflexivity. Qed.

