(** * SymRun: checking symbolic runs of a 6-state machine by computation

    A configuration whose tape is a list of tokens: single cells, and runs [w^n] of a word [w] whose count [n] is a
    linear expression [c + a1 x1 + a2 x2 + ...] in some variables.  [auto] searches for a run from one such
    configuration to a target: it takes single machine steps (unrolling a run whose count is surely at least 1),
    crosses whole runs by a shift rule found on the spot (one copy simulated on a window of cells), and re-brackets
    runs ([x (y x)^n = (x y)^n x], [w^(m q + r) = (w^m)^q w^r]).  Everything it does is a computation on data;
    [auto_sound] proves that when it answers [true], the real machine goes from the one configuration to the other
    in at least one step, for every value of the variables. *)

From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lia PeanoNat Bool.
From BusyCoq Require Export Individual62.
Set Default Goal Selector "!".
Local Open Scope nat_scope.
Local Notation "a && b" := (andb a b).


(** ** Linear expressions *)

Record Lin := mkLin { lc : nat; la : list nat }.

Fixpoint dot (a x : list nat) : nat :=
  match a, x with
  | a :: as_, y :: xs => a * y + dot as_ xs
  | _, _ => 0
  end.

Definition eval (e : Lin) (x : list nat) : nat := lc e + dot (la e) x.

Fixpoint addL (a b : list nat) : list nat :=
  match a, b with
  | a :: as_, b :: bs => (a + b) :: addL as_ bs
  | [], bs => bs
  | as_, [] => as_
  end.

Lemma dot_addL : forall a b x, dot (addL a b) x = dot a x + dot b x.
Proof.
  induction a as [| a as_ IH]; intros [| b bs] [| y ys]; simpl; try lia.
  rewrite IH. lia.
Qed.

Definition ladd (e f : Lin) : Lin := mkLin (lc e + lc f) (addL (la e) (la f)).
Lemma eval_ladd : forall e f x, eval (ladd e f) x = eval e x + eval f x.
Proof. intros. unfold eval, ladd. simpl. rewrite dot_addL. lia. Qed.

Definition lconst (n : nat) : Lin := mkLin n [].
Lemma eval_lconst : forall n x, eval (lconst n) x = n.
Proof. intros. unfold eval. simpl. lia. Qed.

Definition lpred (e : Lin) : Lin := mkLin (lc e - 1) (la e).
Lemma eval_lpred : forall e x, 1 <= lc e -> eval e x = S (eval (lpred e) x).
Proof. intros. unfold eval, lpred. simpl. lia. Qed.

Definition allz (a : list nat) : bool := forallb (Nat.eqb 0) a.
Lemma dot_allz : forall a x, allz a = true -> dot a x = 0.
Proof.
  induction a as [| a as_ IH]; intros [| y ys] H; simpl in *; try lia.
  apply andb_true_iff in H as [H1 H2]. destruct a; [| discriminate]. rewrite IH; auto.
Qed.

Definition lzero (e : Lin) : bool := Nat.eqb (lc e) 0 && allz (la e).
Lemma eval_lzero : forall e x, lzero e = true -> eval e x = 0.
Proof.
  intros e x H. unfold lzero in H. apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. unfold eval. rewrite H1, dot_allz; auto.
Qed.

Fixpoint trimZ (a : list nat) : list nat :=
  match a with
  | [] => []
  | b :: bs => match b, trimZ bs with
               | 0, [] => []
               | _, r => b :: r
               end
  end.
Lemma dot_trimZ : forall a x, dot (trimZ a) x = dot a x.
Proof.
  induction a as [| b bs IH]; intros x; simpl; auto.
  destruct x as [| y ys].
  - destruct b; destruct (trimZ bs); reflexivity.
  - specialize (IH ys). destruct b, (trimZ bs) eqn:E; simpl in *; lia.
Qed.
Definition ltrim (e : Lin) : Lin := mkLin (lc e) (trimZ (la e)).
Lemma eval_ltrim : forall e x, eval (ltrim e) x = eval e x.
Proof. intros. unfold eval, ltrim. simpl. rewrite dot_trimZ. reflexivity. Qed.

Fixpoint divAll (m : nat) (a : list nat) : option (list nat) :=
  match a with
  | [] => Some []
  | b :: bs => if Nat.eqb (b mod m) 0 then
                 match divAll m bs with Some r => Some (b / m :: r) | None => None end
               else None
  end.
Lemma dot_divAll : forall m a q x, m <> 0 -> divAll m a = Some q -> dot a x = m * dot q x.
Proof.
  induction a as [| b bs IH]; intros q x Hm H; simpl in H.
  - inversion H. subst. destruct x; simpl; lia.
  - destruct (Nat.eqb (b mod m) 0) eqn:E; [| discriminate].
    destruct (divAll m bs) as [r |] eqn:E2; [| discriminate].
    inversion H. subst. apply Nat.eqb_eq in E.
    destruct x as [| y ys]; simpl; [lia |].
    rewrite (IH r ys Hm eq_refl).
    rewrite (Nat.div_mod b m Hm) at 1. rewrite E. lia.
Qed.

Definition ldivm (m : nat) (e : Lin) : option (Lin * nat) :=
  if Nat.eqb m 0 then None else
  match divAll m (la e) with
  | Some q => Some (mkLin (lc e / m) q, lc e mod m)
  | None => None
  end.
Lemma eval_ldivm : forall m e q r x, ldivm m e = Some (q, r) -> eval e x = m * eval q x + r.
Proof.
  intros m e q r x H. unfold ldivm in H. destruct (Nat.eqb m 0) eqn:Em; [discriminate |].
  apply Nat.eqb_neq in Em.
  destruct (divAll m (la e)) as [a |] eqn:E; [| discriminate].
  inversion H. subst. unfold eval. cbn [lc la].
  rewrite (dot_divAll m (la e) a x Em E).
  pose proof (Nat.div_mod (lc e) m Em). rewrite Nat.mul_add_distr_l. lia.
Qed.

Fixpoint substL (a : list nat) (s : list Lin) : Lin :=
  match a, s with
  | b :: bs, e :: es => ladd (mkLin (b * lc e) (List.map (Nat.mul b) (la e))) (substL bs es)
  | _, _ => lconst 0
  end.
Definition lsubst (e : Lin) (s : list Lin) : Lin := ladd (lconst (lc e)) (substL (la e) s).

Lemma dot_map_mul : forall b a x, dot (List.map (Nat.mul b) a) x = b * dot a x.
Proof. induction a as [| c cs IH]; intros [| y ys]; simpl; try lia. rewrite IH. lia. Qed.

Lemma eval_substL : forall a s x, eval (substL a s) x = dot a (List.map (fun e => eval e x) s).
Proof.
  induction a as [| b bs IH]; intros [| e es] x; simpl; try (rewrite eval_lconst; reflexivity).
  rewrite eval_ladd, IH. unfold eval at 1. simpl. rewrite dot_map_mul. unfold eval. lia.
Qed.
Lemma eval_lsubst : forall e s x, eval (lsubst e s) x = eval e (List.map (fun e => eval e x) s).
Proof. intros. unfold lsubst. rewrite eval_ladd, eval_lconst, eval_substL. reflexivity. Qed.

Fixpoint list_eqb {A} (eqb : A -> A -> bool) (a b : list A) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && list_eqb eqb xs ys
  | _, _ => false
  end.

Definition lin_eqb (e f : Lin) : bool := Nat.eqb (lc e) (lc f) && list_eqb Nat.eqb (la e) (la f).

(** ** Symbols, words, tokens *)

Definition sym_eqb (a b : sym) : bool :=
  match a, b with S0, S0 | S1, S1 => true | _, _ => false end.
Lemma sym_eqb_eq : forall a b, sym_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

Fixpoint w_eqb (u v : list sym) : bool :=
  match u, v with
  | [], [] => true
  | a :: u, b :: v => sym_eqb a b && w_eqb u v
  | _, _ => false
  end.
Lemma w_eqb_eq : forall u v, w_eqb u v = true <-> u = v.
Proof.
  induction u as [| a u IH]; intros [| b v]; simpl; try (split; congruence).
  rewrite andb_true_iff, sym_eqb_eq, IH. split; [intros [-> ->]; auto | intros H; inversion H; auto].
Qed.

Inductive Tok := TB (s : sym) | TR (w : list sym) (n : Lin).

Definition tok_eqb (a b : Tok) : bool :=
  match a, b with
  | TB s, TB s' => sym_eqb s s'
  | TR w n, TR w' n' => w_eqb w w' && lin_eqb n n'
  | _, _ => false
  end.
Fixpoint toks_eqb (u v : list Tok) : bool :=
  match u, v with
  | [], [] => true
  | a :: u, b :: v => tok_eqb a b && toks_eqb u v
  | _, _ => false
  end.

Lemma list_eqb_nat : forall a b, list_eqb Nat.eqb a b = true -> a = b.
Proof.
  induction a as [| x a IH]; intros [| y b] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. subst. f_equal. auto.
Qed.
Lemma toks_eqb_eq : forall u v, toks_eqb u v = true -> u = v.
Proof.
  induction u as [| a u IH]; intros [| b v] H; simpl in H; try discriminate; auto.
  apply andb_true_iff in H as [H1 H2]. f_equal; auto.
  destruct a, b; simpl in H1; try discriminate.
  - apply sym_eqb_eq in H1. congruence.
  - apply andb_true_iff in H1 as [H1 H3]. apply w_eqb_eq in H1. subst.
    unfold lin_eqb in H3. apply andb_true_iff in H3 as [H3 H4].
    apply Nat.eqb_eq in H3. apply list_eqb_nat in H4. destruct n, n0; simpl in *. congruence.
Qed.

Notation blank := (const S0).

(** The stream of a token list in front of [t]; on the left of the head, everything is written nearest cell
    first. *)
Fixpoint den (x : list nat) (ts : list Tok) (t : Stream sym) : Stream sym :=
  match ts with
  | [] => t
  | TB v :: ts => v >> den x ts t
  | TR w n :: ts => w ^^ (eval n x) *> den x ts t
  end.

Lemma den_app : forall x s ts t, den x (s ++ ts) t = den x s (den x ts t).
Proof. induction s as [| [] s IH]; intros; simpl; try rewrite IH; reflexivity. Qed.

Lemma den_lits : forall x w t, den x (List.map TB w) t = w *> t.
Proof. induction w as [| a w IH]; intros; simpl; try rewrite IH; reflexivity. Qed.

Lemma lpow_nil : forall n (t : Stream sym), ([] : list sym) ^^ n *> t = t.
Proof. induction n; simpl; auto. Qed.

Lemma lpow_succ_r : forall n (w : list sym) t, w ^^ S n *> t = w ^^ n *> w *> t.
Proof. intros. simpl. rewrite Str_app_assoc. rewrite <- Str_app_assoc, <- lpow_shift, Str_app_assoc. reflexivity. Qed.

Lemma lpow_plus : forall n m (w : list sym) t, w ^^ (n + m) *> t = w ^^ n *> w ^^ m *> t.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma lpow_mul : forall q m (w : list sym) t, (w ^^ m) ^^ q *> t = w ^^ (m * q) *> t.
Proof.
  induction q as [| q IH]; intros; simpl.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Str_app_assoc, IH, <- lpow_plus. f_equal. f_equal. lia.
Qed.

(** A configuration: tokens left of the head (nearest first), tokens from the head on, the state. *)
Record MC := mkMC { ml : list Tok; mr : list Tok; mst : state }.

Definition cden (x : list nat) (c : MC) : Q * tape :=
  den x (ml c) blank {{mst c}}> den x (mr c) blank.

(** ** Reading the first cell *)

Fixpoint pop (ts : list Tok) : option (sym * list Tok) :=
  match ts with
  | [] => Some (S0, [])
  | TB v :: ts => Some (v, ts)
  | TR w n :: ts =>
    match w with
    | [] => pop ts
    | a :: w' =>
      match lc n with
      | S k => Some (a, List.map TB w' ++ TR (a :: w') (mkLin k (la n)) :: ts)
      | 0 => if allz (la n) then pop ts else None
      end
    end
  end.

Lemma pop_den : forall x ts v rest, pop ts = Some (v, rest) -> den x ts blank = v >> den x rest blank.
Proof.
  intros x ts. induction ts as [| [u | w n] ts IH]; intros v rest H; cbn [pop] in H.
  - inversion H. subst. simpl. apply const_unfold.
  - inversion H. subst. reflexivity.
  - destruct w as [| a w'].
    + simpl. rewrite lpow_nil. eauto.
    + destruct n as [c la0]. cbn [lc la] in H. destruct c as [| k].
      * destruct (allz la0) eqn:Z; [| discriminate].
        simpl. unfold eval. simpl. rewrite (dot_allz la0 x Z). simpl. eauto.
      * inversion H. subst. simpl. unfold eval. simpl.
        rewrite den_app, den_lits. simpl. unfold eval. simpl.
        rewrite Str_app_assoc. reflexivity.
Qed.
Arguments pop : simpl never.

Section Machine.
Variable tm : TM.

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma step_r : forall Lt v Rt w q s, tm (q, v) = Some (w, R, s) ->
  Lt {{q}}> v >> Rt --> (w >> Lt) {{s}}> Rt.
Proof. intros Lt v Rt w q s H. exact (step_right (l := Lt) (r := Rt) H). Qed.

Lemma step_l : forall y Lt v Rt w q s, tm (q, v) = Some (w, TM.L, s) ->
  (y >> Lt) {{q}}> v >> Rt --> Lt {{s}}> y >> w >> Rt.
Proof. intros y Lt v Rt w q s H. exact (step_left (l := y >> Lt) (r := Rt) H). Qed.

(** One machine step. *)
Definition mstep (c : MC) : option MC :=
  match pop (mr c) with
  | None => None
  | Some (v, rt) =>
    match tm (mst c, v) with
    | None => None
    | Some (w, R, s) => Some (mkMC (TB w :: ml c) rt s)
    | Some (w, TM.L, s) =>
      match pop (ml c) with
      | None => None
      | Some (y, lt) => Some (mkMC lt (TB y :: TB w :: rt) s)
      end
    end
  end.

Lemma mstep_sound : forall x c c', mstep c = Some c' -> cden x c --> cden x c'.
Proof.
  intros x [l r q] c' H. unfold mstep in H. cbn [ml mr mst] in H.
  destruct (pop r) as [[v rt] |] eqn:Hr; [| discriminate].
  pose proof (pop_den x r v rt Hr) as Er.
  destruct (tm (q, v)) as [[[w d] s] |] eqn:Hd; [| discriminate].
  destruct d.
  - destruct (pop l) as [[y lt] |] eqn:Hl; [| discriminate].
    pose proof (pop_den x l y lt Hl) as El.
    injection H as <-. unfold cden. cbn [ml mr mst]. rewrite Er, El. cbn [den]. exact (step_l y (den x lt blank) v (den x rt blank) w q s Hd).
  - injection H as <-. unfold cden. cbn [ml mr mst]. rewrite Er. exact (step_r (den x l blank) v (den x rt blank) w q s Hd).
Qed.

(** ** The window simulator *)

Definition wden (l r : list sym) (q : state) (Lt Rt : Stream sym) : Q * tape := (l *> Lt) {{q}}> (r *> Rt).

Definition wstep (c : list sym * list sym * state) : option (list sym * list sym * state) :=
  match c with
  | (l, [], q) => None
  | (l, v :: rt, q) =>
    match tm (q, v) with
    | None => None
    | Some (w, R, s) => Some (w :: l, rt, s)
    | Some (w, TM.L, s) =>
      match l with
      | [] => None
      | y :: lt => Some (lt, y :: w :: rt, s)
      end
    end
  end.

Fixpoint wsteps (n : nat) (c : list sym * list sym * state) : option (list sym * list sym * state) :=
  match n with
  | 0 => Some c
  | S n => match wstep c with None => None | Some c' => wsteps n c' end
  end.

Lemma wstep_sound : forall l r q l' r' q' Lt Rt, wstep (l, r, q) = Some (l', r', q') ->
  wden l r q Lt Rt --> wden l' r' q' Lt Rt.
Proof.
  intros l r q l' r' q' Lt Rt H. destruct r as [| v rt]; [discriminate |]. simpl in H.
  destruct (tm (q, v)) as [[[w d] s] |] eqn:Hd; [| discriminate].
  destruct d.
  - destruct l as [| y lt]; [discriminate |]. inversion H. subst.
    unfold wden. simpl. apply step_l. assumption.
  - inversion H. subst. unfold wden. simpl. apply step_r. assumption.
Qed.

Lemma wsteps_sound : forall n l r q l' r' q' Lt Rt, wsteps n (l, r, q) = Some (l', r', q') ->
  wden l r q Lt Rt -->* wden l' r' q' Lt Rt.
Proof.
  induction n as [| n IH]; intros l r q l' r' q' Lt Rt H; cbn [wsteps] in H.
  - inversion H. subst. apply evstep_refl.
  - destruct (wstep (l, r, q)) as [[[l2 r2] q2] |] eqn:E; [| discriminate].
    eapply evstep_step; [apply (wstep_sound _ _ _ _ _ _ _ _ E) | eauto].
Qed.

(** ** Crossing a run *)

Fixpoint lits (k : nat) (ts : list Tok) : option (list sym * list Tok) :=
  match k, ts with
  | 0, ts => Some ([], ts)
  | S k, TB v :: ts => match lits k ts with Some (u, r) => Some (v :: u, r) | None => None end
  | _, _ => None
  end.

Lemma lits_eq : forall k ts u rest, lits k ts = Some (u, rest) -> ts = List.map TB u ++ rest.
Proof.
  induction k as [| k IH]; intros ts u rest H; simpl in H.
  - inversion H. reflexivity.
  - destruct ts as [| [v | w n] ts]; try discriminate.
    destruct (lits k ts) as [[u' r'] |] eqn:E; [| discriminate].
    inversion H. subst. simpl. f_equal. eauto.
Qed.

Lemma cross_r : forall u w w' q,
  (forall Lt Rt, (u *> Lt) {{q}}> (w *> Rt) -->* (u *> w' *> Lt) {{q}}> Rt) ->
  forall n Lt Rt, (u *> Lt) {{q}}> (w ^^ n *> Rt) -->* (u *> w' ^^ n *> Lt) {{q}}> Rt.
Proof.
  intros u w w' q H. induction n as [| n IH]; intros Lt Rt.
  - apply evstep_refl.
  - rewrite (lpow_succ_r n w'). rewrite (lpow_S n w), Str_app_assoc.
    eapply evstep_trans; [apply H |]. apply IH.
Qed.

Lemma cross_l : forall u w w' q,
  (forall Lt Rt, (w *> Lt) {{q}}> (u *> Rt) -->* Lt {{q}}> (u *> w' *> Rt)) ->
  forall n Lt Rt, (w ^^ n *> Lt) {{q}}> (u *> Rt) -->* Lt {{q}}> (u *> w' ^^ n *> Rt).
Proof.
  intros u w w' q H. induction n as [| n IH]; intros Lt Rt.
  - apply evstep_refl.
  - rewrite (lpow_succ_r n w'). rewrite (lpow_S n w), Str_app_assoc.
    eapply evstep_trans; [apply H |]. apply IH.
Qed.

Definition st_eqb (a b : state) : bool :=
  match a, b with A, A | B, B | C, C | D, D | E, E | F, F => true | _, _ => false end.
Lemma st_eqb_eq : forall a b, st_eqb a b = true -> a = b.
Proof. intros [] []; simpl; congruence. Qed.
Arguments st_eqb : simpl never.
Arguments wsteps : simpl never.
Arguments lits : simpl never.

Definition crossR (k s : nat) (c : MC) : option MC :=
  match mr c with
  | TR w n :: rest =>
    match lits k (ml c) with
    | None => None
    | Some (u, lrest) =>
      match wsteps s (u, w, mst c) with
      | None => None
      | Some (el, er, est) =>
        match er with
        | [] => if st_eqb est (mst c) && w_eqb (firstn (length u) el) u
                then Some (mkMC (List.map TB u ++ TR (skipn (length u) el) n :: lrest) rest (mst c))
                else None
        | _ => None
        end
      end
    end
  | _ => None
  end.


Lemma firstn_skipn_eq : forall (u l : list sym), firstn (length u) l = u -> l = u ++ skipn (length u) l.
Proof. intros u l H. rewrite <- (firstn_skipn (length u) l) at 1. rewrite H. reflexivity. Qed.

Lemma crossR_sound : forall k s x c c', crossR k s c = Some c' -> cden x c -->* cden x c'.
Proof.
  intros k s x [l r q] c' H. unfold crossR in H. cbn [ml mr mst] in H.
  destruct r as [| [v | w n] rest]; try discriminate.
  destruct (lits k l) as [[u lrest] |] eqn:Hl; [| discriminate].
  destruct (wsteps s (u, w, q)) as [[[el er] est] |] eqn:Hw; [| discriminate].
  destruct er; [| discriminate].
  destruct (st_eqb est q
            && w_eqb (firstn (length u) el) u) eqn:Hc; [| discriminate].
  apply andb_true_iff in Hc as [Hq Hu]. apply (st_eqb_eq est q) in Hq. apply w_eqb_eq in Hu. subst est.
  inversion H. subst. clear H.
  pose proof (firstn_skipn_eq u el Hu) as Eel.
  assert (Hcr : forall Lt Rt, (u *> Lt) {{q}}> (w *> Rt) -->* (u *> skipn (length u) el *> Lt) {{q}}> Rt).
  { intros Lt Rt. pose proof (wsteps_sound s u w q el [] q Lt Rt Hw) as W. unfold wden in W.
    rewrite Eel in W. rewrite Str_app_assoc in W. exact W. }
  unfold cden. simpl. rewrite (lits_eq k l u lrest Hl), den_app, den_lits, den_app, den_lits. simpl.
  apply cross_r. exact Hcr.
Qed.

Definition crossL (k s : nat) (c : MC) : option MC :=
  match ml c with
  | TR w n :: lrest =>
    match lits k (mr c) with
    | None => None
    | Some (u, rest) =>
      match wsteps s (w, u, mst c) with
      | None => None
      | Some (el, er, est) =>
        match el with
        | [] => if st_eqb est (mst c) && w_eqb (firstn (length u) er) u
                then Some (mkMC lrest (List.map TB u ++ TR (skipn (length u) er) n :: rest) (mst c))
                else None
        | _ => None
        end
      end
    end
  | _ => None
  end.

Lemma crossL_sound : forall k s x c c', crossL k s c = Some c' -> cden x c -->* cden x c'.
Proof.
  intros k s x [l r q] c' H. unfold crossL in H. cbn [ml mr mst] in H.
  destruct l as [| [v | w n] lrest]; try discriminate.
  destruct (lits k r) as [[u rest] |] eqn:Hl; [| discriminate].
  destruct (wsteps s (w, u, q)) as [[[el er] est] |] eqn:Hw; [| discriminate].
  destruct el; [| discriminate].
  destruct (st_eqb est q && w_eqb (firstn (length u) er) u) eqn:Hc; [| discriminate].
  apply andb_true_iff in Hc as [Hq Hu]. apply st_eqb_eq in Hq. apply w_eqb_eq in Hu. subst est.
  inversion H. subst. clear H.
  pose proof (firstn_skipn_eq u er Hu) as Eer.
  assert (Hcl : forall Lt Rt, (w *> Lt) {{q}}> (u *> Rt) -->* Lt {{q}}> (u *> skipn (length u) er *> Rt)).
  { intros Lt Rt. pose proof (wsteps_sound s w u q [] er q Lt Rt Hw) as W. unfold wden in W.
    rewrite Eer in W. rewrite Str_app_assoc in W. exact W. }
  unfold cden. simpl. rewrite (lits_eq k r u rest Hl), den_app, den_lits, den_app, den_lits. simpl.
  apply cross_l. exact Hcl.
Qed.

End Machine.
Arguments st_eqb : simpl never.
Arguments wsteps : simpl never.
Arguments lits : simpl never.

(** ** Re-bracketing *)

Lemma rep_rotate : forall (xw y y' : list sym) n t, xw ++ y = y' ++ xw ->
  xw *> y ^^ n *> t = y' ^^ n *> xw *> t.
Proof.
  intros xw y y' n t H. induction n as [| n IH]; simpl; [reflexivity |].
  rewrite !Str_app_assoc, <- (Str_app_assoc xw y), H, Str_app_assoc, IH. reflexivity.
Qed.

Definition rot (k : nat) (ts : list Tok) : option (list Tok) :=
  match lits k ts with
  | None => None
  | Some (xw, TR y n :: rest') =>
    if w_eqb (skipn (length y) (xw ++ y)) xw
    then Some (TR (firstn (length y) (xw ++ y)) n :: List.map TB xw ++ rest') else None
  | Some _ => None
  end.

Lemma rot_den : forall k x ts ts' t, rot k ts = Some ts' -> den x ts t = den x ts' t.
Proof.
  intros k x ts ts' t H. unfold rot in H.
  destruct (lits k ts) as [[xw rest] |] eqn:Hl; [| discriminate].
  destruct rest as [| [v | y n] rest']; try discriminate.
  destruct (w_eqb (skipn (length y) (xw ++ y)) xw) eqn:E; [| discriminate].
  apply w_eqb_eq in E. inversion H. subst. clear H.
  rewrite (lits_eq k ts xw _ Hl), den_app, den_lits. simpl. rewrite den_app, den_lits.
  apply rep_rotate. pose proof (firstn_skipn (length y) (xw ++ y)) as F. rewrite E in F. symmetry. exact F.
Qed.

(** The other way round: literal cells behind a run that repeat the start of its word, moved in front of it
    ([y^n x = x y'^n] when [y x = x y']), so that the cell next to the head is known even when the run may be
    empty. *)
Definition rotB (k : nat) (ts : list Tok) : option (list Tok) :=
  match ts with
  | TR y n :: rest =>
    match lits k rest with
    | Some (xw, rest') =>
      if w_eqb (firstn (length xw) (y ++ xw)) xw
      then Some (List.map TB xw ++ TR (skipn (length xw) (y ++ xw)) n :: rest') else None
    | None => None
    end
  | _ => None
  end.

Lemma rotB_den : forall k x ts ts' t, rotB k ts = Some ts' -> den x ts t = den x ts' t.
Proof.
  intros k x ts ts' t H. destruct ts as [| [v | y n] rest]; try discriminate. unfold rotB in H.
  destruct (lits k rest) as [[xw rest'] |] eqn:Hl; [| discriminate].
  destruct (w_eqb (firstn (length xw) (y ++ xw)) xw) eqn:E; [| discriminate].
  apply w_eqb_eq in E. inversion H. subst. clear H.
  rewrite (lits_eq k rest xw rest' Hl). cbn [den]. rewrite den_app, den_lits, den_app, den_lits. cbn [den].
  symmetry. apply rep_rotate.
  pose proof (firstn_skipn (length xw) (y ++ xw)) as F. rewrite E in F. exact F.
Qed.

Fixpoint rotBs (k : nat) (ts : list Tok) : option (list Tok) :=
  match k with
  | 0 => None
  | S k => match rotBs k ts with Some r => Some r | None => rotB (S k) ts end
  end.
Lemma rotBs_den : forall k x ts ts' t, rotBs k ts = Some ts' -> den x ts t = den x ts' t.
Proof.
  induction k as [| k IH]; intros x ts ts' t H; [discriminate |]. cbn [rotBs] in H.
  destruct (rotBs k ts) as [r |] eqn:E.
  - inversion H. subst. eauto.
  - eapply rotB_den. exact H.
Qed.

Definition grp (m : nat) (ts : list Tok) : option (list Tok) :=
  match ts with
  | TR w n :: rest =>
    match ldivm m n with
    | Some (q, r) => Some (TR (w ^^ m) q :: (if Nat.eqb r 0 then rest else TR w (lconst r) :: rest))
    | None => None
    end
  | _ => None
  end.

Lemma grp_den : forall m x ts ts' t, grp m ts = Some ts' -> den x ts t = den x ts' t.
Proof.
  intros m x ts ts' t H. destruct ts as [| [v | w n] rest]; try discriminate. simpl in H.
  destruct (ldivm m n) as [[q r] |] eqn:E; [| discriminate]. inversion H. subst. clear H.
  simpl. rewrite (eval_ldivm m n q r x E), lpow_mul, lpow_plus.
  destruct (Nat.eqb r 0) eqn:R0.
  - apply Nat.eqb_eq in R0. subst. reflexivity.
  - simpl. rewrite eval_lconst. reflexivity.
Qed.

Definition absorb (ts : list Tok) : option (list Tok) :=
  match ts with
  | TR w n :: rest =>
    match lits (length w) rest with
    | Some (u, rest') => if w_eqb u w then Some (TR w (ladd n (lconst 1)) :: rest') else None
    | None => None
    end
  | _ => None
  end.

Lemma absorb_den : forall x ts ts' t, absorb ts = Some ts' -> den x ts t = den x ts' t.
Proof.
  intros x ts ts' t H. destruct ts as [| [v | w n] rest]; try discriminate. simpl in H.
  destruct (lits (length w) rest) as [[u rest'] |] eqn:E; [| discriminate].
  destruct (w_eqb u w) eqn:U; [| discriminate]. apply w_eqb_eq in U. subst.
  inversion H. subst. clear H.
  rewrite (lits_eq _ rest w rest' E). simpl. rewrite den_app, den_lits, eval_ladd, eval_lconst.
  rewrite Nat.add_1_r, lpow_succ_r. reflexivity.
Qed.

(** ** Normal forms *)

(** One token, expanded: empty runs dropped, constant runs written out. *)
Definition expandTok (tk : Tok) : list Tok :=
  match tk with
  | TB v => [TB v]
  | TR w n =>
    if lzero n then []
    else match w with
         | [] => []
         | _ => if allz (la n) then List.map TB (w ^^ lc n) else [TR w n]
         end
  end.

Lemma expandTok_den : forall x tk t, den x (expandTok tk) t = den x [tk] t.
Proof.
  intros x [v | w n] t; [reflexivity |]. simpl.
  destruct (lzero n) eqn:Z.
  - rewrite (eval_lzero n x Z). reflexivity.
  - destruct w as [| a w'].
    + simpl. rewrite lpow_nil. reflexivity.
    + destruct (allz (la n)) eqn:Az.
      * rewrite den_lits. unfold eval. rewrite (dot_allz _ x Az), Nat.add_0_r. reflexivity.
      * reflexivity.
Qed.

Fixpoint expand (ts : list Tok) : list Tok :=
  match ts with
  | [] => []
  | tk :: ts => expandTok tk ++ expand ts
  end.

Lemma den_cons : forall x tk ts t, den x (tk :: ts) t = den x [tk] (den x ts t).
Proof. intros x [] ts t; reflexivity. Qed.

Lemma expand_den : forall x ts t, den x (expand ts) t = den x ts t.
Proof.
  induction ts as [| tk ts IH]; intros t; [reflexivity |].
  simpl expand. rewrite den_app, IH, expandTok_den, <- den_cons. reflexivity.
Qed.

(** Trailing blank cells dropped. *)
Fixpoint dropTF (ts : list Tok) : list Tok :=
  match ts with
  | [] => []
  | tk :: ts =>
    match tk, dropTF ts with
    | TB S0, [] => []
    | tk, r => tk :: r
    end
  end.

Lemma dropTF_den : forall x ts, den x (dropTF ts) blank = den x ts blank.
Proof.
  induction ts as [| tk ts IH]; [reflexivity |]. simpl.
  destruct tk as [[] | w n]; destruct (dropTF ts) eqn:E; simpl in *; rewrite <- IH; try reflexivity.
  apply const_unfold.
Qed.

Definition trimTok (tk : Tok) : Tok := match tk with TR w n => TR w (ltrim n) | _ => tk end.
Lemma trim_den : forall x ts t, den x (List.map trimTok ts) t = den x ts t.
Proof. induction ts as [| [] ts IH]; intros; simpl; rewrite ?IH, ?eval_ltrim; reflexivity. Qed.

(** The normal form of the 2-symbol runs used by the first machine: runs of [0 1] merged, pairs [0 1] absorbed
    (as in the Lean checker of that machine). *)
Definition is01 (w : list sym) : bool := match w with [S0; S1] => true | _ => false end.

Fixpoint isPairs (w : list sym) : option nat :=
  match w with
  | [] => Some 0
  | S0 :: S1 :: w => match isPairs w with Some m => Some (S m) | None => None end
  | _ => None
  end.
Lemma isPairs_eq : forall w m, isPairs w = Some m -> w = [S0; S1] ^^ m.
Proof.
  fix IH 1. intros w m H. destruct w as [| [] w]; simpl in H.
  - inversion H. reflexivity.
  - destruct w as [| [] w]; try discriminate.
    destruct (isPairs w) as [m' |] eqn:E; [| discriminate]. inversion H. subst.
    rewrite (IH w m' E). reflexivity.
  - discriminate.
Qed.

Definition lscale (m : nat) (e : Lin) : Lin := mkLin (m * lc e) (List.map (Nat.mul m) (la e)).
Lemma eval_lscale : forall m e x, eval (lscale m e) x = m * eval e x.
Proof. intros. unfold eval, lscale. simpl. rewrite dot_map_mul. lia. Qed.

Definition expandTok01 (tk : Tok) : list Tok :=
  match tk with
  | TB v => [TB v]
  | TR w n =>
    if lzero n then []
    else match isPairs w with
         | Some m => [TR [S0; S1] (lscale m n)]
         | None => if allz (la n) then List.map TB (w ^^ lc n) else [TR w n]
         end
  end.

Lemma expandTok01_den : forall x tk t, den x (expandTok01 tk) t = den x [tk] t.
Proof.
  intros x [v | w n] t; [reflexivity |]. simpl.
  destruct (lzero n) eqn:Z; [rewrite (eval_lzero n x Z); reflexivity |].
  destruct (isPairs w) as [m |] eqn:P.
  - simpl. rewrite eval_lscale, (isPairs_eq w m P), lpow_mul. reflexivity.
  - destruct (allz (la n)) eqn:Az; [| reflexivity].
    rewrite den_lits. unfold eval. rewrite (dot_allz _ x Az), Nat.add_0_r. reflexivity.
Qed.

Fixpoint expand01 (ts : list Tok) : list Tok :=
  match ts with [] => [] | tk :: ts => expandTok01 tk ++ expand01 ts end.
Lemma expand01_den : forall x ts t, den x (expand01 ts) t = den x ts t.
Proof.
  induction ts as [| tk ts IH]; intros t; [reflexivity |].
  simpl expand01. rewrite den_app, IH, expandTok01_den, <- den_cons. reflexivity.
Qed.

Fixpoint push01 (f : nat) (tk : Tok) (ts : list Tok) : list Tok :=
  match f with
  | 0 => tk :: ts
  | S f =>
    match tk, ts with
    | TR [S0; S1] n, TR [S0; S1] m :: rest => TR [S0; S1] (ladd n m) :: rest
    | TB S0, TB S1 :: rest => push01 f (TR [S0; S1] (lconst 1)) rest
    | tk, rest => tk :: rest
    end
  end.

Lemma push01_den : forall x t f tk ts, den x (push01 f tk ts) t = den x (tk :: ts) t.
Proof.
  intros x t f. induction f as [| f IH]; intros tk ts; [reflexivity |].
  cbn [push01].
  destruct tk as [v | w n]; destruct ts as [| [v' | w' m] rest];
  repeat match goal with |- context [match ?e with _ => _ end] => is_var e; destruct e end;
  first [ reflexivity | rewrite IH; reflexivity | simpl; rewrite eval_ladd, lpow_plus; reflexivity ].
Qed.

Fixpoint merge01 (ts : list Tok) : list Tok :=
  match ts with [] => [] | tk :: ts => push01 (S (S (length ts))) tk (merge01 ts) end.
Lemma merge01_den : forall x ts t, den x (merge01 ts) t = den x ts t.
Proof.
  induction ts as [| tk ts IH]; intros t; [reflexivity |].
  change (merge01 (tk :: ts)) with (push01 (S (S (length ts))) tk (merge01 ts)).
  rewrite push01_den, den_cons, IH, <- den_cons. reflexivity.
Qed.

Definition norm01 (ts : list Tok) : list Tok := List.map trimTok (merge01 (dropTF (expand01 ts))).
Lemma norm01_den : forall x ts, den x (norm01 ts) blank = den x ts blank.
Proof. intros. unfold norm01. rewrite trim_den, merge01_den, dropTF_den, expand01_den. reflexivity. Qed.

(** A general normal form: literal cells moved to the right through runs ([v (y v)^n = (v y)^n v]), runs of the
    same word merged, copies of a run's word written out behind it absorbed. *)
Fixpoint lastS (w : list sym) : option sym :=
  match w with [] => None | [a] => Some a | _ :: w => lastS w end.

Lemma lastS_app : forall w a, lastS w = Some a -> w = removelast w ++ [a].
Proof.
  induction w as [| b w IH]; intros a H; [discriminate |].
  destruct w as [| c w]; simpl in *.
  - inversion H. reflexivity.
  - rewrite (IH a H) at 1. reflexivity.
Qed.

Fixpoint litsRun (ts : list Tok) : option (list sym * list sym * Lin * list Tok) :=
  match ts with
  | TB v :: ts => match litsRun ts with Some (u, w, n, r) => Some (v :: u, w, n, r) | None => None end
  | TR w n :: r => Some ([], w, n, r)
  | [] => None
  end.
Lemma litsRun_eq : forall ts u w n r, litsRun ts = Some (u, w, n, r) -> ts = List.map TB u ++ TR w n :: r.
Proof.
  induction ts as [| [v | w0 n0] ts IH]; intros u w n r H; cbn [litsRun] in H; try discriminate.
  - destruct (litsRun ts) as [[[[u' w'] n'] r'] |] eqn:E; [| discriminate].
    inversion H. subst. cbn. rewrite (IH u' w n r eq_refl). reflexivity.
  - inversion H. subst. reflexivity.
Qed.

Ltac ab2_tac W := match goal with
  | |- context [litsRun ?ts] =>
    let u := fresh "u" in let w2 := fresh "w2" in let mc := fresh "mc" in let ma := fresh "ma" in
    let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in let k := fresh "k" in
    destruct (litsRun ts) as [[[[u w2] [mc ma]] r] |] eqn:Hr; [| reflexivity];
    cbv beta iota; cbn [lc la]; destruct mc as [| k]; [reflexivity |];
    destruct (w_eqb (u ++ w2) W) eqn:Hw; [| reflexivity];
    apply w_eqb_eq in Hw; match goal with IH : forall tk ts, _ |- _ => rewrite IH end;
    rewrite (litsRun_eq _ _ _ _ _ Hr); cbn [den]; rewrite den_app, den_lits; cbn [den];
    rewrite eval_ladd, eval_lconst, Nat.add_1_r, lpow_succ_r;
    match goal with |- context [eval (mkLin (S k) ma) ?x] =>
      change (eval (mkLin (S k) ma) x) with (S (eval (mkLin k ma) x)) end;
    rewrite lpow_S, !Str_app_assoc, <- Hw, Str_app_assoc; reflexivity
  end.

Fixpoint pushG (f : nat) (tk : Tok) (ts : list Tok) : list Tok :=
  match f with
  | 0 => tk :: ts
  | S f =>
    match tk with
    | TR w n =>
      let ab2 := match litsRun ts with
                 | Some (u, w2, m, r) =>
                   match lc m with
                   | S k => if w_eqb (u ++ w2) w
                            then pushG f (TR w (ladd n (lconst 1))) (TR w2 (mkLin k (la m)) :: r)
                            else tk :: ts
                   | 0 => tk :: ts
                   end
                 | None => tk :: ts
                 end in
      let dflt := match w, lits (length w) ts with
                  | _ :: _, Some (u, rest') => if w_eqb u w then pushG f (TR w (ladd n (lconst 1))) rest' else ab2
                  | _, _ => ab2
                  end in
      match ts with
      | TR w' m :: rest => if w_eqb w w' then TR w (ladd n m) :: rest else dflt
      | _ => dflt
      end
    | TB v =>
      match ts with
      | TR w n :: rest =>
        match lastS w with
        | Some a => if sym_eqb a v then pushG f (TR (v :: removelast w) n) (pushG f (TB v) rest) else tk :: ts
        | None => tk :: ts
        end
      | _ => tk :: ts
      end
    end
  end.

Ltac absorbG_tac := match goal with
  | Hu : w_eqb ?u ?w = true, Hl : lits _ _ = Some (?u, _) |- _ =>
    apply w_eqb_eq in Hu; subst u; match goal with IH : forall tk ts, _ |- _ => rewrite IH end;
    rewrite (lits_eq _ _ _ _ Hl); cbn [den]; rewrite den_app, den_lits, eval_ladd, eval_lconst, Nat.add_1_r, lpow_succ_r;
    reflexivity
  end.

Lemma pushG_den : forall x t f tk ts, den x (pushG f tk ts) t = den x (tk :: ts) t.
Proof.
  intros x t f. induction f as [| f IH]; intros tk ts; [reflexivity |].
  cbn [pushG]. destruct tk as [v | w n].
  - destruct ts as [| [u | w n] rest]; try reflexivity.
    destruct (lastS w) as [a |] eqn:La; [| reflexivity].
    destruct (sym_eqb a v) eqn:Ea; [| reflexivity]. apply sym_eqb_eq in Ea. subst a.
    rewrite IH. cbn [den]. rewrite IH. cbn [den].
    change (v >> w ^^ eval n x *> den x rest t) with ([v] *> w ^^ eval n x *> den x rest t).
    rewrite (rep_rotate [v] w (v :: removelast w)); [reflexivity |].
    rewrite (lastS_app w v La) at 1. reflexivity.
  - cbv zeta. destruct w as [| b w'].
    + cbv beta iota. destruct ts as [| [a | w2' m'] rest].
      * ab2_tac (@nil sym).
      * ab2_tac (@nil sym).
      * destruct (w_eqb [] w2') eqn:Ew.
        -- apply w_eqb_eq in Ew. subst. cbn [den]. rewrite eval_ladd, lpow_plus. reflexivity.
        -- ab2_tac (@nil sym).
    + destruct ts as [| [a | w2' m'] rest].
      * destruct (lits (length (b :: w')) []) as [[u r'] |] eqn:Hl; cbv beta iota.
        -- destruct (w_eqb u (b :: w')) eqn:Hu; [absorbG_tac | ab2_tac (b :: w')].
        -- ab2_tac (b :: w').
      * destruct (lits (length (b :: w')) (TB a :: rest)) as [[u r'] |] eqn:Hl; cbv beta iota.
        -- destruct (w_eqb u (b :: w')) eqn:Hu; [absorbG_tac | ab2_tac (b :: w')].
        -- ab2_tac (b :: w').
      * destruct (w_eqb (b :: w') w2') eqn:Ew.
        -- apply w_eqb_eq in Ew. subst. cbn [den]. rewrite eval_ladd, lpow_plus. reflexivity.
        -- destruct (lits (length (b :: w')) (TR w2' m' :: rest)) as [[u r'] |] eqn:Hl; cbv beta iota.
           ++ destruct (w_eqb u (b :: w')) eqn:Hu; [absorbG_tac | ab2_tac (b :: w')].
           ++ ab2_tac (b :: w').
Qed.

Fixpoint mergeG (f : nat) (ts : list Tok) : list Tok :=
  match ts with [] => [] | tk :: ts => pushG f tk (mergeG f ts) end.
Lemma mergeG_den : forall x f ts t, den x (mergeG f ts) t = den x ts t.
Proof.
  induction ts as [| tk ts IH]; intros t; [reflexivity |].
  simpl mergeG. rewrite pushG_den, den_cons, IH, <- den_cons. reflexivity.
Qed.

Definition normG (ts : list Tok) : list Tok :=
  let e := dropTF (expand ts) in List.map trimTok (mergeG (4 * length e + 16) e).
Lemma normG_den : forall x ts, den x (normG ts) blank = den x ts blank.
Proof. intros. unfold normG. rewrite trim_den, mergeG_den, dropTF_den, expand_den. reflexivity. Qed.

(** A second normal form, with literal cells moved to the left through runs instead ([(b w)^n b = b (w b)^n]),
    and literal copies of a run's word in front of it absorbed. *)

Ltac absorbL_tac := match goal with
  | Hu : w_eqb ?u ?w = true, Hl : lits _ _ = Some (?u, _) |- _ =>
    apply w_eqb_eq in Hu; subst u; match goal with IH : forall tk ts, _ |- _ => rewrite IH end;
    rewrite (lits_eq _ _ _ _ Hl); cbn [den]; rewrite den_app, den_lits, eval_ladd, eval_lconst, Nat.add_1_r, lpow_succ_r;
    reflexivity
  end.
Ltac rotL_tac := match goal with
  | |- context [sym_eqb ?a ?b] =>
    destruct (sym_eqb a b) eqn:Ea; [| reflexivity]; apply sym_eqb_eq in Ea; subst a;
    match goal with IH : forall tk ts, _ |- _ => rewrite IH; cbn [den]; rewrite IH; cbn [den] end;
    match goal with |- ?b >> ?R = _ => transitivity ([b] *> R); [reflexivity |] end;
    match goal with |- [?b] *> (?w' ++ [?b]) ^^ ?e *> ?R = _ =>
      rewrite (rep_rotate [b] (w' ++ [b]) (b :: w') e R) by reflexivity; reflexivity end
  end.

Fixpoint pushL (f : nat) (tk : Tok) (ts : list Tok) : list Tok :=
  match f with
  | 0 => tk :: ts
  | S f =>
    match tk with
    | TB v =>
      match litsRun ts with
      | Some (u, w, n, r) => if w_eqb (v :: u) w then TR w (ladd n (lconst 1)) :: r else tk :: ts
      | None => tk :: ts
      end
    | TR w n =>
      let rot := match w, ts with
                 | b :: w', TB a :: rest =>
                   if sym_eqb a b then pushL f (TB a) (pushL f (TR (w' ++ [a]) n) rest) else tk :: ts
                 | _, _ => tk :: ts
                 end in
      let dflt := match w, lits (length w) ts with
                  | _ :: _, Some (u, rest') => if w_eqb u w then pushL f (TR w (ladd n (lconst 1))) rest' else rot
                  | _, _ => rot
                  end in
      match ts with
      | TR w' m :: rest => if w_eqb w w' then TR w (ladd n m) :: rest else dflt
      | _ => dflt
      end
    end
  end.

Lemma pushL_den : forall x t f tk ts, den x (pushL f tk ts) t = den x (tk :: ts) t.
Proof.
  intros x t f. induction f as [| f IH]; intros tk ts; [reflexivity |].
  cbn [pushL]. destruct tk as [v | w n].
  - destruct (litsRun ts) as [[[[u w] n] r] |] eqn:E; [| reflexivity].
    destruct (w_eqb (v :: u) w) eqn:Ew; [| reflexivity]. apply w_eqb_eq in Ew. subst w.
    rewrite (litsRun_eq ts u (v :: u) n r E). cbn [den]. rewrite den_app, den_lits. cbn [den].
    rewrite eval_ladd, eval_lconst, Nat.add_1_r. cbn [lpow]. rewrite Str_app_assoc. reflexivity.
  - destruct w as [| b w'].
    { destruct ts as [| [a | w2 m] rest]; try reflexivity.
      destruct (w_eqb [] w2) eqn:Ew; [| reflexivity].
      apply w_eqb_eq in Ew. subst. cbn [den]. rewrite eval_ladd, lpow_plus. reflexivity. }
    cbv zeta.
    destruct ts as [| [a | w2 m] rest].
    + destruct (lits (length (b :: w')) []) as [[u r'] |] eqn:Hl; [| reflexivity].
      destruct (w_eqb u (b :: w')) eqn:Hu; [absorbL_tac | reflexivity].
    + destruct (lits (length (b :: w')) (TB a :: rest)) as [[u r'] |] eqn:Hl.
      * destruct (w_eqb u (b :: w')) eqn:Hu; [absorbL_tac | rotL_tac].
      * rotL_tac.
    + destruct (w_eqb (b :: w') w2) eqn:Ew.
      * apply w_eqb_eq in Ew. subst. cbn [den]. rewrite eval_ladd, lpow_plus. reflexivity.
      * destruct (lits (length (b :: w')) (TR w2 m :: rest)) as [[u r'] |] eqn:Hl; [| reflexivity].
        destruct (w_eqb u (b :: w')) eqn:Hu; [absorbL_tac | reflexivity].
Qed.

Fixpoint mergeL (f : nat) (ts : list Tok) : list Tok :=
  match ts with [] => [] | tk :: ts => pushL f tk (mergeL f ts) end.
Lemma mergeL_den : forall x f ts t, den x (mergeL f ts) t = den x ts t.
Proof.
  induction ts as [| tk ts IH]; intros t; [reflexivity |].
  cbn [mergeL]. rewrite pushL_den, den_cons, IH, <- den_cons. reflexivity.
Qed.

Definition normL (ts : list Tok) : list Tok :=
  let e := dropTF (expand ts) in List.map trimTok (mergeL (4 * length e + 16) e).
Lemma normL_den : forall x ts, den x (normL ts) blank = den x ts blank.
Proof. intros. unfold normL. rewrite trim_den, mergeL_den, dropTF_den, expand_den. reflexivity. Qed.

(** Runs with a constant part written as a run of the variable part and literal copies after it, before
    normalizing: this puts more cells where the normal form can move them. *)
Definition splitTok (tk : Tok) : list Tok :=
  match tk with
  | TR w n => if allz (la n) then [tk] else TR w (mkLin 0 (la n)) :: List.map TB (w ^^ lc n)
  | _ => [tk]
  end.
Fixpoint splitC (ts : list Tok) : list Tok :=
  match ts with [] => [] | tk :: ts => splitTok tk ++ splitC ts end.
Lemma splitC_den : forall x ts t, den x (splitC ts) t = den x ts t.
Proof.
  induction ts as [| tk ts IH]; intros t; [reflexivity |].
  cbn [splitC]. rewrite den_app, IH. destruct tk as [v | w n]; [reflexivity |].
  unfold splitTok. destruct (allz (la n)); [reflexivity |].
  cbn [den]. rewrite den_lits. unfold eval at 2. cbn [lc la].
  rewrite <- Str_app_assoc, <- lpow_add. unfold eval. rewrite Nat.add_comm. reflexivity.
Qed.
Definition normS (ts : list Tok) : list Tok := normG (splitC ts).
Lemma normS_den : forall x ts, den x (normS ts) blank = den x ts blank.
Proof. intros. unfold normS. rewrite normG_den, splitC_den. reflexivity. Qed.

Lemma allB_den : forall x ts, forallb (fun tk => match tk with TB S0 => true | _ => false end) ts = true ->
  den x ts blank = blank.
Proof.
  induction ts as [| tk ts IH]; intros H; [reflexivity |]. simpl in H.
  destruct tk as [[] | w n]; try discriminate. simpl. rewrite IH; auto. symmetry. apply const_unfold.
Qed.

Definition allB (ts : list Tok) : bool := forallb (fun tk => match tk with TB S0 => true | _ => false end) ts.

(** ** Searching for the moves *)

Section Search.
Variable tm : TM.
Variable K : nat.   (* the most cells re-bracketed in front of a run *)

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint findR (f : nat) (c : list sym * list sym * state) (n : nat) : option nat :=
  match f with
  | 0 => None
  | S f => match c with
           | (_, [], _) => Some n
           | _ => match wstep tm c with None => None | Some c' => findR f c' (S n) end
           end
  end.

Fixpoint findL (q : state) (u : list sym) (f : nat) (c : list sym * list sym * state) (n : nat) : option nat :=
  match f with
  | 0 => None
  | S f => match c with
           | ([], r, q') => if st_eqb q' q && w_eqb (firstn (length u) r) u then Some n else
                             match wstep tm c with None => None | Some c' => findL q u f c' (S n) end
           | _ => match wstep tm c with None => None | Some c' => findL q u f c' (S n) end
           end
  end.

Definition crossRa (k : nat) (c : MC) : option MC :=
  match mr c, lits k (ml c) with
  | TR w n :: _, Some (u, _) =>
    if lzero n then None else
    match findR 400 (u, w, mst c) 0 with Some s => crossR tm k s c | None => None end
  | _, _ => None
  end.

Definition crossLa (k : nat) (c : MC) : option MC :=
  match ml c, lits k (mr c) with
  | TR w n :: _, Some (u, _) =>
    if lzero n then None else
    match findL (mst c) u 400 (w, u, mst c) 0 with Some s => crossL tm k s c | None => None end
  | _, _ => None
  end.

Definition orElse (a b : option MC) : option MC := match a with Some _ => a | None => b end.

Definition crossRany (c : MC) : option MC :=
  orElse (crossRa 0 c) (orElse (crossRa 1 c) (orElse (crossRa 2 c) (crossRa 3 c))).
Definition crossLany (c : MC) : option MC :=
  orElse (crossLa 1 c) (orElse (crossLa 2 c) (crossLa 3 c)).

Definition withR (c : MC) (o : option (list Tok)) : option MC :=
  match o with Some r => Some (mkMC (ml c) r (mst c)) | None => None end.
Definition withL (c : MC) (o : option (list Tok)) : option MC :=
  match o with Some l => Some (mkMC l (mr c) (mst c)) | None => None end.
Definition bindF (o : option MC) (f : MC -> option MC) : option MC :=
  match o with Some d => f d | None => None end.

Definition headRun (ts : list Tok) : bool := match ts with TR _ _ :: _ => true | _ => false end.
Definition headFT (ts : list Tok) : bool := match ts with TR [S0; S1] _ :: _ => true | _ => false end.
Fixpoint runAt (k : nat) (ts : list Tok) : bool :=
  match k, ts with
  | 0, ts => headRun ts
  | S k, TB _ :: ts => runAt k ts
  | _, _ => false
  end.

Fixpoint rotsR (k : nat) (c : MC) : option MC :=
  match k with
  | 0 => None
  | S k => orElse (rotsR k c) (if runAt (S k) (mr c) then bindF (withR c (rot (S k) (mr c))) crossRany else None)
  end.
Fixpoint rotsL (k : nat) (c : MC) : option MC :=
  match k with
  | 0 => None
  | S k => orElse (rotsL k c) (if runAt (S k) (ml c) then bindF (withL c (rot (S k) (ml c))) crossLany else None)
  end.

Definition candR (c : MC) : option MC :=
  orElse (if headRun (mr c) then crossRany c else None)
  (orElse (if headRun (mr c) then orElse (bindF (withR c (grp 3 (mr c))) crossRany)
                                        (bindF (withR c (grp 2 (mr c))) crossRany) else None)
  (rotsR K c)).
Definition candL (c : MC) : option MC :=
  orElse (if headRun (ml c) then crossLany c else None)
  (orElse (if headRun (ml c) then orElse (bindF (withL c (grp 3 (ml c))) crossLany)
                                        (bindF (withL c (grp 2 (ml c))) crossLany) else None)
  (rotsL K c)).

Definition bindS (o : option MC) : option MC := match o with Some d => mstep tm d | None => None end.
Definition stepA (c : MC) : option MC :=
  orElse (mstep tm c) (orElse (bindS (withL c (absorb (ml c)))) (orElse (bindS (withR c (absorb (mr c))))
  (orElse (bindS (withR c (rotBs K (mr c)))) (orElse (bindS (withL c (rotBs K (ml c))))
  (bindS (bindF (withR c (rotBs K (mr c))) (fun d => withL d (rotBs K (ml d))))))))).

Definition next (c : MC) : option (MC * bool) :=
  match orElse (candR c) (candL c) with
  | Some c' => Some (c', false)
  | None => match stepA c with Some c' => Some (c', true) | None => None end
  end.

(** The target: state [q], and either the head at the left end ([left = true]) with the right part [T], or the
    head at the right end with the left part [T]; [nf] is the normal form used to compare. *)
Variable nf : list Tok -> list Tok.
Hypothesis nf_den : forall x ts, den x (nf ts) blank = den x ts blank.

Definition atEnd (q : state) (left : bool) (c : MC) : bool :=
  st_eqb (mst c) q && allB (if left then ml c else mr c).

Definition normSide (left : bool) (c : MC) : MC :=
  if left then mkMC (ml c) (nf (mr c)) (mst c) else mkMC (nf (ml c)) (mr c) (mst c).

Fixpoint auto (q : state) (left : bool) (T : list Tok) (f : nat) (stepped : bool) (c : MC) : bool :=
  match f with
  | 0 => false
  | S f =>
    let e := atEnd q left c in
    let c := if e then normSide left c else c in
    if stepped && e && toks_eqb (if left then mr c else ml c) T then true
    else match next c with
         | Some (c', b) => auto q left T f (stepped || b) c'
         | None => false
         end
  end.

Definition tgt (q : state) (left : bool) (T : list Tok) : MC := if left then mkMC [] T q else mkMC T [] q.

(** Soundness. *)
Definition Reach (c c' : MC) : Prop := forall x, cden x c -->* cden x c'.

Lemma orElse_reach : forall c a b, (forall c', a = Some c' -> Reach c c') -> (forall c', b = Some c' -> Reach c c') ->
  forall c', orElse a b = Some c' -> Reach c c'.
Proof. intros c [a |] b Ha Hb c' H; simpl in H; eauto. Qed.


Lemma crossRa_reach : forall k c c', crossRa k c = Some c' -> Reach c c'.
Proof.
  intros k c c' H x. unfold crossRa in H.
  destruct (mr c) as [| [v | w n] rest]; try discriminate.
  destruct (lits k (ml c)) as [[u lr] |]; try discriminate.
  destruct (lzero n); try discriminate.
  destruct (findR 400 (u, w, mst c) 0) as [s |]; try discriminate.
  eapply crossR_sound; eauto.
Qed.

Lemma crossLa_reach : forall k c c', crossLa k c = Some c' -> Reach c c'.
Proof.
  intros k c c' H x. unfold crossLa in H.
  destruct (ml c) as [| [v | w n] rest]; try discriminate.
  destruct (lits k (mr c)) as [[u lr] |]; try discriminate.
  destruct (lzero n); try discriminate.
  destruct (findL (mst c) u 400 (w, u, mst c) 0) as [s |]; try discriminate.
  eapply crossL_sound; eauto.
Qed.

Lemma crossRany_reach : forall c c', crossRany c = Some c' -> Reach c c'.
Proof.
  intros c. unfold crossRany.
  repeat (apply orElse_reach; [intros; eapply crossRa_reach; eauto |]). intros; eapply crossRa_reach; eauto.
Qed.
Lemma crossLany_reach : forall c c', crossLany c = Some c' -> Reach c c'.
Proof.
  intros c. unfold crossLany.
  repeat (apply orElse_reach; [intros; eapply crossLa_reach; eauto |]). intros; eapply crossLa_reach; eauto.
Qed.

Lemma bindF_reach : forall c o f, (forall d, o = Some d -> forall x, cden x c = cden x d) ->
  (forall d c', f d = Some c' -> Reach d c') -> forall c', bindF o f = Some c' -> Reach c c'.
Proof.
  intros c [d |] f Ho Hf c' H x; simpl in H; [| discriminate].
  rewrite (Ho d eq_refl x). eapply Hf; eauto.
Qed.

Lemma withR_den : forall c o, (forall r, o = Some r -> forall x, den x (mr c) blank = den x r blank) ->
  forall d, withR c o = Some d -> forall x, cden x c = cden x d.
Proof. intros c [r |] H d E x; simpl in E; [| discriminate]. inversion E. subst. unfold cden. simpl. rewrite (H r eq_refl x). reflexivity. Qed.
Lemma withL_den : forall c o, (forall l, o = Some l -> forall x, den x (ml c) blank = den x l blank) ->
  forall d, withL c o = Some d -> forall x, cden x c = cden x d.
Proof. intros c [l |] H d E x; simpl in E; [| discriminate]. inversion E. subst. unfold cden. simpl. rewrite (H l eq_refl x). reflexivity. Qed.

Lemma ite_reach : forall c (p : bool) o, (forall c', o = Some c' -> Reach c c') ->
  forall c', (if p then o else None) = Some c' -> Reach c c'.
Proof. intros c [] o H c' E; [eauto | discriminate]. Qed.

Lemma rotsR_reach : forall k c c', rotsR k c = Some c' -> Reach c c'.
Proof.
  induction k as [| k IH]; intros c; simpl; [discriminate |].
  apply orElse_reach; [apply IH |]. apply ite_reach.
  apply bindF_reach; [| apply crossRany_reach].
  apply withR_den. intros r Hr x. apply rot_den with (k := S k). assumption.
Qed.
Lemma rotsL_reach : forall k c c', rotsL k c = Some c' -> Reach c c'.
Proof.
  induction k as [| k IH]; intros c; simpl; [discriminate |].
  apply orElse_reach; [apply IH |]. apply ite_reach.
  apply bindF_reach; [| apply crossLany_reach].
  apply withL_den. intros l Hl x. apply rot_den with (k := S k). assumption.
Qed.

Lemma candR_reach : forall c c', candR c = Some c' -> Reach c c'.
Proof.
  intros c. unfold candR.
  apply orElse_reach; [apply ite_reach; apply crossRany_reach |].
  apply orElse_reach; [| apply rotsR_reach].
  apply ite_reach. apply orElse_reach.
  - apply bindF_reach; [| apply crossRany_reach]. apply withR_den. intros r Hr x. eapply grp_den; eauto.
  - apply bindF_reach; [| apply crossRany_reach]. apply withR_den. intros r Hr x. eapply grp_den; eauto.
Qed.
Lemma candL_reach : forall c c', candL c = Some c' -> Reach c c'.
Proof.
  intros c. unfold candL.
  apply orElse_reach; [apply ite_reach; apply crossLany_reach |].
  apply orElse_reach; [| apply rotsL_reach].
  apply ite_reach. apply orElse_reach.
  - apply bindF_reach; [| apply crossLany_reach]. apply withL_den. intros r Hr x. eapply grp_den; eauto.
  - apply bindF_reach; [| apply crossLany_reach]. apply withL_den. intros r Hr x. eapply grp_den; eauto.
Qed.

Lemma bindS_sound : forall x c o, (forall d, o = Some d -> cden x c = cden x d) ->
  forall c', bindS o = Some c' -> cden x c -[ tm ]-> cden x c'.
Proof.
  intros x c [d |] Ho c' H; [| discriminate]. cbn [bindS] in H.
  rewrite (Ho d eq_refl). apply mstep_sound. exact H.
Qed.

Lemma stepA_sound : forall x c c', stepA c = Some c' -> cden x c -[ tm ]-> cden x c'.
Proof.
  intros x c c' H. unfold stepA, orElse in H.
  destruct (mstep tm c) eqn:E1; [inversion H; subst; apply mstep_sound; assumption |].
  destruct (bindS (withL c (absorb (ml c)))) eqn:E2.
  { inversion H. subst. eapply bindS_sound; [| exact E2].
    intros d Hd. apply (withL_den c (absorb (ml c))); auto. intros l Hl y. apply absorb_den. exact Hl. }
  destruct (bindS (withR c (absorb (mr c)))) eqn:E3.
  { inversion H. subst. eapply bindS_sound; [| exact E3].
    intros d Hd. apply (withR_den c (absorb (mr c))); auto. intros r Hr y. apply absorb_den. exact Hr. }
  destruct (bindS (withR c (rotBs K (mr c)))) eqn:E4.
  { inversion H. subst. eapply bindS_sound; [| exact E4].
    intros d Hd. apply (withR_den c (rotBs K (mr c))); auto. intros r Hr y. eapply rotBs_den. exact Hr. }
  destruct (bindS (withL c (rotBs K (ml c)))) eqn:E5.
  { inversion H. subst. eapply bindS_sound; [| exact E5].
    intros d Hd. apply (withL_den c (rotBs K (ml c))); auto. intros l Hl y. eapply rotBs_den. exact Hl. }
  eapply bindS_sound; [| exact H].
  intros d Hd. destruct (withR c (rotBs K (mr c))) as [e |] eqn:E6; cbn [bindF] in Hd; [| discriminate].
  rewrite (withR_den c (rotBs K (mr c)) ltac:(intros r Hr y; eapply rotBs_den; exact Hr) e E6 x).
  apply (withL_den e (rotBs K (ml e))); auto. intros l Hl y. eapply rotBs_den. exact Hl.
Qed.

Lemma next_sound : forall c c' b, next c = Some (c', b) -> forall x,
  cden x c -->* cden x c' /\ (b = true -> cden x c -->+ cden x c').
Proof.
  intros c c' b H x. unfold next in H.
  destruct (orElse (candR c) (candL c)) as [d |] eqn:E.
  - inversion H. subst. split; [| discriminate].
    eapply orElse_reach; [apply candR_reach | apply candL_reach | exact E].
  - destruct (stepA c) as [d |] eqn:E2; [| discriminate]. inversion H. subst.
    pose proof (stepA_sound x c c' E2). split; [apply evstep_one; assumption | intros _; apply progress_base; assumption].
Qed.

Lemma normSide_den : forall left c x, cden x (normSide left c) = cden x c.
Proof. intros [] c x; unfold normSide, cden; simpl; rewrite nf_den; reflexivity. Qed.

Theorem auto_sound : forall q left T f stepped c, auto q left T f stepped c = true -> forall x,
  cden x c -->* cden x (tgt q left T) /\ (stepped = false -> cden x c -->+ cden x (tgt q left T)).
Proof.
  intros q left T. induction f as [| f IH]; intros stepped c H x; simpl in H; [discriminate |].
  set (e := atEnd q left c) in H.
  set (d := if e then normSide left c else c) in H.
  assert (Ed : cden x d = cden x c) by (unfold d; destruct e; [apply normSide_den | reflexivity]).
  rewrite <- Ed.
  destruct (stepped && e && toks_eqb (if left then mr d else ml d) T) eqn:Hm.
  - apply andb_true_iff in Hm as [Hm H3]. apply andb_true_iff in Hm as [Hs He'].
    apply toks_eqb_eq in H3. subst stepped.
    assert (Et : cden x d = cden x (tgt q left T)).
    { pose proof He' as Ha. unfold e, atEnd in Ha. apply andb_true_iff in Ha as [Hq Hb]. apply st_eqb_eq in Hq.
      unfold allB in Hb.
      unfold d in *. rewrite He' in *. clear Ed.
      destruct left; unfold normSide, tgt, cden in *; cbn [ml mr mst] in *; rewrite <- H3, Hq, (allB_den x _ Hb);
        reflexivity. }
    rewrite Et. split; [apply evstep_refl | discriminate].
  - destruct (next d) as [[c' b] |] eqn:Hn; [| discriminate].
    destruct (next_sound d c' b Hn x) as [N1 N2].
    destruct (IH (stepped || b) c' H x) as [I1 I2].
    split; [eapply evstep_trans; eauto |].
    intros Hs. subst stepped. destruct b.
    + eapply progress_evstep_trans; [apply N2; reflexivity | exact I1].
    + eapply evstep_progress_trans; [exact N1 | apply I2; reflexivity].
Qed.

Corollary auto_reach : forall q left T f c, auto q left T f false c = true -> forall x,
  cden x c -->+ cden x (tgt q left T).
Proof. intros. eapply auto_sound; eauto. Qed.

End Search.
