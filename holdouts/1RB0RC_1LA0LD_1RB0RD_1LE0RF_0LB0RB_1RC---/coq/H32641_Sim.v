(** * 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC--- (bbchallenge 32641): the machine and two simulators

    [wstep] is the machine on a finite window of cells (two lists and a facing direction); a run of it is a run
    of the machine whatever lies outside the window ([wrun_ok]).  [mstep] is a block macro step: the tape is a
    list of blocks, each block a [positive] whose bits are its cells (lowest bit = the cell nearest to the head,
    the top bit is a sentinel), and one step takes the head through one block by a table lookup; an entry that
    is missing from the table is computed on the spot ([mkEntry], a window run).  [mrun_ok]: a macro run is a
    run of the machine, for every table whose entries agree with [mkEntry].  Nothing here is specific to a block
    size. *)

From Coq Require Import Lists.List PArith FMapPositive. Import ListNotations.
From BusyCoq Require Export Individual62.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, S0 => Some (S1, R, B)  | A, S1 => Some (S0, R, C)
  | B, S0 => Some (S1, L, A)  | B, S1 => Some (S0, L, D)
  | C, S0 => Some (S1, R, B)  | C, S1 => Some (S0, R, D)
  | D, S0 => Some (S1, L, E)  | D, S1 => Some (S0, R, F)
  | E, S0 => Some (S0, L, B)  | E, S1 => Some (S0, R, B)
  | F, S0 => Some (S1, R, C)  | F, S1 => None
  end.

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Iterating a function a binary number of times *)

Lemma iter_inv : forall {X : Type} (P : X -> Prop) (f : X -> X), (forall x, P x -> P (f x)) ->
  forall n x, P x -> P (Pos.iter f x n).
Proof.
  intros X P f Hf. induction n as [n IH | n IH |]; intros x Hx; cbn [Pos.iter].
  - apply Hf, IH, IH, Hx.
  - apply IH, IH, Hx.
  - apply Hf, Hx.
Qed.

(** ** The window simulator

    [mkW l r q true] is the head in state [q] on the first cell of [r], with [l] on its left (nearest cell first);
    [mkW l r q false] is the head on the first cell of [l], with [r] on its right. *)

Record W := mkW { wl : list sym; wr : list sym; wq : state; wf : bool }.

Definition wsem (Lt Rt : Stream sym) (c : W) : Q * tape :=
  if wf c then (wl c *> Lt) {{wq c}}> (wr c *> Rt) else (wl c *> Lt) <{{wq c}} (wr c *> Rt).

Definition wstep (c : W) : option W :=
  match c with
  | mkW l r q true =>
    match r with
    | [] => None
    | s :: r' =>
      match tm (q, s) with
      | Some (s', R, q') => Some (mkW (s' :: l) r' q' true)
      | Some (s', L, q') => Some (mkW l (s' :: r') q' false)
      | None => None
      end
    end
  | mkW l r q false =>
    match l with
    | [] => None
    | s :: l' =>
      match tm (q, s) with
      | Some (s', R, q') => Some (mkW (s' :: l') r q' true)
      | Some (s', L, q') => Some (mkW l' (s' :: r) q' false)
      | None => None
      end
    end
  end.

Lemma wstep_ok : forall c c', wstep c = Some c' -> forall Lt Rt, wsem Lt Rt c --> wsem Lt Rt c'.
Proof.
  intros [l r q f] c' H Lt Rt. destruct f; cbn [wstep] in H.
  - destruct r as [| s r']; [discriminate |].
    destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E; [| discriminate].
    destruct d; inversion H; subst c'.
    + exact (@step_left tm q q' s s' (l *> Lt) (r' *> Rt) E).
    + exact (@step_right tm q q' s s' (l *> Lt) (r' *> Rt) E).
  - destruct l as [| s l']; [discriminate |].
    destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E; [| discriminate].
    destruct d; inversion H; subst c'.
    + exact (@step_left tm q q' s s' (l' *> Lt) (r *> Rt) E).
    + exact (@step_right tm q q' s s' (l' *> Lt) (r *> Rt) E).
Qed.

Definition wstep1 (c : W) : W := match wstep c with Some c' => c' | None => c end.
Definition wrun (n : positive) (c : W) : W := Pos.iter wstep1 c n.

Lemma wrun_ok : forall n c Lt Rt, wsem Lt Rt c -->* wsem Lt Rt (wrun n c).
Proof.
  intros n c Lt Rt. unfold wrun.
  apply (iter_inv (fun d => wsem Lt Rt c -->* wsem Lt Rt d)); [| apply evstep_refl].
  intros x Hx. unfold wstep1. destruct (wstep x) as [x' |] eqn:E; [| exact Hx].
  eapply evstep_trans; [exact Hx |]. apply evstep_one. apply wstep_ok. exact E.
Qed.

(** ** Blocks *)

Fixpoint dec (p : positive) : list sym :=
  match p with xH => [] | xO p => S0 :: dec p | xI p => S1 :: dec p end.
Fixpoint enc (l : list sym) : positive :=
  match l with [] => xH | S0 :: l => xO (enc l) | S1 :: l => xI (enc l) end.
Lemma dec_enc : forall l, dec (enc l) = l.
Proof. induction l as [| [|] l IH]; cbn [enc dec]; congruence. Qed.

(** The cells of a list of blocks, then blanks for ever. *)
Fixpoint decs (bs : list positive) : Stream sym :=
  match bs with [] => const S0 | b :: bs => dec b *> decs bs end.

(** Run inside a window until the head leaves it. *)
Fixpoint brun (fuel : nat) (c : W) : option W :=
  match fuel with
  | O => None
  | S fuel =>
    match c with
    | mkW _ [] _ true => Some c
    | mkW [] _ _ false => Some c
    | _ => match wstep c with Some c' => brun fuel c' | None => None end
    end
  end.

Lemma brun_ok : forall fuel c c', brun fuel c = Some c' -> forall Lt Rt, wsem Lt Rt c -->* wsem Lt Rt c'.
Proof.
  induction fuel as [| fuel IH]; intros c c' H Lt Rt; [discriminate |].
  cbn [brun] in H.
  assert (G : c' = c \/ exists d, wstep c = Some d /\ brun fuel d = Some c').
  { destruct c as [[| sl l] [| sr r] q [|]];
      first [ left; congruence | right; destruct (wstep _) as [d |]; [| discriminate]; eauto ]. }
  destruct G as [-> | [d [H1 H2]]]; [apply evstep_refl |].
  eapply evstep_step; [apply wstep_ok; exact H1 |]. apply IH. exact H2.
Qed.

(** What the machine does with a block: it leaves on the right ([ER], with the block as seen from its right end)
    or on the left ([EL], with the block as seen from its left end), in a new state. *)
Inductive Ent := ER (b : positive) (q : state) | EL (b : positive) (q : state).

(** [f = true]: the head enters the block [b] on its first cell from the left; [f = false]: on its last cell
    from the right ([b] is then read right to left). *)
Definition entOf (w : W) : option Ent :=
  if wf w then match wr w with [] => Some (ER (enc (wl w)) (wq w)) | _ => None end
  else match wl w with [] => Some (EL (enc (wr w)) (wq w)) | _ => None end.
Definition mkEntry (fuel : nat) (q : state) (f : bool) (b : positive) : option Ent :=
  match brun fuel (if f then mkW [] (dec b) q true else mkW (dec b) [] q false) with
  | Some w => entOf w
  | None => None
  end.

(** The table of one state and one side, computed from a list of blocks. *)
Definition build (fuel : nat) (q : state) (f : bool) (keys : list positive) : PositiveMap.t Ent :=
  fold_left (fun t b => match mkEntry fuel q f b with Some e => PositiveMap.add b e t | None => t end)
    keys (PositiveMap.empty Ent).

Lemma build_ok : forall fuel q f keys b e, PositiveMap.find b (build fuel q f keys) = Some e -> mkEntry fuel q f b = Some e.
Proof.
  intros fuel q f keys. unfold build.
  assert (G : forall t, (forall b e, PositiveMap.find b t = Some e -> mkEntry fuel q f b = Some e) ->
    forall b e, PositiveMap.find b (fold_left
      (fun t b => match mkEntry fuel q f b with Some e => PositiveMap.add b e t | None => t end) keys t) = Some e ->
      mkEntry fuel q f b = Some e).
  { induction keys as [| k keys IH]; intros t Ht; cbn [fold_left]; [exact Ht |].
    apply IH. intros b e. destruct (mkEntry fuel q f k) as [e0 |] eqn:E; [| apply Ht].
    destruct (Pos.eq_dec b k) as [-> | Hne].
    - rewrite PositiveMap.gss. congruence.
    - rewrite PositiveMap.gso by exact Hne. apply Ht. }
  apply G. intros b e H. rewrite PositiveMap.gempty in H. discriminate.
Qed.

(** ** The macro simulator *)

Record MC := mkM { mL : list positive; mR : list positive; mq : state; mf : bool }.

Definition msem (c : MC) : Q * tape :=
  if mf c then decs (mL c) {{mq c}}> decs (mR c) else decs (mL c) <{{mq c}} decs (mR c).

Section Macro.
Variable fuel : nat.
Variable T : state -> bool -> PositiveMap.t Ent.
Variable bl : positive.
Hypothesis T_ok : forall q f b e, PositiveMap.find b (T q f) = Some e -> mkEntry fuel q f b = Some e.
Hypothesis bl_ok : forallb (fun s => match s with S0 => true | S1 => false end) (dec bl) = true.

Definition look (q : state) (f : bool) (b : positive) : option Ent :=
  match PositiveMap.find b (T q f) with Some e => Some e | None => mkEntry fuel q f b end.

Definition mstep (c : MC) : MC :=
  match c with
  | mkM Ls Rs q true =>
    match Rs with
    | [] => match look q true bl with
            | Some (ER b' q') => mkM (b' :: Ls) [] q' true
            | Some (EL b' q') => mkM Ls [b'] q' false
            | None => c
            end
    | b :: Rs' => match look q true b with
            | Some (ER b' q') => mkM (b' :: Ls) Rs' q' true
            | Some (EL b' q') => mkM Ls (b' :: Rs') q' false
            | None => c
            end
    end
  | mkM Ls Rs q false =>
    match Ls with
    | [] => match look q false bl with
            | Some (ER b' q') => mkM [b'] Rs q' true
            | Some (EL b' q') => mkM [] (b' :: Rs) q' false
            | None => c
            end
    | b :: Ls' => match look q false b with
            | Some (ER b' q') => mkM (b' :: Ls') Rs q' true
            | Some (EL b' q') => mkM Ls' (b' :: Rs) q' false
            | None => c
            end
    end
  end.

Lemma look_ok : forall q f b e, look q f b = Some e -> mkEntry fuel q f b = Some e.
Proof.
  intros q f b e H. unfold look in H.
  destruct (PositiveMap.find b (T q f)) as [e0 |] eqn:E; [| exact H].
  inversion H; subst e0. exact (T_ok q f b e E).
Qed.

Lemma zeros_const : forall l, forallb (fun s => match s with S0 => true | S1 => false end) l = true ->
  l *> const S0 = const S0.
Proof.
  induction l as [| [|] l IH]; intros H; cbn [forallb] in H; [reflexivity | | discriminate].
  cbn [Str_app]. rewrite IH by exact H. rewrite <- const_unfold. reflexivity.
Qed.

Lemma bl_blank : dec bl *> const S0 = const S0.
Proof. apply zeros_const. exact bl_ok. Qed.

(** Entering a block from the left. *)
Lemma enter_r : forall q b e Lt Rt, mkEntry fuel q true b = Some e ->
  Lt {{q}}> (dec b *> Rt) -->*
  match e with ER b' q' => (dec b' *> Lt) {{q'}}> Rt | EL b' q' => Lt <{{q'}} (dec b' *> Rt) end.
Proof.
  intros q b e Lt Rt H. unfold mkEntry in H.
  destruct (brun fuel (mkW [] (dec b) q true)) as [[l r q' f] |] eqn:E; [| discriminate].
  pose proof (brun_ok _ _ _ E Lt Rt) as G.
  unfold entOf in H. cbn [wf wl wr wq] in H. destruct f.
  - destruct r; [| discriminate]. injection H as <-. rewrite dec_enc. exact G.
  - destruct l; [| discriminate]. injection H as <-. rewrite dec_enc. exact G.
Qed.

(** Entering a block from the right. *)
Lemma enter_l : forall q b e Lt Rt, mkEntry fuel q false b = Some e ->
  (dec b *> Lt) <{{q}} Rt -->*
  match e with ER b' q' => (dec b' *> Lt) {{q'}}> Rt | EL b' q' => Lt <{{q'}} (dec b' *> Rt) end.
Proof.
  intros q b e Lt Rt H. unfold mkEntry in H.
  destruct (brun fuel (mkW (dec b) [] q false)) as [[l r q' f] |] eqn:E; [| discriminate].
  pose proof (brun_ok _ _ _ E Lt Rt) as G.
  unfold entOf in H. cbn [wf wl wr wq] in H. destruct f.
  - destruct r; [| discriminate]. injection H as <-. rewrite dec_enc. exact G.
  - destruct l; [| discriminate]. injection H as <-. rewrite dec_enc. exact G.
Qed.

Lemma mstep_ok : forall c, msem c -->* msem (mstep c).
Proof.
  intros [Ls Rs q f]. destruct f; cbn [mstep].
  - destruct Rs as [| b Rs'].
    + destruct (look q true bl) as [e |] eqn:E; [| apply evstep_refl].
      apply look_ok in E. pose proof (enter_r q bl e (decs Ls) (const S0) E) as G.
      rewrite bl_blank in G. destruct e; exact G.
    + destruct (look q true b) as [e |] eqn:E; [| apply evstep_refl].
      apply look_ok in E. pose proof (enter_r q b e (decs Ls) (decs Rs') E) as G.
      destruct e; exact G.
  - destruct Ls as [| b Ls'].
    + destruct (look q false bl) as [e |] eqn:E; [| apply evstep_refl].
      apply look_ok in E. pose proof (enter_l q bl e (const S0) (decs Rs) E) as G.
      rewrite bl_blank in G. destruct e; exact G.
    + destruct (look q false b) as [e |] eqn:E; [| apply evstep_refl].
      apply look_ok in E. pose proof (enter_l q b e (decs Ls') (decs Rs) E) as G.
      destruct e; exact G.
Qed.

Definition mrun (n : positive) (c : MC) : MC := Pos.iter mstep c n.

Lemma mrun_ok : forall n c, msem c -->* msem (mrun n c).
Proof.
  intros n c. unfold mrun.
  apply (iter_inv (fun d => msem c -->* msem d)); [| apply evstep_refl].
  intros x Hx. eapply evstep_trans; [exact Hx | apply mstep_ok].
Qed.

Lemma mrun_to : forall n c c', mrun n c = c' -> msem c -->* msem c'.
Proof. intros n c c' <-. apply mrun_ok. Qed.

End Macro.
