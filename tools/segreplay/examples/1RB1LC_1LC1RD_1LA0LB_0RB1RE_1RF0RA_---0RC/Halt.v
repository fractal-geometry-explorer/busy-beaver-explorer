(** The last 59,656,218,975 visits of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC, replayed by the generated
    checker: from visit 79,800,000,000,000 (the start of the last segment J399 of the busycoq proof) the
    orbit of [Visits.op] reaches some (a, 3), where the machine halts. *)
From Coq Require Import ZArith Lia Uint63.
From SegReplay Require Import Core.
From M Require Import Map Visits Link Final.
Local Open Scope Z_scope.

Lemma zn_first a b : 0 <= a -> 0 <= b -> zmk 0 a b = zn (Z.to_nat a) (Z.to_nat b).
Proof. intros. unfold zn. rewrite !Z2Nat.id by assumption. reflexivity. Qed.

Theorem tail_halts :
  exists j a, opIter j (Z.to_nat 208496432744458, Z.to_nat 70803563135337) = Some (a, 3%nat).
Proof.
  apply (halt_orbit (Z.to_nat 59656218975)).
  rewrite <- zn_first by (intro H; discriminate H).
  exact orbit_halts.
Qed.
Print Assumptions tail_halts.
