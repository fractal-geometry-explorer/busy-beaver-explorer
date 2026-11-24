(* The two rules at the left end of the tape that the run uses besides PR 93's 21 macro rules.
   build.sh appends this to the head of U_A.v (everything up to rule_pairR) to make Wall.v.
   CfgL l r = l <{{B}} [1] *> r; D_word n = 1(11)^n 00; in "l <* w" the word w is listed outward from the head. *)

Ltac auto_rule := repeat (norm_cb; first [ solve [finish] | follow scanR | follow scanR1 | follow scanB | follow scanB0 | follow scanC | follow ones2_1 | follow ones2 | follow scanPair | step ]).

(* B at the left end with a single 1 before it *)
Lemma rule_wall1 r a : CfgL (0inf <* [1]) (D_word a *> r) -->*
  CfgL (0inf <* [1; 0]^^(a + 3)) ([1; 0] *> r).
Proof. auto_rule. Qed.

(* B at the left end with blank tape before it *)
Lemma rule_wall0 r a b : CfgL 0inf (D_word a *> [1] *> [1; 1]^^b *> [0] *> r) -->*
  CfgL (0inf <* [1; 0] <* [1; 1]^^(a + 1) <* [1; 0]^^(b + 2)) ([1] *> r).
Proof. auto_rule. Qed.
End HU.
