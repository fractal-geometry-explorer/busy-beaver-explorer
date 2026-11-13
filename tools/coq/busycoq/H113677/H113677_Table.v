(** * 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB: from blank tape to the last macro state before step 1e30

    The first 29,301 steps (blank tape to [fO 14 37 11]) by the symbolic runner, then the branch table of
    py/macro.py: 196 moves, each a rule or a k-fold iterate with concrete arguments.  Large numbers are
    written [N.to_nat n%N] and only compared by [lia], never computed in unary. *)

From Coq Require Import Lists.List Lia PeanoNat NArith. Import ListNotations.
From BusyCoq Require Import SymForms.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

From BusyCoq Require Import H113677_Rules.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition blank_mc : MC := mkMC [] [] A.
Lemma blank_O : c0 -->+ fO 14 37 11.
Proof.
  pose proof (rules_sound tm KK (Nat.pow 2 16) blank_mc [] O_mc [mkLin 14 []; mkLin 37 []; mkLin 11 []]
    ltac:(vm_compute; reflexivity) []) as H.
  exact H.
Qed.

Lemma move0 : fO 14 37 11 -->* fS1 15 37 9.
Proof. eapply tr; [apply progress_evstep; exact (oentry 14 31 9) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move1 : fS1 15 37 9 -->* fS1 27 85 1.
Proof. eapply tr; [exact (cycle_iter 4 15 35 1) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move2 : fS1 27 85 1 -->* fRF 30 5 91.
Proof. eapply tr; [apply progress_evstep; exact (oexit 27 79) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move3 : fRF 30 5 91 -->* fRF 30 95 1.
Proof. eapply tr; [exact (rcyc_iter 90 30 5 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move4 : fRF 30 95 1 -->* fEF 30 47.
Proof. eapply tr; [apply progress_evstep; exact (rend_ 30 47) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move5 : fEF 30 47 -->* fT3 5 14 23 8 7 44.
Proof. eapply tr; [apply progress_evstep; exact (eentry 23 42) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move6 : fT3 5 14 23 8 7 44 -->* fT3 21 46 3 36 27 36.
Proof. eapply tr; [exact (cycle3_iter 4 5 8 3 2 1 36) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move7 : fT3 21 46 3 36 27 36 -->* fT2 26 92 36 34.
Proof. eapply tr; [apply progress_evstep; exact (texit3 21 33 40 31 21) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move8 : fT2 26 92 36 34 -->* fT2 77 211 121 0.
Proof. eapply tr; [exact (cycle2_iter 17 26 86 30 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move9 : fT2 77 211 121 0 -->* fRG 80 210 4 117.
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 77 209 111) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move10 : fRG 80 210 4 117 -->* fRG 80 210 120 1.
Proof. eapply tr; [exact (gcyc_iter 116 80 210 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move11 : fRG 80 210 120 1 -->* fO 79 219 61.
Proof. eapply tr; [apply progress_evstep; exact (gend_ 78 210 60) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move12 : fO 79 219 61 -->* fS1 80 219 59.
Proof. eapply tr; [apply progress_evstep; exact (oentry 79 213 59) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move13 : fS1 80 219 59 -->* fS1 167 567 1.
Proof. eapply tr; [exact (cycle_iter 29 80 217 1) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move14 : fS1 167 567 1 -->* fRF 170 5 573.
Proof. eapply tr; [apply progress_evstep; exact (oexit 167 561) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move15 : fRF 170 5 573 -->* fRF 170 577 1.
Proof. eapply tr; [exact (rcyc_iter 572 170 5 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move16 : fRF 170 577 1 -->* fEF 170 288.
Proof. eapply tr; [apply progress_evstep; exact (rend_ 170 288) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move17 : fEF 170 288 -->* fT3 5 14 163 8 7 285.
Proof. eapply tr; [apply progress_evstep; exact (eentry 163 283) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move18 : fT3 5 14 163 8 7 285 -->* fT3 133 270 3 232 167 221.
Proof. eapply tr; [exact (cycle3_iter 32 5 8 3 2 1 221) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move19 : fT3 133 270 3 232 167 221 -->* fT2 138 512 176 219.
Proof. eapply tr; [apply progress_evstep; exact (texit3 133 218 264 227 161) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move20 : fT2 138 512 176 219 -->* fT2 465 1275 721 1.
Proof. eapply tr; [exact (cycle2_iter 109 138 506 170 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move21 : fT2 465 1275 721 1 -->* fRG 468 1274 5 716.
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 465 1273 709) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move22 : fRG 468 1274 5 716 -->* fRG 468 1274 720 1.
Proof. eapply tr; [exact (gcyc_iter 715 468 1274 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move23 : fRG 468 1274 720 1 -->* fO 467 1283 361.
Proof. eapply tr; [apply progress_evstep; exact (gend_ 466 1274 360) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move24 : fO 467 1283 361 -->* fS1 468 1283 359.
Proof. eapply tr; [apply progress_evstep; exact (oentry 467 1277 359) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move25 : fS1 468 1283 359 -->* fS1 1005 3431 1.
Proof. eapply tr; [exact (cycle_iter 179 468 1281 1) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move26 : fS1 1005 3431 1 -->* fRF 1008 5 3437.
Proof. eapply tr; [apply progress_evstep; exact (oexit 1005 3425) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move27 : fRF 1008 5 3437 -->* fRF 1008 3441 1.
Proof. eapply tr; [exact (rcyc_iter 3436 1008 5 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move28 : fRF 1008 3441 1 -->* fEF 1008 1720.
Proof. eapply tr; [apply progress_evstep; exact (rend_ 1008 1720) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move29 : fEF 1008 1720 -->* fT3 5 14 1001 8 7 1717.
Proof. eapply tr; [apply progress_evstep; exact (eentry 1001 1715) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move30 : fT3 5 14 1001 8 7 1717 -->* fT3 805 1614 1 1408 1007 1317.
Proof. eapply tr; [exact (cycle3_iter 200 5 8 1 2 1 1317) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move31 : fT3 805 1614 1 1408 1007 1317 -->* fU3 807 1614 1409 1012 1315.
Proof. eapply tr; [apply progress_evstep; exact (texit1 805 1315 1608 1403 1001) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move32 : fU3 807 1614 1409 1012 1315 -->* fU3 2778 (N.to_nat 6213%N) 1409 4297 1.
Proof. eapply tr; [exact (ucyc_iter 657 807 1612 1403 1006 1) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move33 : fU3 2778 (N.to_nat 6213%N) 1409 4297 1 -->* fRG3 2781 (N.to_nat 6218%N) 1407 5 4296.
Proof. eapply tr; [apply progress_evstep; exact (uexit1 2778 (N.to_nat 6211%N) 1403 4285) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move34 : fRG3 2781 (N.to_nat 6218%N) 1407 5 4296 -->* fRG3 2781 (N.to_nat 6218%N) 1407 4300 1.
Proof. eapply tr; [exact (g3cyc_iter 4295 2781 (N.to_nat 6218%N) 1407 5 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move35 : fRG3 2781 (N.to_nat 6218%N) 1407 4300 1 -->* fT2 2784 (N.to_nat 6227%N) 1413 2149.
Proof. eapply tr; [apply progress_evstep; exact (g3end_ 2781 (N.to_nat 6218%N) 1403 2148) | apply fRG3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move36 : fT2 2784 (N.to_nat 6227%N) 1413 2149 -->* fT2 (N.to_nat 6006%N) (N.to_nat 13745%N) (N.to_nat 6783%N) 1.
Proof. eapply tr; [exact (cycle2_iter 1074 2784 (N.to_nat 6221%N) 1407 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move37 : fT2 (N.to_nat 6006%N) (N.to_nat 13745%N) (N.to_nat 6783%N) 1 -->* fRG (N.to_nat 6009%N) (N.to_nat 13744%N) 5 (N.to_nat 6778%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 6006%N) (N.to_nat 13743%N) (N.to_nat 6771%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move38 : fRG (N.to_nat 6009%N) (N.to_nat 13744%N) 5 (N.to_nat 6778%N) -->* fRG (N.to_nat 6009%N) (N.to_nat 13744%N) (N.to_nat 6782%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 6777%N) (N.to_nat 6009%N) (N.to_nat 13744%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move39 : fRG (N.to_nat 6009%N) (N.to_nat 13744%N) (N.to_nat 6782%N) 1 -->* fO (N.to_nat 6008%N) (N.to_nat 13753%N) 3392.
Proof. eapply tr; [apply progress_evstep; exact (gend_ (N.to_nat 6007%N) (N.to_nat 13744%N) 3391) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move40 : fO (N.to_nat 6008%N) (N.to_nat 13753%N) 3392 -->* fS1 (N.to_nat 6009%N) (N.to_nat 13753%N) 3390.
Proof. eapply tr; [apply progress_evstep; exact (oentry (N.to_nat 6008%N) (N.to_nat 13747%N) 3390) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move41 : fS1 (N.to_nat 6009%N) (N.to_nat 13753%N) 3390 -->* fS1 (N.to_nat 11094%N) (N.to_nat 34093%N) 0.
Proof. eapply tr; [exact (cycle_iter 1695 (N.to_nat 6009%N) (N.to_nat 13751%N) 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move42 : fS1 (N.to_nat 11094%N) (N.to_nat 34093%N) 0 -->* fRF (N.to_nat 11097%N) 4 (N.to_nat 34100%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 11094%N) (N.to_nat 34090%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move43 : fRF (N.to_nat 11097%N) 4 (N.to_nat 34100%N) -->* fRF (N.to_nat 11097%N) (N.to_nat 34103%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 34099%N) (N.to_nat 11097%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move44 : fRF (N.to_nat 11097%N) (N.to_nat 34103%N) 1 -->* fEF (N.to_nat 11097%N) (N.to_nat 17051%N).
Proof. eapply tr; [apply progress_evstep; exact (rend_ (N.to_nat 11097%N) (N.to_nat 17051%N)) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move45 : fEF (N.to_nat 11097%N) (N.to_nat 17051%N) -->* fT3 5 14 (N.to_nat 11090%N) 8 7 (N.to_nat 17048%N).
Proof. eapply tr; [apply progress_evstep; exact (eentry (N.to_nat 11090%N) (N.to_nat 17046%N)) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move46 : fT3 5 14 (N.to_nat 11090%N) 8 7 (N.to_nat 17048%N) -->* fT3 (N.to_nat 8877%N) (N.to_nat 17758%N) 0 (N.to_nat 15534%N) (N.to_nat 11097%N) (N.to_nat 12612%N).
Proof. eapply tr; [exact (cycle3_iter 2218 5 8 0 2 1 (N.to_nat 12612%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move47 : fT3 (N.to_nat 8877%N) (N.to_nat 17758%N) 0 (N.to_nat 15534%N) (N.to_nat 11097%N) (N.to_nat 12612%N) -->* fT2 (N.to_nat 8878%N) (N.to_nat 33291%N) (N.to_nat 11101%N) (N.to_nat 12612%N).
Proof. eapply tr; [apply progress_evstep; exact (texit0 (N.to_nat 8877%N) (N.to_nat 12611%N) (N.to_nat 17753%N) (N.to_nat 15532%N) (N.to_nat 11095%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move48 : fT2 (N.to_nat 8878%N) (N.to_nat 33291%N) (N.to_nat 11101%N) (N.to_nat 12612%N) -->* fT2 (N.to_nat 27796%N) (N.to_nat 77433%N) (N.to_nat 42631%N) 0.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 6306%N) (N.to_nat 8878%N) (N.to_nat 33285%N) (N.to_nat 11095%N) 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move49 : fT2 (N.to_nat 27796%N) (N.to_nat 77433%N) (N.to_nat 42631%N) 0 -->* fRG (N.to_nat 27799%N) (N.to_nat 77432%N) 4 (N.to_nat 42627%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 (N.to_nat 27796%N) (N.to_nat 77431%N) (N.to_nat 42621%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move50 : fRG (N.to_nat 27799%N) (N.to_nat 77432%N) 4 (N.to_nat 42627%N) -->* fRG (N.to_nat 27799%N) (N.to_nat 77432%N) (N.to_nat 42630%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 42626%N) (N.to_nat 27799%N) (N.to_nat 77432%N) 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move51 : fRG (N.to_nat 27799%N) (N.to_nat 77432%N) (N.to_nat 42630%N) 1 -->* fO (N.to_nat 27798%N) (N.to_nat 77441%N) (N.to_nat 21316%N).
Proof. eapply tr; [apply progress_evstep; exact (gend_ (N.to_nat 27797%N) (N.to_nat 77432%N) (N.to_nat 21315%N)) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move52 : fO (N.to_nat 27798%N) (N.to_nat 77441%N) (N.to_nat 21316%N) -->* fS1 (N.to_nat 27799%N) (N.to_nat 77441%N) (N.to_nat 21314%N).
Proof. eapply tr; [apply progress_evstep; exact (oentry (N.to_nat 27798%N) (N.to_nat 77435%N) (N.to_nat 21314%N)) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move53 : fS1 (N.to_nat 27799%N) (N.to_nat 77441%N) (N.to_nat 21314%N) -->* fS1 (N.to_nat 59770%N) (N.to_nat 205325%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 10657%N) (N.to_nat 27799%N) (N.to_nat 77439%N) 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move54 : fS1 (N.to_nat 59770%N) (N.to_nat 205325%N) 0 -->* fRF (N.to_nat 59773%N) 4 (N.to_nat 205332%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 59770%N) (N.to_nat 205322%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move55 : fRF (N.to_nat 59773%N) 4 (N.to_nat 205332%N) -->* fRF (N.to_nat 59773%N) (N.to_nat 205335%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 205331%N) (N.to_nat 59773%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move56 : fRF (N.to_nat 59773%N) (N.to_nat 205335%N) 1 -->* fEF (N.to_nat 59773%N) (N.to_nat 102667%N).
Proof. eapply tr; [apply progress_evstep; exact (rend_ (N.to_nat 59773%N) (N.to_nat 102667%N)) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move57 : fEF (N.to_nat 59773%N) (N.to_nat 102667%N) -->* fT3 5 14 (N.to_nat 59766%N) 8 7 (N.to_nat 102664%N).
Proof. eapply tr; [apply progress_evstep; exact (eentry (N.to_nat 59766%N) (N.to_nat 102662%N)) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move58 : fT3 5 14 (N.to_nat 59766%N) 8 7 (N.to_nat 102664%N) -->* fT3 (N.to_nat 47817%N) (N.to_nat 95638%N) 1 (N.to_nat 83679%N) (N.to_nat 59772%N) (N.to_nat 78758%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 11953%N) 5 8 1 2 1 (N.to_nat 78758%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move59 : fT3 (N.to_nat 47817%N) (N.to_nat 95638%N) 1 (N.to_nat 83679%N) (N.to_nat 59772%N) (N.to_nat 78758%N) -->* fU3 (N.to_nat 47819%N) (N.to_nat 95638%N) (N.to_nat 83680%N) (N.to_nat 59777%N) (N.to_nat 78756%N).
Proof. eapply tr; [apply progress_evstep; exact (texit1 (N.to_nat 47817%N) (N.to_nat 78756%N) (N.to_nat 95632%N) (N.to_nat 83674%N) (N.to_nat 59766%N)) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move60 : fU3 (N.to_nat 47819%N) (N.to_nat 95638%N) (N.to_nat 83680%N) (N.to_nat 59777%N) (N.to_nat 78756%N) -->* fU3 (N.to_nat 165953%N) (N.to_nat 371284%N) (N.to_nat 83680%N) (N.to_nat 256667%N) 0.
Proof. eapply tr; [exact (ucyc_iter (N.to_nat 39378%N) (N.to_nat 47819%N) (N.to_nat 95636%N) (N.to_nat 83674%N) (N.to_nat 59771%N) 0) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move61 : fU3 (N.to_nat 165953%N) (N.to_nat 371284%N) (N.to_nat 83680%N) (N.to_nat 256667%N) 0 -->* fRG3 (N.to_nat 165956%N) (N.to_nat 371289%N) (N.to_nat 83678%N) 4 (N.to_nat 256667%N).
Proof. eapply tr; [apply progress_evstep; exact (uexit0 (N.to_nat 165953%N) (N.to_nat 371282%N) (N.to_nat 83674%N) (N.to_nat 256657%N)) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move62 : fRG3 (N.to_nat 165956%N) (N.to_nat 371289%N) (N.to_nat 83678%N) 4 (N.to_nat 256667%N) -->* fRG3 (N.to_nat 165956%N) (N.to_nat 371289%N) (N.to_nat 83678%N) (N.to_nat 256670%N) 1.
Proof. eapply tr; [exact (g3cyc_iter (N.to_nat 256666%N) (N.to_nat 165956%N) (N.to_nat 371289%N) (N.to_nat 83678%N) 4 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move63 : fRG3 (N.to_nat 165956%N) (N.to_nat 371289%N) (N.to_nat 83678%N) (N.to_nat 256670%N) 1 -->* fT2 (N.to_nat 165959%N) (N.to_nat 371298%N) (N.to_nat 83684%N) (N.to_nat 128334%N).
Proof. eapply tr; [apply progress_evstep; exact (g3end_ (N.to_nat 165956%N) (N.to_nat 371289%N) (N.to_nat 83674%N) (N.to_nat 128333%N)) | apply fRG3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move64 : fT2 (N.to_nat 165959%N) (N.to_nat 371298%N) (N.to_nat 83684%N) (N.to_nat 128334%N) -->* fT2 (N.to_nat 358460%N) (N.to_nat 820467%N) (N.to_nat 404519%N) 0.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 64167%N) (N.to_nat 165959%N) (N.to_nat 371292%N) (N.to_nat 83678%N) 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move65 : fT2 (N.to_nat 358460%N) (N.to_nat 820467%N) (N.to_nat 404519%N) 0 -->* fRG (N.to_nat 358463%N) (N.to_nat 820466%N) 4 (N.to_nat 404515%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 (N.to_nat 358460%N) (N.to_nat 820465%N) (N.to_nat 404509%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move66 : fRG (N.to_nat 358463%N) (N.to_nat 820466%N) 4 (N.to_nat 404515%N) -->* fRG (N.to_nat 358463%N) (N.to_nat 820466%N) (N.to_nat 404518%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 404514%N) (N.to_nat 358463%N) (N.to_nat 820466%N) 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move67 : fRG (N.to_nat 358463%N) (N.to_nat 820466%N) (N.to_nat 404518%N) 1 -->* fO (N.to_nat 358462%N) (N.to_nat 820475%N) (N.to_nat 202260%N).
Proof. eapply tr; [apply progress_evstep; exact (gend_ (N.to_nat 358461%N) (N.to_nat 820466%N) (N.to_nat 202259%N)) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move68 : fO (N.to_nat 358462%N) (N.to_nat 820475%N) (N.to_nat 202260%N) -->* fS1 (N.to_nat 358463%N) (N.to_nat 820475%N) (N.to_nat 202258%N).
Proof. eapply tr; [apply progress_evstep; exact (oentry (N.to_nat 358462%N) (N.to_nat 820469%N) (N.to_nat 202258%N)) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move69 : fS1 (N.to_nat 358463%N) (N.to_nat 820475%N) (N.to_nat 202258%N) -->* fS1 (N.to_nat 661850%N) (N.to_nat 2034023%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 101129%N) (N.to_nat 358463%N) (N.to_nat 820473%N) 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move70 : fS1 (N.to_nat 661850%N) (N.to_nat 2034023%N) 0 -->* fRF (N.to_nat 661853%N) 4 (N.to_nat 2034030%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 661850%N) (N.to_nat 2034020%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move71 : fRF (N.to_nat 661853%N) 4 (N.to_nat 2034030%N) -->* fRF (N.to_nat 661853%N) (N.to_nat 2034033%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 2034029%N) (N.to_nat 661853%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move72 : fRF (N.to_nat 661853%N) (N.to_nat 2034033%N) 1 -->* fEF (N.to_nat 661853%N) (N.to_nat 1017016%N).
Proof. eapply tr; [apply progress_evstep; exact (rend_ (N.to_nat 661853%N) (N.to_nat 1017016%N)) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move73 : fEF (N.to_nat 661853%N) (N.to_nat 1017016%N) -->* fT3 5 14 (N.to_nat 661846%N) 8 7 (N.to_nat 1017013%N).
Proof. eapply tr; [apply progress_evstep; exact (eentry (N.to_nat 661846%N) (N.to_nat 1017011%N)) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move74 : fT3 5 14 (N.to_nat 661846%N) 8 7 (N.to_nat 1017013%N) -->* fT3 (N.to_nat 529481%N) (N.to_nat 1058966%N) 1 (N.to_nat 926591%N) (N.to_nat 661852%N) (N.to_nat 752275%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 132369%N) 5 8 1 2 1 (N.to_nat 752275%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move75 : fT3 (N.to_nat 529481%N) (N.to_nat 1058966%N) 1 (N.to_nat 926591%N) (N.to_nat 661852%N) (N.to_nat 752275%N) -->* fU3 (N.to_nat 529483%N) (N.to_nat 1058966%N) (N.to_nat 926592%N) (N.to_nat 661857%N) (N.to_nat 752273%N).
Proof. eapply tr; [apply progress_evstep; exact (texit1 (N.to_nat 529481%N) (N.to_nat 752273%N) (N.to_nat 1058960%N) (N.to_nat 926586%N) (N.to_nat 661846%N)) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move76 : fU3 (N.to_nat 529483%N) (N.to_nat 1058966%N) (N.to_nat 926592%N) (N.to_nat 661857%N) (N.to_nat 752273%N) -->* fU3 (N.to_nat 1657891%N) (N.to_nat 3691918%N) (N.to_nat 926592%N) (N.to_nat 2542537%N) 1.
Proof. eapply tr; [exact (ucyc_iter (N.to_nat 376136%N) (N.to_nat 529483%N) (N.to_nat 1058964%N) (N.to_nat 926586%N) (N.to_nat 661851%N) 1) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move77 : fU3 (N.to_nat 1657891%N) (N.to_nat 3691918%N) (N.to_nat 926592%N) (N.to_nat 2542537%N) 1 -->* fRG3 (N.to_nat 1657894%N) (N.to_nat 3691923%N) (N.to_nat 926590%N) 5 (N.to_nat 2542536%N).
Proof. eapply tr; [apply progress_evstep; exact (uexit1 (N.to_nat 1657891%N) (N.to_nat 3691916%N) (N.to_nat 926586%N) (N.to_nat 2542525%N)) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move78 : fRG3 (N.to_nat 1657894%N) (N.to_nat 3691923%N) (N.to_nat 926590%N) 5 (N.to_nat 2542536%N) -->* fRG3 (N.to_nat 1657894%N) (N.to_nat 3691923%N) (N.to_nat 926590%N) (N.to_nat 2542540%N) 1.
Proof. eapply tr; [exact (g3cyc_iter (N.to_nat 2542535%N) (N.to_nat 1657894%N) (N.to_nat 3691923%N) (N.to_nat 926590%N) 5 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move79 : fRG3 (N.to_nat 1657894%N) (N.to_nat 3691923%N) (N.to_nat 926590%N) (N.to_nat 2542540%N) 1 -->* fT2 (N.to_nat 1657897%N) (N.to_nat 3691932%N) (N.to_nat 926596%N) (N.to_nat 1271269%N).
Proof. eapply tr; [apply progress_evstep; exact (g3end_ (N.to_nat 1657894%N) (N.to_nat 3691923%N) (N.to_nat 926586%N) (N.to_nat 1271268%N)) | apply fRG3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move80 : fT2 (N.to_nat 1657897%N) (N.to_nat 3691932%N) (N.to_nat 926596%N) (N.to_nat 1271269%N) -->* fT2 (N.to_nat 3564799%N) (N.to_nat 8141370%N) (N.to_nat 4104766%N) 1.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 635634%N) (N.to_nat 1657897%N) (N.to_nat 3691926%N) (N.to_nat 926590%N) 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move81 : fT2 (N.to_nat 3564799%N) (N.to_nat 8141370%N) (N.to_nat 4104766%N) 1 -->* fRG (N.to_nat 3564802%N) (N.to_nat 8141369%N) 5 (N.to_nat 4104761%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 3564799%N) (N.to_nat 8141368%N) (N.to_nat 4104754%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move82 : fRG (N.to_nat 3564802%N) (N.to_nat 8141369%N) 5 (N.to_nat 4104761%N) -->* fRG (N.to_nat 3564802%N) (N.to_nat 8141369%N) (N.to_nat 4104765%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 4104760%N) (N.to_nat 3564802%N) (N.to_nat 8141369%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move83 : fRG (N.to_nat 3564802%N) (N.to_nat 8141369%N) (N.to_nat 4104765%N) 1 -->* fT3 1 6 (N.to_nat 3564799%N) 11 (N.to_nat 8141377%N) (N.to_nat 2052380%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 3564799%N) (N.to_nat 8141363%N) (N.to_nat 2052379%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move84 : fT3 1 6 (N.to_nat 3564799%N) 11 (N.to_nat 8141377%N) (N.to_nat 2052380%N) -->* fT3 (N.to_nat 2851837%N) (N.to_nat 5703678%N) 4 (N.to_nat 4990724%N) (N.to_nat 11706172%N) (N.to_nat 626462%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 712959%N) 1 0 4 5 (N.to_nat 8141371%N) (N.to_nat 626462%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move85 : fT3 (N.to_nat 2851837%N) (N.to_nat 5703678%N) 4 (N.to_nat 4990724%N) (N.to_nat 11706172%N) (N.to_nat 626462%N) -->* fT2 (N.to_nat 2851842%N) (N.to_nat 10694414%N) (N.to_nat 11706181%N) (N.to_nat 626460%N).
Proof. eapply tr; [apply progress_evstep; exact (texit4 (N.to_nat 2851837%N) (N.to_nat 626459%N) (N.to_nat 5703672%N) (N.to_nat 4990719%N) (N.to_nat 11706166%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move86 : fT2 (N.to_nat 2851842%N) (N.to_nat 10694414%N) (N.to_nat 11706181%N) (N.to_nat 626460%N) -->* fT2 (N.to_nat 3791532%N) (N.to_nat 12887024%N) (N.to_nat 13272331%N) 0.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 313230%N) (N.to_nat 2851842%N) (N.to_nat 10694408%N) (N.to_nat 11706175%N) 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move87 : fT2 (N.to_nat 3791532%N) (N.to_nat 12887024%N) (N.to_nat 13272331%N) 0 -->* fRG (N.to_nat 3791535%N) (N.to_nat 12887023%N) 4 (N.to_nat 13272327%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 (N.to_nat 3791532%N) (N.to_nat 12887022%N) (N.to_nat 13272321%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move88 : fRG (N.to_nat 3791535%N) (N.to_nat 12887023%N) 4 (N.to_nat 13272327%N) -->* fRG (N.to_nat 3791535%N) (N.to_nat 12887023%N) (N.to_nat 13272330%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 13272326%N) (N.to_nat 3791535%N) (N.to_nat 12887023%N) 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move89 : fRG (N.to_nat 3791535%N) (N.to_nat 12887023%N) (N.to_nat 13272330%N) 1 -->* fO (N.to_nat 3791534%N) (N.to_nat 12887032%N) (N.to_nat 6636166%N).
Proof. eapply tr; [apply progress_evstep; exact (gend_ (N.to_nat 3791533%N) (N.to_nat 12887023%N) (N.to_nat 6636165%N)) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move90 : fO (N.to_nat 3791534%N) (N.to_nat 12887032%N) (N.to_nat 6636166%N) -->* fS1 (N.to_nat 3791535%N) (N.to_nat 12887032%N) (N.to_nat 6636164%N).
Proof. eapply tr; [apply progress_evstep; exact (oentry (N.to_nat 3791534%N) (N.to_nat 12887026%N) (N.to_nat 6636164%N)) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move91 : fS1 (N.to_nat 3791535%N) (N.to_nat 12887032%N) (N.to_nat 6636164%N) -->* fS1 (N.to_nat 13745781%N) (N.to_nat 52704016%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 3318082%N) (N.to_nat 3791535%N) (N.to_nat 12887030%N) 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move92 : fS1 (N.to_nat 13745781%N) (N.to_nat 52704016%N) 0 -->* fRF (N.to_nat 13745784%N) 4 (N.to_nat 52704023%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 13745781%N) (N.to_nat 52704013%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move93 : fRF (N.to_nat 13745784%N) 4 (N.to_nat 52704023%N) -->* fRF (N.to_nat 13745784%N) (N.to_nat 52704026%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 52704022%N) (N.to_nat 13745784%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move94 : fRF (N.to_nat 13745784%N) (N.to_nat 52704026%N) 1 -->* fO (N.to_nat 13745784%N) 0 (N.to_nat 26352014%N).
Proof. eapply tr; [apply progress_evstep; exact (rende_ (N.to_nat 13745784%N) (N.to_nat 26352013%N)) | apply fRF_eq; lia | apply fO_eq; lia]. Qed.
Lemma move95 : fO (N.to_nat 13745784%N) 0 (N.to_nat 26352014%N) -->* fT3 (N.to_nat 13745786%N) 0 0 0 7 (N.to_nat 26352011%N).
Proof. eapply tr; [apply progress_evstep; exact (ozero (N.to_nat 13745784%N) (N.to_nat 26352011%N)) | apply fO_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move96 : fT3 (N.to_nat 13745786%N) 0 0 0 7 (N.to_nat 26352011%N) -->* fS1 (N.to_nat 13745786%N) 7 (N.to_nat 26352011%N).
Proof. rewrite (t3_s1 (N.to_nat 13745786%N) (N.to_nat 26352011%N) 7). apply evstep_refl. Qed.
Lemma move97 : fS1 (N.to_nat 13745786%N) 7 (N.to_nat 26352011%N) -->* fS1 (N.to_nat 53273801%N) (N.to_nat 158112067%N) 1.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 13176005%N) (N.to_nat 13745786%N) 5 1) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move98 : fS1 (N.to_nat 53273801%N) (N.to_nat 158112067%N) 1 -->* fRF (N.to_nat 53273804%N) 5 (N.to_nat 158112073%N).
Proof. eapply tr; [apply progress_evstep; exact (oexit (N.to_nat 53273801%N) (N.to_nat 158112061%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move99 : fRF (N.to_nat 53273804%N) 5 (N.to_nat 158112073%N) -->* fRF (N.to_nat 53273804%N) (N.to_nat 158112077%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 158112072%N) (N.to_nat 53273804%N) 5 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move100 : fRF (N.to_nat 53273804%N) (N.to_nat 158112077%N) 1 -->* fEF (N.to_nat 53273804%N) (N.to_nat 79056038%N).
Proof. eapply tr; [apply progress_evstep; exact (rend_ (N.to_nat 53273804%N) (N.to_nat 79056038%N)) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move101 : fEF (N.to_nat 53273804%N) (N.to_nat 79056038%N) -->* fT3 5 14 (N.to_nat 53273797%N) 8 7 (N.to_nat 79056035%N).
Proof. eapply tr; [apply progress_evstep; exact (eentry (N.to_nat 53273797%N) (N.to_nat 79056033%N)) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move102 : fT3 5 14 (N.to_nat 53273797%N) 8 7 (N.to_nat 79056035%N) -->* fT3 (N.to_nat 42619041%N) (N.to_nat 85238086%N) 2 (N.to_nat 74583321%N) (N.to_nat 53273802%N) (N.to_nat 57746517%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 10654759%N) 5 8 2 2 1 (N.to_nat 57746517%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move103 : fT3 (N.to_nat 42619041%N) (N.to_nat 85238086%N) 2 (N.to_nat 74583321%N) (N.to_nat 53273802%N) (N.to_nat 57746517%N) -->* fU3 (N.to_nat 42619043%N) (N.to_nat 85238088%N) (N.to_nat 74583322%N) (N.to_nat 53273807%N) (N.to_nat 57746515%N).
Proof. eapply tr; [apply progress_evstep; exact (texit2 (N.to_nat 42619041%N) (N.to_nat 57746515%N) (N.to_nat 85238080%N) (N.to_nat 74583316%N) (N.to_nat 53273796%N)) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move104 : fU3 (N.to_nat 42619043%N) (N.to_nat 85238088%N) (N.to_nat 74583322%N) (N.to_nat 53273807%N) (N.to_nat 57746515%N) -->* fU3 (N.to_nat 129238814%N) (N.to_nat 287350887%N) (N.to_nat 74583322%N) (N.to_nat 197640092%N) 1.
Proof. eapply tr; [exact (ucyc_iter (N.to_nat 28873257%N) (N.to_nat 42619043%N) (N.to_nat 85238086%N) (N.to_nat 74583316%N) (N.to_nat 53273801%N) 1) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move105 : fU3 (N.to_nat 129238814%N) (N.to_nat 287350887%N) (N.to_nat 74583322%N) (N.to_nat 197640092%N) 1 -->* fRG3 (N.to_nat 129238817%N) (N.to_nat 287350892%N) (N.to_nat 74583320%N) 5 (N.to_nat 197640091%N).
Proof. eapply tr; [apply progress_evstep; exact (uexit1 (N.to_nat 129238814%N) (N.to_nat 287350885%N) (N.to_nat 74583316%N) (N.to_nat 197640080%N)) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move106 : fRG3 (N.to_nat 129238817%N) (N.to_nat 287350892%N) (N.to_nat 74583320%N) 5 (N.to_nat 197640091%N) -->* fRG3 (N.to_nat 129238817%N) (N.to_nat 287350892%N) (N.to_nat 74583320%N) (N.to_nat 197640095%N) 1.
Proof. eapply tr; [exact (g3cyc_iter (N.to_nat 197640090%N) (N.to_nat 129238817%N) (N.to_nat 287350892%N) (N.to_nat 74583320%N) 5 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move107 : fRG3 (N.to_nat 129238817%N) (N.to_nat 287350892%N) (N.to_nat 74583320%N) (N.to_nat 197640095%N) 1 -->* fT3 5 14 (N.to_nat 129238810%N) 15 (N.to_nat 361934217%N) (N.to_nat 98820045%N).
Proof. eapply tr; [apply progress_evstep; exact (g3endo_ (N.to_nat 129238810%N) (N.to_nat 287350882%N) (N.to_nat 74583318%N) (N.to_nat 98820044%N)) | apply fRG3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move108 : fT3 5 14 (N.to_nat 129238810%N) 15 (N.to_nat 361934217%N) (N.to_nat 98820045%N) -->* fT3 (N.to_nat 103391053%N) (N.to_nat 206782110%N) 0 (N.to_nat 180934349%N) (N.to_nat 491173027%N) (N.to_nat 47124521%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 25847762%N) 5 8 0 9 (N.to_nat 361934211%N) (N.to_nat 47124521%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move109 : fT3 (N.to_nat 103391053%N) (N.to_nat 206782110%N) 0 (N.to_nat 180934349%N) (N.to_nat 491173027%N) (N.to_nat 47124521%N) -->* fT2 (N.to_nat 103391054%N) (N.to_nat 387716458%N) (N.to_nat 491173031%N) (N.to_nat 47124521%N).
Proof. eapply tr; [apply progress_evstep; exact (texit0 (N.to_nat 103391053%N) (N.to_nat 47124520%N) (N.to_nat 206782105%N) (N.to_nat 180934347%N) (N.to_nat 491173025%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move110 : fT2 (N.to_nat 103391054%N) (N.to_nat 387716458%N) (N.to_nat 491173031%N) (N.to_nat 47124521%N) -->* fT2 (N.to_nat 174077834%N) (N.to_nat 552652278%N) (N.to_nat 608984331%N) 1.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 23562260%N) (N.to_nat 103391054%N) (N.to_nat 387716452%N) (N.to_nat 491173025%N) 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move111 : fT2 (N.to_nat 174077834%N) (N.to_nat 552652278%N) (N.to_nat 608984331%N) 1 -->* fRG (N.to_nat 174077837%N) (N.to_nat 552652277%N) 5 (N.to_nat 608984326%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 174077834%N) (N.to_nat 552652276%N) (N.to_nat 608984319%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move112 : fRG (N.to_nat 174077837%N) (N.to_nat 552652277%N) 5 (N.to_nat 608984326%N) -->* fRG (N.to_nat 174077837%N) (N.to_nat 552652277%N) (N.to_nat 608984330%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 608984325%N) (N.to_nat 174077837%N) (N.to_nat 552652277%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move113 : fRG (N.to_nat 174077837%N) (N.to_nat 552652277%N) (N.to_nat 608984330%N) 1 -->* fO (N.to_nat 174077836%N) (N.to_nat 552652286%N) (N.to_nat 304492166%N).
Proof. eapply tr; [apply progress_evstep; exact (gend_ (N.to_nat 174077835%N) (N.to_nat 552652277%N) (N.to_nat 304492165%N)) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move114 : fO (N.to_nat 174077836%N) (N.to_nat 552652286%N) (N.to_nat 304492166%N) -->* fS1 (N.to_nat 174077837%N) (N.to_nat 552652286%N) (N.to_nat 304492164%N).
Proof. eapply tr; [apply progress_evstep; exact (oentry (N.to_nat 174077836%N) (N.to_nat 552652280%N) (N.to_nat 304492164%N)) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move115 : fS1 (N.to_nat 174077837%N) (N.to_nat 552652286%N) (N.to_nat 304492164%N) -->* fS1 (N.to_nat 630816083%N) (N.to_nat 2379605270%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 152246082%N) (N.to_nat 174077837%N) (N.to_nat 552652284%N) 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move116 : fS1 (N.to_nat 630816083%N) (N.to_nat 2379605270%N) 0 -->* fRF (N.to_nat 630816086%N) 4 (N.to_nat 2379605277%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 630816083%N) (N.to_nat 2379605267%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move117 : fRF (N.to_nat 630816086%N) 4 (N.to_nat 2379605277%N) -->* fRF (N.to_nat 630816086%N) (N.to_nat 2379605280%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 2379605276%N) (N.to_nat 630816086%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move118 : fRF (N.to_nat 630816086%N) (N.to_nat 2379605280%N) 1 -->* fO (N.to_nat 630816086%N) 0 (N.to_nat 1189802641%N).
Proof. eapply tr; [apply progress_evstep; exact (rende_ (N.to_nat 630816086%N) (N.to_nat 1189802640%N)) | apply fRF_eq; lia | apply fO_eq; lia]. Qed.
Lemma move119 : fO (N.to_nat 630816086%N) 0 (N.to_nat 1189802641%N) -->* fT3 (N.to_nat 630816088%N) 0 0 0 7 (N.to_nat 1189802638%N).
Proof. eapply tr; [apply progress_evstep; exact (ozero (N.to_nat 630816086%N) (N.to_nat 1189802638%N)) | apply fO_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move120 : fT3 (N.to_nat 630816088%N) 0 0 0 7 (N.to_nat 1189802638%N) -->* fS1 (N.to_nat 630816088%N) 7 (N.to_nat 1189802638%N).
Proof. rewrite (t3_s1 (N.to_nat 630816088%N) (N.to_nat 1189802638%N) 7). apply evstep_refl. Qed.
Lemma move121 : fS1 (N.to_nat 630816088%N) 7 (N.to_nat 1189802638%N) -->* fS1 (N.to_nat 2415520045%N) (N.to_nat 7138815835%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 594901319%N) (N.to_nat 630816088%N) 5 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move122 : fS1 (N.to_nat 2415520045%N) (N.to_nat 7138815835%N) 0 -->* fRF (N.to_nat 2415520048%N) 4 (N.to_nat 7138815842%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 2415520045%N) (N.to_nat 7138815832%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move123 : fRF (N.to_nat 2415520048%N) 4 (N.to_nat 7138815842%N) -->* fRF (N.to_nat 2415520048%N) (N.to_nat 7138815845%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 7138815841%N) (N.to_nat 2415520048%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move124 : fRF (N.to_nat 2415520048%N) (N.to_nat 7138815845%N) 1 -->* fEF (N.to_nat 2415520048%N) (N.to_nat 3569407922%N).
Proof. eapply tr; [apply progress_evstep; exact (rend_ (N.to_nat 2415520048%N) (N.to_nat 3569407922%N)) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move125 : fEF (N.to_nat 2415520048%N) (N.to_nat 3569407922%N) -->* fT3 5 14 (N.to_nat 2415520041%N) 8 7 (N.to_nat 3569407919%N).
Proof. eapply tr; [apply progress_evstep; exact (eentry (N.to_nat 2415520041%N) (N.to_nat 3569407917%N)) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move126 : fT3 5 14 (N.to_nat 2415520041%N) 8 7 (N.to_nat 3569407919%N) -->* fT3 (N.to_nat 1932416037%N) (N.to_nat 3864832078%N) 1 (N.to_nat 3381728064%N) (N.to_nat 2415520047%N) (N.to_nat 2603199903%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 483104008%N) 5 8 1 2 1 (N.to_nat 2603199903%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move127 : fT3 (N.to_nat 1932416037%N) (N.to_nat 3864832078%N) 1 (N.to_nat 3381728064%N) (N.to_nat 2415520047%N) (N.to_nat 2603199903%N) -->* fU3 (N.to_nat 1932416039%N) (N.to_nat 3864832078%N) (N.to_nat 3381728065%N) (N.to_nat 2415520052%N) (N.to_nat 2603199901%N).
Proof. eapply tr; [apply progress_evstep; exact (texit1 (N.to_nat 1932416037%N) (N.to_nat 2603199901%N) (N.to_nat 3864832072%N) (N.to_nat 3381728059%N) (N.to_nat 2415520041%N)) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move128 : fU3 (N.to_nat 1932416039%N) (N.to_nat 3864832078%N) (N.to_nat 3381728065%N) (N.to_nat 2415520052%N) (N.to_nat 2603199901%N) -->* fU3 (N.to_nat 5837215889%N) (N.to_nat 12976031728%N) (N.to_nat 3381728065%N) (N.to_nat 8923519802%N) 1.
Proof. eapply tr; [exact (ucyc_iter (N.to_nat 1301599950%N) (N.to_nat 1932416039%N) (N.to_nat 3864832076%N) (N.to_nat 3381728059%N) (N.to_nat 2415520046%N) 1) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move129 : fU3 (N.to_nat 5837215889%N) (N.to_nat 12976031728%N) (N.to_nat 3381728065%N) (N.to_nat 8923519802%N) 1 -->* fRG3 (N.to_nat 5837215892%N) (N.to_nat 12976031733%N) (N.to_nat 3381728063%N) 5 (N.to_nat 8923519801%N).
Proof. eapply tr; [apply progress_evstep; exact (uexit1 (N.to_nat 5837215889%N) (N.to_nat 12976031726%N) (N.to_nat 3381728059%N) (N.to_nat 8923519790%N)) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move130 : fRG3 (N.to_nat 5837215892%N) (N.to_nat 12976031733%N) (N.to_nat 3381728063%N) 5 (N.to_nat 8923519801%N) -->* fRG3 (N.to_nat 5837215892%N) (N.to_nat 12976031733%N) (N.to_nat 3381728063%N) (N.to_nat 8923519805%N) 1.
Proof. eapply tr; [exact (g3cyc_iter (N.to_nat 8923519800%N) (N.to_nat 5837215892%N) (N.to_nat 12976031733%N) (N.to_nat 3381728063%N) 5 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move131 : fRG3 (N.to_nat 5837215892%N) (N.to_nat 12976031733%N) (N.to_nat 3381728063%N) (N.to_nat 8923519805%N) 1 -->* fT3 5 14 (N.to_nat 5837215885%N) 15 (N.to_nat 16357759801%N) (N.to_nat 4461759900%N).
Proof. eapply tr; [apply progress_evstep; exact (g3endo_ (N.to_nat 5837215885%N) (N.to_nat 12976031723%N) (N.to_nat 3381728061%N) (N.to_nat 4461759899%N)) | apply fRG3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move132 : fT3 5 14 (N.to_nat 5837215885%N) 15 (N.to_nat 16357759801%N) (N.to_nat 4461759900%N) -->* fT3 (N.to_nat 4669772713%N) (N.to_nat 9339545430%N) 0 (N.to_nat 8172102254%N) (N.to_nat 22194975686%N) (N.to_nat 2126873546%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 1167443177%N) 5 8 0 9 (N.to_nat 16357759795%N) (N.to_nat 2126873546%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move133 : fT3 (N.to_nat 4669772713%N) (N.to_nat 9339545430%N) 0 (N.to_nat 8172102254%N) (N.to_nat 22194975686%N) (N.to_nat 2126873546%N) -->* fT2 (N.to_nat 4669772714%N) (N.to_nat 17511647683%N) (N.to_nat 22194975690%N) (N.to_nat 2126873546%N).
Proof. eapply tr; [apply progress_evstep; exact (texit0 (N.to_nat 4669772713%N) (N.to_nat 2126873545%N) (N.to_nat 9339545425%N) (N.to_nat 8172102252%N) (N.to_nat 22194975684%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move134 : fT2 (N.to_nat 4669772714%N) (N.to_nat 17511647683%N) (N.to_nat 22194975690%N) (N.to_nat 2126873546%N) -->* fT2 (N.to_nat 7860083033%N) (N.to_nat 24955705094%N) (N.to_nat 27512159555%N) 0.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 1063436773%N) (N.to_nat 4669772714%N) (N.to_nat 17511647677%N) (N.to_nat 22194975684%N) 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move135 : fT2 (N.to_nat 7860083033%N) (N.to_nat 24955705094%N) (N.to_nat 27512159555%N) 0 -->* fRG (N.to_nat 7860083036%N) (N.to_nat 24955705093%N) 4 (N.to_nat 27512159551%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 (N.to_nat 7860083033%N) (N.to_nat 24955705092%N) (N.to_nat 27512159545%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move136 : fRG (N.to_nat 7860083036%N) (N.to_nat 24955705093%N) 4 (N.to_nat 27512159551%N) -->* fRG (N.to_nat 7860083036%N) (N.to_nat 24955705093%N) (N.to_nat 27512159554%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 27512159550%N) (N.to_nat 7860083036%N) (N.to_nat 24955705093%N) 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move137 : fRG (N.to_nat 7860083036%N) (N.to_nat 24955705093%N) (N.to_nat 27512159554%N) 1 -->* fO (N.to_nat 7860083035%N) (N.to_nat 24955705102%N) (N.to_nat 13756079778%N).
Proof. eapply tr; [apply progress_evstep; exact (gend_ (N.to_nat 7860083034%N) (N.to_nat 24955705093%N) (N.to_nat 13756079777%N)) | apply fRG_eq; lia | apply fO_eq; lia]. Qed.
Lemma move138 : fO (N.to_nat 7860083035%N) (N.to_nat 24955705102%N) (N.to_nat 13756079778%N) -->* fS1 (N.to_nat 7860083036%N) (N.to_nat 24955705102%N) (N.to_nat 13756079776%N).
Proof. eapply tr; [apply progress_evstep; exact (oentry (N.to_nat 7860083035%N) (N.to_nat 24955705096%N) (N.to_nat 13756079776%N)) | apply fO_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move139 : fS1 (N.to_nat 7860083036%N) (N.to_nat 24955705102%N) (N.to_nat 13756079776%N) -->* fS1 (N.to_nat 28494202700%N) (N.to_nat 107492183758%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 6878039888%N) (N.to_nat 7860083036%N) (N.to_nat 24955705100%N) 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move140 : fS1 (N.to_nat 28494202700%N) (N.to_nat 107492183758%N) 0 -->* fRF (N.to_nat 28494202703%N) 4 (N.to_nat 107492183765%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 28494202700%N) (N.to_nat 107492183755%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move141 : fRF (N.to_nat 28494202703%N) 4 (N.to_nat 107492183765%N) -->* fRF (N.to_nat 28494202703%N) (N.to_nat 107492183768%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 107492183764%N) (N.to_nat 28494202703%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move142 : fRF (N.to_nat 28494202703%N) (N.to_nat 107492183768%N) 1 -->* fO (N.to_nat 28494202703%N) 0 (N.to_nat 53746091885%N).
Proof. eapply tr; [apply progress_evstep; exact (rende_ (N.to_nat 28494202703%N) (N.to_nat 53746091884%N)) | apply fRF_eq; lia | apply fO_eq; lia]. Qed.
Lemma move143 : fO (N.to_nat 28494202703%N) 0 (N.to_nat 53746091885%N) -->* fT3 (N.to_nat 28494202705%N) 0 0 0 7 (N.to_nat 53746091882%N).
Proof. eapply tr; [apply progress_evstep; exact (ozero (N.to_nat 28494202703%N) (N.to_nat 53746091882%N)) | apply fO_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move144 : fT3 (N.to_nat 28494202705%N) 0 0 0 7 (N.to_nat 53746091882%N) -->* fS1 (N.to_nat 28494202705%N) 7 (N.to_nat 53746091882%N).
Proof. rewrite (t3_s1 (N.to_nat 28494202705%N) (N.to_nat 53746091882%N) 7). apply evstep_refl. Qed.
Lemma move145 : fS1 (N.to_nat 28494202705%N) 7 (N.to_nat 53746091882%N) -->* fS1 (N.to_nat 109113340528%N) (N.to_nat 322476551299%N) 0.
Proof. eapply tr; [exact (cycle_iter (N.to_nat 26873045941%N) (N.to_nat 28494202705%N) 5 0) | apply fS1_eq; lia | apply fS1_eq; lia]. Qed.
Lemma move146 : fS1 (N.to_nat 109113340528%N) (N.to_nat 322476551299%N) 0 -->* fRF (N.to_nat 109113340531%N) 4 (N.to_nat 322476551306%N).
Proof. eapply tr; [apply progress_evstep; exact (sexit0 (N.to_nat 109113340528%N) (N.to_nat 322476551296%N)) | apply fS1_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move147 : fRF (N.to_nat 109113340531%N) 4 (N.to_nat 322476551306%N) -->* fRF (N.to_nat 109113340531%N) (N.to_nat 322476551309%N) 1.
Proof. eapply tr; [exact (rcyc_iter (N.to_nat 322476551305%N) (N.to_nat 109113340531%N) 4 0) | apply fRF_eq; lia | apply fRF_eq; lia]. Qed.
Lemma move148 : fRF (N.to_nat 109113340531%N) (N.to_nat 322476551309%N) 1 -->* fEF (N.to_nat 109113340531%N) (N.to_nat 161238275654%N).
Proof. eapply tr; [apply progress_evstep; exact (rend_ (N.to_nat 109113340531%N) (N.to_nat 161238275654%N)) | apply fRF_eq; lia | apply fEF_eq; lia]. Qed.
Lemma move149 : fEF (N.to_nat 109113340531%N) (N.to_nat 161238275654%N) -->* fT3 5 14 (N.to_nat 109113340524%N) 8 7 (N.to_nat 161238275651%N).
Proof. eapply tr; [apply progress_evstep; exact (eentry (N.to_nat 109113340524%N) (N.to_nat 161238275649%N)) | apply fEF_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move150 : fT3 5 14 (N.to_nat 109113340524%N) 8 7 (N.to_nat 161238275651%N) -->* fT3 (N.to_nat 87290672421%N) (N.to_nat 174581344846%N) 4 (N.to_nat 152758676736%N) (N.to_nat 109113340527%N) (N.to_nat 117592939443%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 21822668104%N) 5 8 4 2 1 (N.to_nat 117592939443%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move151 : fT3 (N.to_nat 87290672421%N) (N.to_nat 174581344846%N) 4 (N.to_nat 152758676736%N) (N.to_nat 109113340527%N) (N.to_nat 117592939443%N) -->* fT2 (N.to_nat 87290672426%N) (N.to_nat 327340021594%N) (N.to_nat 109113340536%N) (N.to_nat 117592939441%N).
Proof. eapply tr; [apply progress_evstep; exact (texit4 (N.to_nat 87290672421%N) (N.to_nat 117592939440%N) (N.to_nat 174581344840%N) (N.to_nat 152758676731%N) (N.to_nat 109113340521%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move152 : fT2 (N.to_nat 87290672426%N) (N.to_nat 327340021594%N) (N.to_nat 109113340536%N) (N.to_nat 117592939441%N) -->* fT2 (N.to_nat 263680081586%N) (N.to_nat 738915309634%N) (N.to_nat 403095689136%N) 1.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 58796469720%N) (N.to_nat 87290672426%N) (N.to_nat 327340021588%N) (N.to_nat 109113340530%N) 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move153 : fT2 (N.to_nat 263680081586%N) (N.to_nat 738915309634%N) (N.to_nat 403095689136%N) 1 -->* fRG (N.to_nat 263680081589%N) (N.to_nat 738915309633%N) 5 (N.to_nat 403095689131%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 263680081586%N) (N.to_nat 738915309632%N) (N.to_nat 403095689124%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move154 : fRG (N.to_nat 263680081589%N) (N.to_nat 738915309633%N) 5 (N.to_nat 403095689131%N) -->* fRG (N.to_nat 263680081589%N) (N.to_nat 738915309633%N) (N.to_nat 403095689135%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 403095689130%N) (N.to_nat 263680081589%N) (N.to_nat 738915309633%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move155 : fRG (N.to_nat 263680081589%N) (N.to_nat 738915309633%N) (N.to_nat 403095689135%N) 1 -->* fT3 1 6 (N.to_nat 263680081586%N) 11 (N.to_nat 738915309641%N) (N.to_nat 201547844565%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 263680081586%N) (N.to_nat 738915309627%N) (N.to_nat 201547844564%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move156 : fT3 1 6 (N.to_nat 263680081586%N) 11 (N.to_nat 738915309641%N) (N.to_nat 201547844565%N) -->* fT3 (N.to_nat 210944065269%N) (N.to_nat 421888130542%N) 1 (N.to_nat 369152114230%N) (N.to_nat 1002595391226%N) (N.to_nat 96075811931%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 52736016317%N) 1 0 1 5 (N.to_nat 738915309635%N) (N.to_nat 96075811931%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move157 : fT3 (N.to_nat 210944065269%N) (N.to_nat 421888130542%N) 1 (N.to_nat 369152114230%N) (N.to_nat 1002595391226%N) (N.to_nat 96075811931%N) -->* fU3 (N.to_nat 210944065271%N) (N.to_nat 421888130542%N) (N.to_nat 369152114231%N) (N.to_nat 1002595391231%N) (N.to_nat 96075811929%N).
Proof. eapply tr; [apply progress_evstep; exact (texit1 (N.to_nat 210944065269%N) (N.to_nat 96075811929%N) (N.to_nat 421888130536%N) (N.to_nat 369152114225%N) (N.to_nat 1002595391220%N)) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move158 : fU3 (N.to_nat 210944065271%N) (N.to_nat 421888130542%N) (N.to_nat 369152114231%N) (N.to_nat 1002595391231%N) (N.to_nat 96075811929%N) -->* fU3 (N.to_nat 355057783163%N) (N.to_nat 758153472290%N) (N.to_nat 369152114231%N) (N.to_nat 1242784921051%N) 1.
Proof. eapply tr; [exact (ucyc_iter (N.to_nat 48037905964%N) (N.to_nat 210944065271%N) (N.to_nat 421888130540%N) (N.to_nat 369152114225%N) (N.to_nat 1002595391225%N) 1) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move159 : fU3 (N.to_nat 355057783163%N) (N.to_nat 758153472290%N) (N.to_nat 369152114231%N) (N.to_nat 1242784921051%N) 1 -->* fRG3 (N.to_nat 355057783166%N) (N.to_nat 758153472295%N) (N.to_nat 369152114229%N) 5 (N.to_nat 1242784921050%N).
Proof. eapply tr; [apply progress_evstep; exact (uexit1 (N.to_nat 355057783163%N) (N.to_nat 758153472288%N) (N.to_nat 369152114225%N) (N.to_nat 1242784921039%N)) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move160 : fRG3 (N.to_nat 355057783166%N) (N.to_nat 758153472295%N) (N.to_nat 369152114229%N) 5 (N.to_nat 1242784921050%N) -->* fRG3 (N.to_nat 355057783166%N) (N.to_nat 758153472295%N) (N.to_nat 369152114229%N) (N.to_nat 1242784921054%N) 1.
Proof. eapply tr; [exact (g3cyc_iter (N.to_nat 1242784921049%N) (N.to_nat 355057783166%N) (N.to_nat 758153472295%N) (N.to_nat 369152114229%N) 5 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move161 : fRG3 (N.to_nat 355057783166%N) (N.to_nat 758153472295%N) (N.to_nat 369152114229%N) (N.to_nat 1242784921054%N) 1 -->* fT2 (N.to_nat 355057783169%N) (N.to_nat 758153472304%N) (N.to_nat 369152114235%N) (N.to_nat 621392460526%N).
Proof. eapply tr; [apply progress_evstep; exact (g3end_ (N.to_nat 355057783166%N) (N.to_nat 758153472295%N) (N.to_nat 369152114225%N) (N.to_nat 621392460525%N)) | apply fRG3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move162 : fT2 (N.to_nat 355057783169%N) (N.to_nat 758153472304%N) (N.to_nat 369152114235%N) (N.to_nat 621392460526%N) -->* fT2 (N.to_nat 1287146473958%N) (N.to_nat 2933027084145%N) (N.to_nat 1922633265550%N) 0.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 310696230263%N) (N.to_nat 355057783169%N) (N.to_nat 758153472298%N) (N.to_nat 369152114229%N) 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move163 : fT2 (N.to_nat 1287146473958%N) (N.to_nat 2933027084145%N) (N.to_nat 1922633265550%N) 0 -->* fRG (N.to_nat 1287146473961%N) (N.to_nat 2933027084144%N) 4 (N.to_nat 1922633265546%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 (N.to_nat 1287146473958%N) (N.to_nat 2933027084143%N) (N.to_nat 1922633265540%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move164 : fRG (N.to_nat 1287146473961%N) (N.to_nat 2933027084144%N) 4 (N.to_nat 1922633265546%N) -->* fRG (N.to_nat 1287146473961%N) (N.to_nat 2933027084144%N) (N.to_nat 1922633265549%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 1922633265545%N) (N.to_nat 1287146473961%N) (N.to_nat 2933027084144%N) 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move165 : fRG (N.to_nat 1287146473961%N) (N.to_nat 2933027084144%N) (N.to_nat 1922633265549%N) 1 -->* fT3 1 6 (N.to_nat 1287146473958%N) 11 (N.to_nat 2933027084152%N) (N.to_nat 961316632772%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 1287146473958%N) (N.to_nat 2933027084138%N) (N.to_nat 961316632771%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move166 : fT3 1 6 (N.to_nat 1287146473958%N) 11 (N.to_nat 2933027084152%N) (N.to_nat 961316632772%N) -->* fT3 (N.to_nat 1029717179165%N) (N.to_nat 2059434358334%N) 3 (N.to_nat 1802005063548%N) (N.to_nat 4220173558107%N) (N.to_nat 446458043190%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 257429294791%N) 1 0 3 5 (N.to_nat 2933027084146%N) (N.to_nat 446458043190%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move167 : fT3 (N.to_nat 1029717179165%N) (N.to_nat 2059434358334%N) 3 (N.to_nat 1802005063548%N) (N.to_nat 4220173558107%N) (N.to_nat 446458043190%N) -->* fT2 (N.to_nat 1029717179170%N) (N.to_nat 3861439421892%N) (N.to_nat 4220173558116%N) (N.to_nat 446458043188%N).
Proof. eapply tr; [apply progress_evstep; exact (texit3 (N.to_nat 1029717179165%N) (N.to_nat 446458043187%N) (N.to_nat 2059434358328%N) (N.to_nat 1802005063543%N) (N.to_nat 4220173558101%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move168 : fT2 (N.to_nat 1029717179170%N) (N.to_nat 3861439421892%N) (N.to_nat 4220173558116%N) (N.to_nat 446458043188%N) -->* fT2 (N.to_nat 1699404243952%N) (N.to_nat 5424042573050%N) (N.to_nat 5336318666086%N) 0.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 223229021594%N) (N.to_nat 1029717179170%N) (N.to_nat 3861439421886%N) (N.to_nat 4220173558110%N) 0) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move169 : fT2 (N.to_nat 1699404243952%N) (N.to_nat 5424042573050%N) (N.to_nat 5336318666086%N) 0 -->* fRG (N.to_nat 1699404243955%N) (N.to_nat 5424042573049%N) 4 (N.to_nat 5336318666082%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit0 (N.to_nat 1699404243952%N) (N.to_nat 5424042573048%N) (N.to_nat 5336318666076%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move170 : fRG (N.to_nat 1699404243955%N) (N.to_nat 5424042573049%N) 4 (N.to_nat 5336318666082%N) -->* fRG (N.to_nat 1699404243955%N) (N.to_nat 5424042573049%N) (N.to_nat 5336318666085%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 5336318666081%N) (N.to_nat 1699404243955%N) (N.to_nat 5424042573049%N) 4 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move171 : fRG (N.to_nat 1699404243955%N) (N.to_nat 5424042573049%N) (N.to_nat 5336318666085%N) 1 -->* fT3 1 6 (N.to_nat 1699404243952%N) 11 (N.to_nat 5424042573057%N) (N.to_nat 2668159333040%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 1699404243952%N) (N.to_nat 5424042573043%N) (N.to_nat 2668159333039%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move172 : fT3 1 6 (N.to_nat 1699404243952%N) 11 (N.to_nat 5424042573057%N) (N.to_nat 2668159333040%N) -->* fT3 (N.to_nat 1359523395161%N) (N.to_nat 2719046790326%N) 2 (N.to_nat 2379165941541%N) (N.to_nat 7123446817007%N) (N.to_nat 1988397635460%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 339880848790%N) 1 0 2 5 (N.to_nat 5424042573051%N) (N.to_nat 1988397635460%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move173 : fT3 (N.to_nat 1359523395161%N) (N.to_nat 2719046790326%N) 2 (N.to_nat 2379165941541%N) (N.to_nat 7123446817007%N) (N.to_nat 1988397635460%N) -->* fU3 (N.to_nat 1359523395163%N) (N.to_nat 2719046790328%N) (N.to_nat 2379165941542%N) (N.to_nat 7123446817012%N) (N.to_nat 1988397635458%N).
Proof. eapply tr; [apply progress_evstep; exact (texit2 (N.to_nat 1359523395161%N) (N.to_nat 1988397635458%N) (N.to_nat 2719046790320%N) (N.to_nat 2379165941536%N) (N.to_nat 7123446817001%N)) | apply fT3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move174 : fU3 (N.to_nat 1359523395163%N) (N.to_nat 2719046790328%N) (N.to_nat 2379165941542%N) (N.to_nat 7123446817012%N) (N.to_nat 1988397635458%N) -->* fU3 (N.to_nat 4342119848350%N) (N.to_nat 9678438514431%N) (N.to_nat 2379165941542%N) (N.to_nat 12094440905657%N) 0.
Proof. eapply tr; [exact (ucyc_iter (N.to_nat 994198817729%N) (N.to_nat 1359523395163%N) (N.to_nat 2719046790326%N) (N.to_nat 2379165941536%N) (N.to_nat 7123446817006%N) 0) | apply fU3_eq; lia | apply fU3_eq; lia]. Qed.
Lemma move175 : fU3 (N.to_nat 4342119848350%N) (N.to_nat 9678438514431%N) (N.to_nat 2379165941542%N) (N.to_nat 12094440905657%N) 0 -->* fRG3 (N.to_nat 4342119848353%N) (N.to_nat 9678438514436%N) (N.to_nat 2379165941540%N) 4 (N.to_nat 12094440905657%N).
Proof. eapply tr; [apply progress_evstep; exact (uexit0 (N.to_nat 4342119848350%N) (N.to_nat 9678438514429%N) (N.to_nat 2379165941536%N) (N.to_nat 12094440905647%N)) | apply fU3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move176 : fRG3 (N.to_nat 4342119848353%N) (N.to_nat 9678438514436%N) (N.to_nat 2379165941540%N) 4 (N.to_nat 12094440905657%N) -->* fRG3 (N.to_nat 4342119848353%N) (N.to_nat 9678438514436%N) (N.to_nat 2379165941540%N) (N.to_nat 12094440905660%N) 1.
Proof. eapply tr; [exact (g3cyc_iter (N.to_nat 12094440905656%N) (N.to_nat 4342119848353%N) (N.to_nat 9678438514436%N) (N.to_nat 2379165941540%N) 4 0) | apply fRG3_eq; lia | apply fRG3_eq; lia]. Qed.
Lemma move177 : fRG3 (N.to_nat 4342119848353%N) (N.to_nat 9678438514436%N) (N.to_nat 2379165941540%N) (N.to_nat 12094440905660%N) 1 -->* fT2 (N.to_nat 4342119848356%N) (N.to_nat 9678438514445%N) (N.to_nat 2379165941546%N) (N.to_nat 6047220452829%N).
Proof. eapply tr; [apply progress_evstep; exact (g3end_ (N.to_nat 4342119848353%N) (N.to_nat 9678438514436%N) (N.to_nat 2379165941536%N) (N.to_nat 6047220452828%N)) | apply fRG3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move178 : fT2 (N.to_nat 4342119848356%N) (N.to_nat 9678438514445%N) (N.to_nat 2379165941546%N) (N.to_nat 6047220452829%N) -->* fT2 (N.to_nat 13412950527598%N) (N.to_nat 30843710099343%N) (N.to_nat 17497217073616%N) 1.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 3023610226414%N) (N.to_nat 4342119848356%N) (N.to_nat 9678438514439%N) (N.to_nat 2379165941540%N) 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move179 : fT2 (N.to_nat 13412950527598%N) (N.to_nat 30843710099343%N) (N.to_nat 17497217073616%N) 1 -->* fRG (N.to_nat 13412950527601%N) (N.to_nat 30843710099342%N) 5 (N.to_nat 17497217073611%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 13412950527598%N) (N.to_nat 30843710099341%N) (N.to_nat 17497217073604%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move180 : fRG (N.to_nat 13412950527601%N) (N.to_nat 30843710099342%N) 5 (N.to_nat 17497217073611%N) -->* fRG (N.to_nat 13412950527601%N) (N.to_nat 30843710099342%N) (N.to_nat 17497217073615%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 17497217073610%N) (N.to_nat 13412950527601%N) (N.to_nat 30843710099342%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move181 : fRG (N.to_nat 13412950527601%N) (N.to_nat 30843710099342%N) (N.to_nat 17497217073615%N) 1 -->* fT3 1 6 (N.to_nat 13412950527598%N) 11 (N.to_nat 30843710099350%N) (N.to_nat 8748608536805%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 13412950527598%N) (N.to_nat 30843710099336%N) (N.to_nat 8748608536804%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move182 : fT3 1 6 (N.to_nat 13412950527598%N) 11 (N.to_nat 30843710099350%N) (N.to_nat 8748608536805%N) -->* fT3 (N.to_nat 10730360422077%N) (N.to_nat 21460720844158%N) 3 (N.to_nat 18778130738644%N) (N.to_nat 44256660626945%N) (N.to_nat 3383428325767%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 2682590105519%N) 1 0 3 5 (N.to_nat 30843710099344%N) (N.to_nat 3383428325767%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move183 : fT3 (N.to_nat 10730360422077%N) (N.to_nat 21460720844158%N) 3 (N.to_nat 18778130738644%N) (N.to_nat 44256660626945%N) (N.to_nat 3383428325767%N) -->* fT2 (N.to_nat 10730360422082%N) (N.to_nat 40238851582812%N) (N.to_nat 44256660626954%N) (N.to_nat 3383428325765%N).
Proof. eapply tr; [apply progress_evstep; exact (texit3 (N.to_nat 10730360422077%N) (N.to_nat 3383428325764%N) (N.to_nat 21460720844152%N) (N.to_nat 18778130738639%N) (N.to_nat 44256660626939%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move184 : fT2 (N.to_nat 10730360422082%N) (N.to_nat 40238851582812%N) (N.to_nat 44256660626954%N) (N.to_nat 3383428325765%N) -->* fT2 (N.to_nat 15805502910728%N) (N.to_nat 52080850722986%N) (N.to_nat 52715231441364%N) 1.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 1691714162882%N) (N.to_nat 10730360422082%N) (N.to_nat 40238851582806%N) (N.to_nat 44256660626948%N) 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move185 : fT2 (N.to_nat 15805502910728%N) (N.to_nat 52080850722986%N) (N.to_nat 52715231441364%N) 1 -->* fRG (N.to_nat 15805502910731%N) (N.to_nat 52080850722985%N) 5 (N.to_nat 52715231441359%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 15805502910728%N) (N.to_nat 52080850722984%N) (N.to_nat 52715231441352%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move186 : fRG (N.to_nat 15805502910731%N) (N.to_nat 52080850722985%N) 5 (N.to_nat 52715231441359%N) -->* fRG (N.to_nat 15805502910731%N) (N.to_nat 52080850722985%N) (N.to_nat 52715231441363%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 52715231441358%N) (N.to_nat 15805502910731%N) (N.to_nat 52080850722985%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move187 : fRG (N.to_nat 15805502910731%N) (N.to_nat 52080850722985%N) (N.to_nat 52715231441363%N) 1 -->* fT3 1 6 (N.to_nat 15805502910728%N) 11 (N.to_nat 52080850722993%N) (N.to_nat 26357615720679%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 15805502910728%N) (N.to_nat 52080850722979%N) (N.to_nat 26357615720678%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move188 : fT3 1 6 (N.to_nat 15805502910728%N) 11 (N.to_nat 52080850722993%N) (N.to_nat 26357615720679%N) -->* fT3 (N.to_nat 12644402328581%N) (N.to_nat 25288804657166%N) 3 (N.to_nat 22127704075026%N) (N.to_nat 67886353633718%N) (N.to_nat 20035414556389%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 3161100582145%N) 1 0 3 5 (N.to_nat 52080850722987%N) (N.to_nat 20035414556389%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move189 : fT3 (N.to_nat 12644402328581%N) (N.to_nat 25288804657166%N) 3 (N.to_nat 22127704075026%N) (N.to_nat 67886353633718%N) (N.to_nat 20035414556389%N) -->* fT2 (N.to_nat 12644402328586%N) (N.to_nat 47416508732202%N) (N.to_nat 67886353633727%N) (N.to_nat 20035414556387%N).
Proof. eapply tr; [apply progress_evstep; exact (texit3 (N.to_nat 12644402328581%N) (N.to_nat 20035414556386%N) (N.to_nat 25288804657160%N) (N.to_nat 22127704075021%N) (N.to_nat 67886353633712%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move190 : fT2 (N.to_nat 12644402328586%N) (N.to_nat 47416508732202%N) (N.to_nat 67886353633727%N) (N.to_nat 20035414556387%N) -->* fT2 (N.to_nat 42697524163165%N) (N.to_nat 117540459679553%N) (N.to_nat 117974890024692%N) 1.
Proof. eapply tr; [exact (cycle2_iter (N.to_nat 10017707278193%N) (N.to_nat 12644402328586%N) (N.to_nat 47416508732196%N) (N.to_nat 67886353633721%N) 1) | apply fT2_eq; lia | apply fT2_eq; lia]. Qed.
Lemma move191 : fT2 (N.to_nat 42697524163165%N) (N.to_nat 117540459679553%N) (N.to_nat 117974890024692%N) 1 -->* fRG (N.to_nat 42697524163168%N) (N.to_nat 117540459679552%N) 5 (N.to_nat 117974890024687%N).
Proof. eapply tr; [apply progress_evstep; exact (t2exit1 (N.to_nat 42697524163165%N) (N.to_nat 117540459679551%N) (N.to_nat 117974890024680%N)) | apply fT2_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move192 : fRG (N.to_nat 42697524163168%N) (N.to_nat 117540459679552%N) 5 (N.to_nat 117974890024687%N) -->* fRG (N.to_nat 42697524163168%N) (N.to_nat 117540459679552%N) (N.to_nat 117974890024691%N) 1.
Proof. eapply tr; [exact (gcyc_iter (N.to_nat 117974890024686%N) (N.to_nat 42697524163168%N) (N.to_nat 117540459679552%N) 5 0) | apply fRG_eq; lia | apply fRG_eq; lia]. Qed.
Lemma move193 : fRG (N.to_nat 42697524163168%N) (N.to_nat 117540459679552%N) (N.to_nat 117974890024691%N) 1 -->* fT3 1 6 (N.to_nat 42697524163165%N) 11 (N.to_nat 117540459679560%N) (N.to_nat 58987445012343%N).
Proof. eapply tr; [apply progress_evstep; exact (gendo_ (N.to_nat 42697524163165%N) (N.to_nat 117540459679546%N) (N.to_nat 58987445012342%N)) | apply fRG_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move194 : fT3 1 6 (N.to_nat 42697524163165%N) 11 (N.to_nat 117540459679560%N) (N.to_nat 58987445012343%N) -->* fT3 (N.to_nat 34158019330533%N) (N.to_nat 68316038661070%N) 0 (N.to_nat 59776533828442%N) (N.to_nat 160237983842725%N) (N.to_nat 41908435347077%N).
Proof. eapply tr; [exact (cycle3_iter (N.to_nat 8539504832633%N) 1 0 0 5 (N.to_nat 117540459679554%N) (N.to_nat 41908435347077%N)) | apply fT3_eq; lia | apply fT3_eq; lia]. Qed.
Lemma move195 : fT3 (N.to_nat 34158019330533%N) (N.to_nat 68316038661070%N) 0 (N.to_nat 59776533828442%N) (N.to_nat 160237983842725%N) (N.to_nat 41908435347077%N) -->* fT2 (N.to_nat 34158019330534%N) (N.to_nat 128092572489511%N) (N.to_nat 160237983842729%N) (N.to_nat 41908435347077%N).
Proof. eapply tr; [apply progress_evstep; exact (texit0 (N.to_nat 34158019330533%N) (N.to_nat 41908435347076%N) (N.to_nat 68316038661065%N) (N.to_nat 59776533828440%N) (N.to_nat 160237983842723%N)) | apply fT3_eq; lia | apply fT2_eq; lia]. Qed.

Definition last_cfg : Q * tape := fT2 (N.to_nat 34158019330534%N) (N.to_nat 128092572489511%N) (N.to_nat 160237983842729%N) (N.to_nat 41908435347077%N).
Lemma table_run : fO 14 37 11 -->* last_cfg.
Proof.
  unfold last_cfg.
  eapply evstep_trans; [exact move0 |].
  eapply evstep_trans; [exact move1 |].
  eapply evstep_trans; [exact move2 |].
  eapply evstep_trans; [exact move3 |].
  eapply evstep_trans; [exact move4 |].
  eapply evstep_trans; [exact move5 |].
  eapply evstep_trans; [exact move6 |].
  eapply evstep_trans; [exact move7 |].
  eapply evstep_trans; [exact move8 |].
  eapply evstep_trans; [exact move9 |].
  eapply evstep_trans; [exact move10 |].
  eapply evstep_trans; [exact move11 |].
  eapply evstep_trans; [exact move12 |].
  eapply evstep_trans; [exact move13 |].
  eapply evstep_trans; [exact move14 |].
  eapply evstep_trans; [exact move15 |].
  eapply evstep_trans; [exact move16 |].
  eapply evstep_trans; [exact move17 |].
  eapply evstep_trans; [exact move18 |].
  eapply evstep_trans; [exact move19 |].
  eapply evstep_trans; [exact move20 |].
  eapply evstep_trans; [exact move21 |].
  eapply evstep_trans; [exact move22 |].
  eapply evstep_trans; [exact move23 |].
  eapply evstep_trans; [exact move24 |].
  eapply evstep_trans; [exact move25 |].
  eapply evstep_trans; [exact move26 |].
  eapply evstep_trans; [exact move27 |].
  eapply evstep_trans; [exact move28 |].
  eapply evstep_trans; [exact move29 |].
  eapply evstep_trans; [exact move30 |].
  eapply evstep_trans; [exact move31 |].
  eapply evstep_trans; [exact move32 |].
  eapply evstep_trans; [exact move33 |].
  eapply evstep_trans; [exact move34 |].
  eapply evstep_trans; [exact move35 |].
  eapply evstep_trans; [exact move36 |].
  eapply evstep_trans; [exact move37 |].
  eapply evstep_trans; [exact move38 |].
  eapply evstep_trans; [exact move39 |].
  eapply evstep_trans; [exact move40 |].
  eapply evstep_trans; [exact move41 |].
  eapply evstep_trans; [exact move42 |].
  eapply evstep_trans; [exact move43 |].
  eapply evstep_trans; [exact move44 |].
  eapply evstep_trans; [exact move45 |].
  eapply evstep_trans; [exact move46 |].
  eapply evstep_trans; [exact move47 |].
  eapply evstep_trans; [exact move48 |].
  eapply evstep_trans; [exact move49 |].
  eapply evstep_trans; [exact move50 |].
  eapply evstep_trans; [exact move51 |].
  eapply evstep_trans; [exact move52 |].
  eapply evstep_trans; [exact move53 |].
  eapply evstep_trans; [exact move54 |].
  eapply evstep_trans; [exact move55 |].
  eapply evstep_trans; [exact move56 |].
  eapply evstep_trans; [exact move57 |].
  eapply evstep_trans; [exact move58 |].
  eapply evstep_trans; [exact move59 |].
  eapply evstep_trans; [exact move60 |].
  eapply evstep_trans; [exact move61 |].
  eapply evstep_trans; [exact move62 |].
  eapply evstep_trans; [exact move63 |].
  eapply evstep_trans; [exact move64 |].
  eapply evstep_trans; [exact move65 |].
  eapply evstep_trans; [exact move66 |].
  eapply evstep_trans; [exact move67 |].
  eapply evstep_trans; [exact move68 |].
  eapply evstep_trans; [exact move69 |].
  eapply evstep_trans; [exact move70 |].
  eapply evstep_trans; [exact move71 |].
  eapply evstep_trans; [exact move72 |].
  eapply evstep_trans; [exact move73 |].
  eapply evstep_trans; [exact move74 |].
  eapply evstep_trans; [exact move75 |].
  eapply evstep_trans; [exact move76 |].
  eapply evstep_trans; [exact move77 |].
  eapply evstep_trans; [exact move78 |].
  eapply evstep_trans; [exact move79 |].
  eapply evstep_trans; [exact move80 |].
  eapply evstep_trans; [exact move81 |].
  eapply evstep_trans; [exact move82 |].
  eapply evstep_trans; [exact move83 |].
  eapply evstep_trans; [exact move84 |].
  eapply evstep_trans; [exact move85 |].
  eapply evstep_trans; [exact move86 |].
  eapply evstep_trans; [exact move87 |].
  eapply evstep_trans; [exact move88 |].
  eapply evstep_trans; [exact move89 |].
  eapply evstep_trans; [exact move90 |].
  eapply evstep_trans; [exact move91 |].
  eapply evstep_trans; [exact move92 |].
  eapply evstep_trans; [exact move93 |].
  eapply evstep_trans; [exact move94 |].
  eapply evstep_trans; [exact move95 |].
  eapply evstep_trans; [exact move96 |].
  eapply evstep_trans; [exact move97 |].
  eapply evstep_trans; [exact move98 |].
  eapply evstep_trans; [exact move99 |].
  eapply evstep_trans; [exact move100 |].
  eapply evstep_trans; [exact move101 |].
  eapply evstep_trans; [exact move102 |].
  eapply evstep_trans; [exact move103 |].
  eapply evstep_trans; [exact move104 |].
  eapply evstep_trans; [exact move105 |].
  eapply evstep_trans; [exact move106 |].
  eapply evstep_trans; [exact move107 |].
  eapply evstep_trans; [exact move108 |].
  eapply evstep_trans; [exact move109 |].
  eapply evstep_trans; [exact move110 |].
  eapply evstep_trans; [exact move111 |].
  eapply evstep_trans; [exact move112 |].
  eapply evstep_trans; [exact move113 |].
  eapply evstep_trans; [exact move114 |].
  eapply evstep_trans; [exact move115 |].
  eapply evstep_trans; [exact move116 |].
  eapply evstep_trans; [exact move117 |].
  eapply evstep_trans; [exact move118 |].
  eapply evstep_trans; [exact move119 |].
  eapply evstep_trans; [exact move120 |].
  eapply evstep_trans; [exact move121 |].
  eapply evstep_trans; [exact move122 |].
  eapply evstep_trans; [exact move123 |].
  eapply evstep_trans; [exact move124 |].
  eapply evstep_trans; [exact move125 |].
  eapply evstep_trans; [exact move126 |].
  eapply evstep_trans; [exact move127 |].
  eapply evstep_trans; [exact move128 |].
  eapply evstep_trans; [exact move129 |].
  eapply evstep_trans; [exact move130 |].
  eapply evstep_trans; [exact move131 |].
  eapply evstep_trans; [exact move132 |].
  eapply evstep_trans; [exact move133 |].
  eapply evstep_trans; [exact move134 |].
  eapply evstep_trans; [exact move135 |].
  eapply evstep_trans; [exact move136 |].
  eapply evstep_trans; [exact move137 |].
  eapply evstep_trans; [exact move138 |].
  eapply evstep_trans; [exact move139 |].
  eapply evstep_trans; [exact move140 |].
  eapply evstep_trans; [exact move141 |].
  eapply evstep_trans; [exact move142 |].
  eapply evstep_trans; [exact move143 |].
  eapply evstep_trans; [exact move144 |].
  eapply evstep_trans; [exact move145 |].
  eapply evstep_trans; [exact move146 |].
  eapply evstep_trans; [exact move147 |].
  eapply evstep_trans; [exact move148 |].
  eapply evstep_trans; [exact move149 |].
  eapply evstep_trans; [exact move150 |].
  eapply evstep_trans; [exact move151 |].
  eapply evstep_trans; [exact move152 |].
  eapply evstep_trans; [exact move153 |].
  eapply evstep_trans; [exact move154 |].
  eapply evstep_trans; [exact move155 |].
  eapply evstep_trans; [exact move156 |].
  eapply evstep_trans; [exact move157 |].
  eapply evstep_trans; [exact move158 |].
  eapply evstep_trans; [exact move159 |].
  eapply evstep_trans; [exact move160 |].
  eapply evstep_trans; [exact move161 |].
  eapply evstep_trans; [exact move162 |].
  eapply evstep_trans; [exact move163 |].
  eapply evstep_trans; [exact move164 |].
  eapply evstep_trans; [exact move165 |].
  eapply evstep_trans; [exact move166 |].
  eapply evstep_trans; [exact move167 |].
  eapply evstep_trans; [exact move168 |].
  eapply evstep_trans; [exact move169 |].
  eapply evstep_trans; [exact move170 |].
  eapply evstep_trans; [exact move171 |].
  eapply evstep_trans; [exact move172 |].
  eapply evstep_trans; [exact move173 |].
  eapply evstep_trans; [exact move174 |].
  eapply evstep_trans; [exact move175 |].
  eapply evstep_trans; [exact move176 |].
  eapply evstep_trans; [exact move177 |].
  eapply evstep_trans; [exact move178 |].
  eapply evstep_trans; [exact move179 |].
  eapply evstep_trans; [exact move180 |].
  eapply evstep_trans; [exact move181 |].
  eapply evstep_trans; [exact move182 |].
  eapply evstep_trans; [exact move183 |].
  eapply evstep_trans; [exact move184 |].
  eapply evstep_trans; [exact move185 |].
  eapply evstep_trans; [exact move186 |].
  eapply evstep_trans; [exact move187 |].
  eapply evstep_trans; [exact move188 |].
  eapply evstep_trans; [exact move189 |].
  eapply evstep_trans; [exact move190 |].
  eapply evstep_trans; [exact move191 |].
  eapply evstep_trans; [exact move192 |].
  eapply evstep_trans; [exact move193 |].
  eapply evstep_trans; [exact move194 |].
  exact move195.
Qed.

Lemma blank_last : c0 -->* last_cfg.
Proof. eapply evstep_trans; [apply progress_evstep; exact blank_O | exact table_run]. Qed.