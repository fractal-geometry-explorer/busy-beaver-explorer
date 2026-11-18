Fixpoint runs_list (xs : Runs) : list Sym :=
  match xs with
  | [] => []
  | (w, n) :: xs' => (sw_toList w)^^(N.to_nat n) ++ runs_list xs'
  end.
Fixpoint revDigitsList (v : Digits) (acc : list Sym) : list Sym :=
  match v with
  | [] => acc
  | (n, k) :: xs => revDigitsList xs ((D_word (N.to_nat n))^^(N.to_nat k) ++ acc)
  end.
Definition rt_list (rt : RTape) : list Sym :=
  runs_list (r_raw rt) ++ digitsToList (d_front rt) ++ revDigitsList (d_back rt) (runs_list (r_tail rt)).
(* left outward, state, true = head on hd of left, right *)
Definition fs_list (s : FastState) : list Sym * Q * bool * list Sym :=
  let l := runs_list (fs_L s) in
  let r := rt_list (fs_R s) in
  match fs_mode s with
  | MR => (l, A, false, [0; 1; 0; 0] ++ r)
  | ML => (l, B, true, [1] ++ r)
  | MJ => (l, C, true, [1; 0; 0] ++ r)
  | RAW q R => (l, q, false, r)
  | RAW q L => (l, q, true, r)
  end.
Definition fs_size (s : FastState) : N := N.of_nat (List.length (fs_L s) + List.length (r_raw (fs_R s)) + List.length (d_front (fs_R s)) + List.length (d_back (fs_R s)) + List.length (r_tail (fs_R s))).
Definition initFastB : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW B R).
Definition initFastD : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW D R).
Definition sw_cells (w : SymWord) : N :=
  match w with
  | SW_raw lw => N.of_nat (List.length lw)
  | SW_D n => 3 + 2 * n
  | SW_S n => 3 + 2 * n
  | SW_PL n => 4 * n + 14
  | SW_DEF a k => 2 * a + k + 5
  | SW_DF ds => fold_right (fun (nk : N * N) (acc : N) => ((3 + 2 * fst nk) * snd nk + acc)%N) 0%N ds
  | SW_DB ds => fold_right (fun (nk : N * N) (acc : N) => ((3 + 2 * fst nk) * snd nk + acc)%N) 0%N ds
  end%N.
Definition runs_cells (xs : Runs) : N := fold_right (fun (wk : SymWord * N) (acc : N) => (sw_cells (fst wk) * snd wk + acc)%N) 0%N xs.
Definition digits_cells (ds : Digits) : N := fold_right (fun (nk : N * N) (acc : N) => ((3 + 2 * fst nk) * snd nk + acc)%N) 0%N ds.
(* cells written on the tape (the blank ends not counted), a measure of progress: about the square root of the step count *)
Definition fs_cells (s : FastState) : N :=
  (runs_cells (fs_L s) + runs_cells (r_raw (fs_R s)) + digits_cells (d_front (fs_R s))
   + digits_cells (d_back (fs_R s)) + runs_cells (r_tail (fs_R s)) + 4)%N.
