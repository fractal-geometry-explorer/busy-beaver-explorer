From BusyCoq Require Import T4C.
From Coq Require Import NArith PArith.
Require Import Extraction ExtrOcamlZBigInt.
(* A few more realizations of binary-number functions by Zarith (ExtrOcamlZBigInt covers add, sub, mul, compare,
   div, ...); each is the function's mathematical meaning on non-negative integers. *)
Extract Constant N.eqb => "Big_int_Z.eq_big_int".
Extract Constant N.leb => "Big_int_Z.le_big_int".
Extract Constant N.ltb => "Big_int_Z.lt_big_int".
Extract Constant Pos.eqb => "Big_int_Z.eq_big_int".
Extract Constant N.double => "(fun x -> Big_int_Z.mult_int_big_int 2 x)".
Extract Constant N.succ_double => "(fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))".
Extract Constant N.div2 => "(fun x -> Big_int_Z.shift_right_big_int x 1)".
Extraction Language OCaml.
Extraction "t4cengz" T4C.stepFast T4C.initFastA T4C.initFastB T4C.initFastC T4C.initFastD T4C.fs_size T4C.fs_cells T4C.fs_mode T4C.fs_L T4C.fs_R T4C.runs_pop T4C.r_raw T4C.d_front T4C.d_back T4C.r_tail T4C.fs_list.
