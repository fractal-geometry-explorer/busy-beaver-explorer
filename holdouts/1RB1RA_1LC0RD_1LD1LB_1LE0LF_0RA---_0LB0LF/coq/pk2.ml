open T4ceng
let rec n2s = function N0 -> "0" | Npos p -> let rec pb = function XH -> "1" | XO q -> pb q ^ "0" | XI q -> pb q ^ "1" in "0b" ^ pb p
let rec bits = function N0 -> 0 | Npos p -> let rec pb = function XH -> 1 | XO q | XI q -> 1 + pb q in pb p
let small n = if bits n < 30 then (let rec v = function XH -> 1 | XO q -> 2 * v q | XI q -> 2 * v q + 1 in match n with N0 -> "0" | Npos p -> string_of_int (v p)) else Printf.sprintf "2^%d" (bits n - 1)
let rec syms = function Nil -> "" | Cons (S0, r) -> "0" ^ syms r | Cons (S1, r) -> "1" ^ syms r
let sw = function
  | T4C.SW_raw w -> "[" ^ syms w ^ "]" | T4C.SW_D n -> "D" ^ small n | T4C.SW_S n -> "S" ^ small n
  | T4C.SW_PL n -> "PL" ^ small n | T4C.SW_DEF (a, k) -> "DEF(" ^ small a ^ "," ^ small k ^ ")"
  | T4C.SW_DF _ -> "DF" | T4C.SW_DB _ -> "DB"
let rec runs k = function Nil -> "" | Cons (Pair (w, c), r) -> if k = 0 then " ..." else " " ^ sw w ^ "^" ^ small c ^ runs (k-1) r
let rec digs k = function Nil -> "" | Cons (Pair (n, c), r) -> if k = 0 then " ..." else " D" ^ small n ^ "^" ^ small c ^ digs (k-1) r
let mname s = match T4C.fs_mode s with T4C.RAW (q, d) -> "RAW " ^ (match q with A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F") ^ (if d = L then "L" else "R") | T4C.MR -> "MR" | T4C.ML -> "ML" | T4C.MJ -> "MJ"
let () =
  let s = ref (match Sys.argv.(1) with "A" -> T4C.initFastA | "B" -> T4C.initFastB | "D" -> T4C.initFastD | _ -> T4C.initFastC) and i = ref 0 in
  let a = int_of_string Sys.argv.(2) and b = int_of_string Sys.argv.(3) in
  while !i < b do
    if !i >= a then begin
      let rt = T4C.fs_R !s in
      Printf.printf "%d %s | L:%s | R raw:%s fr:%s bk:%s tl:%s\n" !i (mname !s) (runs 6 (T4C.fs_L !s)) (runs 4 (T4C.r_raw rt)) (digs 3 (T4C.d_front rt)) (digs 2 (T4C.d_back rt)) (runs 3 (T4C.r_tail rt)) end;
    (match T4C.stepFast !s with None -> (print_endline "STOP"; i := b) | Some s' -> s := s'; incr i)
  done
