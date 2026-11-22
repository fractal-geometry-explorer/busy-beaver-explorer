(* Show a checkpoint of watch: the fast step, the size of the tape and the first runs on each side.  usage: peek CHECKPOINT *)
open Wceng
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
let () =
  let ic = open_in_bin Sys.argv.(1) in
  let (s, n) : T4C.coq_FastState * int = Marshal.from_channel ic in
  Printf.printf "fast step %d  cells 2^%d\n" n (bits (T4C.fs_cells s) - 1);
  (match T4C.fs_mode s with T4C.RAW (q, d) -> Printf.printf "RAW %s %s\n" (match q with A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F") (if d = L then "L (head on first cell of left)" else "R") | _ -> print_endline "macro mode");
  Printf.printf "left (outward):%s\n" (runs 12 (T4C.fs_L s));
  let rt = T4C.fs_R s in
  Printf.printf "right raw:%s\nright front digits:%s\nright back digits:%s\nright tail:%s\n" (runs 12 (T4C.r_raw rt)) (digs 12 (T4C.d_front rt)) (digs 12 (T4C.d_back rt)) (runs 12 (T4C.r_tail rt))
