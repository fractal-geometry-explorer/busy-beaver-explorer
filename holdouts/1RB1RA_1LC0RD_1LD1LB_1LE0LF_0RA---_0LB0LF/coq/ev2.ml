(* ev2 START N [CK]: print every raw event of interest with context *)
open T4ceng
let rec bits = function N0 -> 0 | Npos p -> let rec pb = function XH -> 1 | XO q | XI q -> 1 + pb q in pb p
let small n = if bits n < 30 then (let rec v = function XH -> 1 | XO q -> 2 * v q | XI q -> 2 * v q + 1 in match n with N0 -> "0" | Npos p -> string_of_int (v p)) else Printf.sprintf "2^%d" (bits n - 1)
let rec syms = function Nil -> "" | Cons (S0, r) -> "0" ^ syms r | Cons (S1, r) -> "1" ^ syms r
let sw = function
  | T4C.SW_raw w -> "[" ^ syms w ^ "]" | T4C.SW_D n -> "D" ^ small n | T4C.SW_S n -> "S" ^ small n
  | T4C.SW_PL n -> "PL" ^ small n | T4C.SW_DEF (a, k) -> "DEF(" ^ small a ^ "," ^ small k ^ ")"
  | T4C.SW_DF _ -> "DF" | T4C.SW_DB _ -> "DB"
let rec runs k = function Nil -> "" | Cons (Pair (w, c), r) -> if k = 0 then " ..." else " " ^ sw w ^ "^" ^ small c ^ runs (k-1) r
let rec digs k = function Nil -> "" | Cons (Pair (n, c), r) -> if k = 0 then " ..." else " D" ^ small n ^ "^" ^ small c ^ digs (k-1) r
let rec popn k l = if k = 0 then "" else match T4C.runs_pop l with Pair (b, r) -> (if b = S1 then "1" else "0") ^ popn (k-1) r
let qs = function A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F"
let () =
  let s = ref (match Sys.argv.(1) with "A" -> T4C.initFastA | "B" -> T4C.initFastB | _ -> T4C.initFastC) and i = ref 0 in
  (if Array.length Sys.argv > 3 && Sys.file_exists Sys.argv.(3) then
     let ic = open_in_bin Sys.argv.(3) in let (st, n) : T4C.coq_FastState * int = Marshal.from_channel ic in close_in ic; s := st; i := n);
  let lim = int_of_string Sys.argv.(2) and fin = ref false and last = ref "" in
  let save () = if Array.length Sys.argv > 4 then begin let f = Sys.argv.(4) in let oc = open_out_bin (f ^ ".tmp") in Marshal.to_channel oc (!s, !i) []; close_out oc; Sys.rename (f ^ ".tmp") f end in
  let nexts = ref (Unix.gettimeofday () +. 600.) and nextr = ref (Unix.gettimeofday () +. 300.) in
  while not !fin && !i < lim do
    (match T4C.fs_mode !s with
     | T4C.RAW (q, L) ->
       let ctx = popn 6 (T4C.fs_L !s) in
       let hd = ctx.[0] in
       if (q = D && hd = '0') || (q = F && hd = '1') || (q = C && hd = '0') then begin
         let rt = T4C.fs_R !s in
         Printf.printf "%d %s reads %c left(outward)=%s | L:%s | R raw:%s fr:%s bk:%s tl:%s\n%!" !i (qs q) hd (String.sub ctx 1 5) (runs 6 (T4C.fs_L !s)) (runs 4 (T4C.r_raw rt)) (digs 3 (T4C.d_front rt)) (digs 2 (T4C.d_back rt)) (runs 3 (T4C.r_tail rt)) end
     | _ -> ());
    (match T4C.stepFast !s with None -> fin := true | Some s' -> s := s'; incr i);
    ignore last;
    if Unix.gettimeofday () > !nexts then (save (); nexts := Unix.gettimeofday () +. 600.);
    if Unix.gettimeofday () > !nextr then (Printf.printf "at %d cells 2^%d\n%!" !i (bits (T4C.fs_cells !s) - 1); nextr := Unix.gettimeofday () +. 300.)
  done;
  save ();
  Printf.printf "end %d stopped %b\n" !i !fin
