(* Print where W reads 1 in state F: the step at which PR 93's machine T3 halts and W (and this machine) go on.
   usage: f1 MAXFAST MAXEVENTS *)
open Wceng
let cap = 1 lsl 40
let rec n2i = function N0 -> 0 | Npos p -> let rec pf = function XH -> 1 | XO q -> let v = pf q in if v >= cap then cap else 2*v | XI q -> let v = pf q in if v >= cap then cap else 2*v+1 in pf p
(* profile: Z len (all zeros) | P (lead, trail, inner) *)
type prof = Z of int | P of int * int * int
let e = Z 0
let comp a b = match a, b with
  | Z x, Z y -> Z (Stdlib.min cap (x+y))
  | Z x, P (l,t,i) -> P (Stdlib.min cap (x+l), t, i)
  | P (l,t,i), Z y -> P (l, Stdlib.min cap (t+y), i)
  | P (l1,t1,i1), P (l2,t2,i2) -> P (l1, t2, Stdlib.max (Stdlib.max i1 i2) (t1+l2))
let rev = function Z x -> Z x | P (l,t,i) -> P (t,l,i)
let rep p k = if k = 0 then e else match p with Z x -> Z (Stdlib.min cap (x*k)) | P _ -> if k = 1 then p else comp p p
let of_bits l = List.fold_left (fun acc b -> comp acc (if b = 1 then P (0,0,0) else Z 1)) e l
let rec syms = function Nil -> [] | Cons (S0, r) -> 0 :: syms r | Cons (S1, r) -> 1 :: syms r
let rep_bits w k = List.concat (List.init k (fun _ -> w))
let dword = P (0,2,0)
let rec digs = function Nil -> e | Cons (Pair (_, k), r) -> comp (rep dword (n2i k)) (digs r)
let sw = function
  | T4C.SW_raw w -> of_bits (syms w)
  | T4C.SW_D _ -> dword
  | T4C.SW_S _ -> P (0,0,1)
  | T4C.SW_PL n -> let n = Stdlib.min 2 (n2i n) in of_bits (rep_bits [1;0] (n+4) @ rep_bits [1;1] n @ [1;0;1;1;0;1])
  | T4C.SW_DEF (a,k) -> let a = Stdlib.min 2 (n2i a) and k = Stdlib.min 2 (n2i k) in of_bits (rep_bits [1;0] a @ rep_bits [1] k @ [0;1;1;0;1])
  | T4C.SW_DF ds -> digs ds
  | T4C.SW_DB ds -> digs ds
let rec runs = function Nil -> e | Cons (Pair (w, c), r) -> comp (rep (sw w) (n2i c)) (runs r)
let rec digsrev = function Nil -> e | Cons (Pair (_, k), r) -> comp (digsrev r) (rep dword (n2i k))
let qs = function A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F"
let mode s = match T4C.fs_mode s with T4C.MR -> "MR" | T4C.ML -> "ML" | T4C.MJ -> "MJ"
  | T4C.RAW (q, d) -> "RAW " ^ qs q ^ (if d = L then "L" else "R")
let profile s =
  let lp = rev (runs (T4C.fs_L s)) in   (* left in tape order *)
  let rt = T4C.fs_R s in
  let rp = comp (runs (T4C.r_raw rt)) (comp (digs (T4C.d_front rt)) (comp (digsrev (T4C.d_back rt)) (runs (T4C.r_tail rt)))) in
  let pre = match T4C.fs_mode s with T4C.MR -> of_bits [0;1;0;0] | T4C.ML -> of_bits [1] | T4C.MJ -> of_bits [1;0;0] | _ -> e in
  let lpi = match lp with P (_,_,i) -> i | _ -> 0 and rpi = match rp with P (_,_,i) -> i | _ -> 0 in
  (comp lp (comp pre rp), lpi, rpi)
let rec n2s = function N0 -> "0" | Npos p -> let v = n2i (Npos p) in if v >= cap then "big" else string_of_int v
let swn = function
  | T4C.SW_raw w -> "[" ^ String.concat "" (List.map string_of_int (syms w)) ^ "]" | T4C.SW_D n -> "D" ^ n2s n | T4C.SW_S n -> "S" ^ n2s n
  | T4C.SW_PL n -> "PL" ^ n2s n | T4C.SW_DEF (a, k) -> "DEF(" ^ n2s a ^ "," ^ n2s k ^ ")"
  | T4C.SW_DF _ -> "DF" | T4C.SW_DB _ -> "DB"
let rec runsn k = function Nil -> "" | Cons (Pair (w, c), r) -> if k = 0 then " ..." else " " ^ swn w ^ "^" ^ n2s c ^ runsn (k-1) r
let rec digsn k = function Nil -> "" | Cons (Pair (n, c), r) -> if k = 0 then " ..." else " D" ^ n2s n ^ "^" ^ n2s c ^ digsn (k-1) r
let show s = let rt = T4C.fs_R s in
  Printf.printf "    L:%s\n    R raw:%s | front:%s | back:%s | tail:%s\n%!" (runsn 8 (T4C.fs_L s)) (runsn 8 (T4C.r_raw rt)) (digsn 6 (T4C.d_front rt)) (digsn 6 (T4C.d_back rt)) (runsn 6 (T4C.r_tail rt))
let dbits n = 1 :: rep_bits [1;1] n @ [0;0]
let rec take k l = if k = 0 then [] else match l with [] -> [] | x :: r -> x :: take (k-1) r
let rec digbits k = function Nil -> [] | Cons (Pair (n, c), r) -> if k <= 0 then [] else
   let w = dbits (Stdlib.min 8 (n2i n)) in let b = take k (rep_bits w (Stdlib.min k (n2i c))) in b @ digbits (k - List.length b) r
let swbits k = function
  | T4C.SW_raw w -> syms w | T4C.SW_D n -> take k (dbits (n2i n |> Stdlib.min k))
  | T4C.SW_S n -> take k (1 :: rep_bits [0;1] (Stdlib.min k (n2i n) + 1))
  | T4C.SW_PL n -> let n = n2i n |> Stdlib.min k in take k (rep_bits [1;0] (n+4) @ rep_bits [1;1] n @ [1;0;1;1;0;1])
  | T4C.SW_DEF (a,kk) -> let a = n2i a |> Stdlib.min k and kk = n2i kk |> Stdlib.min k in take k (rep_bits [1;0] a @ rep_bits [1] kk @ [0;1;1;0;1])
  | T4C.SW_DF ds -> digbits k ds
  | T4C.SW_DB ds -> digbits k (let rec rv acc = function Nil -> acc | Cons (x, r) -> rv (Cons (x, acc)) r in rv Nil ds)
let rec runbits k = function Nil -> [] | Cons (Pair (w, c), r) -> if k <= 0 then [] else
   let b = take k (rep_bits (swbits k w) (Stdlib.min k (n2i c))) in b @ runbits (k - List.length b) r
let rightbits k s = let rt = T4C.fs_R s in
  let a = runbits k (T4C.r_raw rt) in let b = digbits (k - List.length a) (T4C.d_front rt) in
  let rec rv acc = function Nil -> acc | Cons (x, r) -> rv (Cons (x, acc)) r in
  let c = digbits (k - List.length a - List.length b) (rv Nil (T4C.d_back rt)) in
  let d = runbits (k - List.length a - List.length b - List.length c) (T4C.r_tail rt) in
  let x = a @ b @ c @ d in x @ List.init (k - List.length x) (fun _ -> 0)
let leftbits k s = let x = runbits k (T4C.fs_L s) in x @ List.init (k - List.length x) (fun _ -> 0)
(* exact halting test of M at a fast-step boundary: true if the next W steps reach D reading 0 with a 1 on its left *)
let danger s =
  let l = leftbits 4 s and r = (match T4C.fs_mode s with T4C.RAW (_, R) -> rightbits 1 s | _ -> [0]) in
  let nth l i = List.nth l i in
  match T4C.fs_mode s with
  | T4C.RAW (D, R) -> nth r 0 = 0 && nth l 0 = 1
  | T4C.RAW (D, L) -> nth l 0 = 0 && nth l 1 = 1
  | T4C.RAW (C, R) -> nth r 0 = 0 && nth l 0 = 0 && nth l 1 = 1
  | T4C.RAW (C, L) -> nth l 0 = 0 && nth l 1 = 0 && nth l 2 = 1
  | T4C.RAW (B, R) -> nth r 0 = 0 && nth l 0 = 0 && nth l 1 = 0 && nth l 2 = 1
  | T4C.RAW (B, L) | T4C.ML -> nth l 0 = 0 && nth l 1 = 0 && nth l 2 = 0 && nth l 3 = 1
  | T4C.MJ -> nth l 0 = 0 && nth l 1 = 0 && nth l 2 = 1
  | _ -> false
let init = function "A" -> T4C.initFastA | "B" -> T4C.initFastB | "C" -> T4C.initFastC | _ -> T4C.initFastD
let rec bits = function N0 -> 0 | Npos p -> let rec pb = function XH -> 1 | XO q | XI q -> 1 + pb q in pb p
let () =
  let s = ref (init "C") and i = ref 0 and cnt = ref 0 in
  let lim = int_of_string Sys.argv.(1) and maxev = int_of_string Sys.argv.(2) in
  while !i < lim && !cnt < maxev do
    (match T4C.stepFast !s with None -> i := lim | Some s' -> s := s'; incr i);
    let f1 = match T4C.fs_mode !s with
      | T4C.RAW (F, R) -> List.hd (rightbits 1 !s) = 1
      | T4C.RAW (F, L) -> List.hd (leftbits 1 !s) = 1
      | _ -> false in
    if f1 then (incr cnt; Printf.printf "F reads 1 (T3 halts here) at fast %d, cells 2^%d, mode %s\n%!" !i (bits (T4C.fs_cells !s) - 1) (mode !s); show !s)
  done
