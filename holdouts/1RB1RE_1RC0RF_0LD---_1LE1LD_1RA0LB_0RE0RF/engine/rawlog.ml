(* Raw-step logger for PR 93's engine on W.  Every fast step whose mode is RAW (q,d) is an unbatched step (or a short
   shift scan inside stepRaw).  Consecutive raw steps form a stretch; we record its signature
   (entry macro mode, sequence of q d read).  For every D step reading 0, and every leftward B or C step reading 0
   (the only raw route to a halt: B< 0, C< 0, D< 0 with a 1 beyond), it records the 4 cells beyond the read one;
   a HALT line means D read 0 with a 1 beside it.
   usage: rawlog START MAXFAST [CK_IN|-] [CK_OUT] *)
open Wceng
(* The helpers below are those of watch.ml. *)
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
let init = function "A" -> T4C.initFastA | "B" -> T4C.initFastB | "C" -> T4C.initFastC | _ -> T4C.initFastD
let bstr l = String.concat "" (List.map string_of_int l)
let mshort s = match T4C.fs_mode s with T4C.MR -> "MR" | T4C.ML -> "ML" | T4C.MJ -> "MJ"
  | T4C.RAW (q, d) -> qs q ^ (if d = L then "<" else ">")
(* window: 10 cells left (nearest first, printed in tape order) and 10 right *)
let window s = let l = List.rev (leftbits 16 s) and r = rightbits 16 s in bstr l ^ "|" ^ bstr r
let () =
  let s = ref (init Sys.argv.(1)) and i = ref 0 in
  if Array.length Sys.argv > 3 && Sys.argv.(3) <> "-" then (let ic = open_in_bin Sys.argv.(3) in let (st, n) : T4C.coq_FastState * int = Marshal.from_channel ic in close_in ic; s := st; i := n);
  let lim = int_of_string Sys.argv.(2) in
  let ck = if Array.length Sys.argv > 4 then Some Sys.argv.(4) else None in
  let nextck = ref (Unix.gettimeofday () +. 600.) in
  let sigs : (string, int * int) Hashtbl.t = Hashtbl.create 100 in   (* signature -> count, first fast *)
  let dctx : (string, int * int) Hashtbl.t = Hashtbl.create 100 in   (* D-reading-0 context -> count, first *)
  let modes : (string, int) Hashtbl.t = Hashtbl.create 20 in
  let bump h k v = match Hashtbl.find_opt h k with Some (c, f) -> Hashtbl.replace h k (c+1, f) | None -> Hashtbl.replace h k (1, v) in
  let cur = Buffer.create 256 and entry = ref "" and start = ref 0 and startwin = ref "" and inraw = ref false and prev = ref "start" in
  let fin = ref false and t0 = Unix.gettimeofday () in
  let report () =
    Printf.printf "== at fast %d (%.0fs)\nmodes:" !i (Unix.gettimeofday () -. t0);
    Hashtbl.iter (fun k v -> Printf.printf " %s=%d" k v) modes; print_newline ();
    Printf.printf "D-reading-0 contexts (far side 4 cells, nearest first):\n";
    Hashtbl.iter (fun k (c, f) -> Printf.printf "  %s  x%d  first fast %d\n" k c f) dctx;
    Printf.printf "%d raw stretch signatures\n%!" (Hashtbl.length sigs) in
  while not !fin && !i < lim do
    let m = mshort !s in
    Hashtbl.replace modes m (1 + Option.value ~default:0 (Hashtbl.find_opt modes m));
    (match T4C.fs_mode !s with
     | T4C.RAW (q, d) ->
       let rd = if d = R then List.hd (rightbits 1 !s) else List.hd (leftbits 1 !s) in
       if not !inraw then (inraw := true; Buffer.clear cur; entry := !prev; start := !i; startwin := window !s);
       Buffer.add_string cur (Printf.sprintf "%s%d " m rd);
       let tk = Printf.sprintf "%s%d" m rd in
       Hashtbl.replace modes tk (1 + Option.value ~default:0 (Hashtbl.find_opt modes tk));
       (* leftward chain B<0 -> C<0 -> D<0: the only raw route to a halt.  Record the cells beyond the read one. *)
       if d = L && rd = 0 && (q = B || q = C) then begin
         let far = List.tl (leftbits 5 !s) in
         let k = Printf.sprintf "%s read0 far=%s" m (bstr far) in
         if not (Hashtbl.mem dctx k) then Printf.printf "NEW leftward-0 context %s at fast %d win %s\n%!" k !i (window !s);
         bump dctx k !i end;
       if q = D && rd = 0 then begin
         let far = if d = R then leftbits 4 !s else List.tl (leftbits 5 !s) in
         let k = Printf.sprintf "D%s read0 far=%s" m (bstr far) in
         if not (Hashtbl.mem dctx k) then Printf.printf "NEW D0 context %s at fast %d win %s\n%!" k !i (window !s);
         bump dctx k !i;
         if List.hd far = 1 then Printf.printf "HALT: D reads 0 with a 1 beside it at fast %d\n%!" !i
       end
     | _ ->
       if !inraw then begin
         inraw := false;
         let toks = String.split_on_char ' ' (String.trim (Buffer.contents cur)) in
         let rec rle acc = function [] -> List.rev acc | t :: r -> (match acc with (u, c) :: a when u = t -> rle ((u, c+1) :: a) r | _ -> rle ((t, 1) :: acc) r) in
         let body = String.concat " " (List.map (fun (t, c) -> if c = 1 then t else if c <= 3 then t ^ "^" ^ string_of_int c else t ^ "^n") (rle [] toks)) in
         let sg = Printf.sprintf "%s -> %s -> %s" !entry body m in
         if not (Hashtbl.mem sigs sg) then Printf.printf "NEW stretch #%d at fast %d (len %d) win %s : %s\n%!" (Hashtbl.length sigs) !start (!i - !start) !startwin sg;
         if not (Hashtbl.mem sigs sg) then Printf.printf "   exit win %s\n%!" (window !s);
         bump sigs sg !start;
         let n = List.fold_left (fun acc (t, c) -> if t = "A>1" then Stdlib.max acc c else acc) 0 (rle [] toks) in
         Printf.printf "STRETCH at fast %d len %d A>1-run %d : %s\n%!" !start (!i - !start) n sg
       end;
       prev := m);
    (match T4C.stepFast !s with None -> fin := true | Some s' -> s := s'; incr i);
    if !i mod 1000 = 0 && Unix.gettimeofday () > !nextck then begin nextck := Unix.gettimeofday () +. 600.;
      match ck with None -> () | Some f -> let oc = open_out_bin (f ^ ".tmp") in Marshal.to_channel oc (!s, !i) []; close_out oc; Sys.rename (f ^ ".tmp") f end;
    if !i mod 1000000 = 0 then report ()
  done;
  report ();
  Printf.printf "signature counts:\n";
  let l = Hashtbl.fold (fun k (c, f) acc -> (f, c, k) :: acc) sigs [] |> List.sort compare in
  List.iter (fun (f, c, k) -> Printf.printf "  x%d first %d : %s\n" c f k) l;
  Printf.printf "end at %d stopped=%b\n" !i !fin
