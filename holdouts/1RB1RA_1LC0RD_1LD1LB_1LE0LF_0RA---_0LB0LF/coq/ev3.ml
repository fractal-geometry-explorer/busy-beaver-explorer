(* ev3 START N: classify every entry into RAW mode by (state, dir, first 8 left cells, first 8 right cells) *)
open T4ceng
let rec popn k l = if k = 0 then "" else match T4C.runs_pop l with Pair (b, r) -> (if b = S1 then "1" else "0") ^ popn (k-1) r
let qs = function A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F"
let rec syms = function Nil -> "" | Cons (S0, r) -> "0" ^ syms r | Cons (S1, r) -> "1" ^ syms r
let rec take k = function Nil -> "" | Cons (S0, r) -> if k=0 then "" else "0" ^ take (k-1) r | Cons (S1, r) -> if k=0 then "" else "1" ^ take (k-1) r
let () =
  let s = ref (match Sys.argv.(1) with "A" -> T4C.initFastA | "B" -> T4C.initFastB | "D" -> T4C.initFastD | _ -> T4C.initFastC) and i = ref 0 in
  let lim = int_of_string Sys.argv.(2) and fin = ref false and inraw = ref true in
  let h = Hashtbl.create 100 in
  while not !fin && !i < lim do
    (match T4C.fs_mode !s with
     | T4C.RAW (q, d) ->
       if not !inraw then begin
         let rec rp k rt = if k = 0 then "" else match T4C.popBitRTape rt with Pair (b, rt') -> (if b = S1 then "1" else "0") ^ rp (k-1) rt' in
         let r = rp 8 (T4C.fs_R !s) in
         let key = Printf.sprintf "%s%s L=%s R=%s" (qs q) (if d = L then "<" else ">") (popn 8 (T4C.fs_L !s)) r in
         (match Hashtbl.find_opt h key with None -> Hashtbl.add h key (1, !i); Printf.printf "new %d %s\n%!" !i key | Some (c, f) -> Hashtbl.replace h key (c+1, f)) end;
       inraw := true
     | _ -> inraw := false);
    (match T4C.stepFast !s with None -> fin := true | Some s' -> s := s'; incr i)
  done;
  Printf.printf "end %d stopped %b\n" !i !fin;
  Hashtbl.iter (fun k (c, f) -> Printf.printf "%8d first %d  %s\n" c f k) h
