(* runz START MAXFAST CHECKPOINT: the PR 93 engine extracted with Coq's binary numbers realized by Zarith
   (ExtrOcamlZBigInt), run from blank tape in START.  Saves (state, fast step, raw-entry table) every 10 minutes
   and resumes from CHECKPOINT.  Like ev3, every entry into raw mode is classified by state, direction and the
   8 nearest cells on each side; a new kind is printed when first seen. *)
open T4ceng
let bits x = Z.numbits x
let qs = function A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F"
let mode s = match T4C.fs_mode s with T4C.MR -> "MR" | T4C.ML -> "ML" | T4C.MJ -> "MJ"
  | T4C.RAW (q, d) -> "RAW " ^ qs q ^ (if d = L then "L" else "R")
let init = function "A" -> T4C.initFastA | "B" -> T4C.initFastB | "C" -> T4C.initFastC | "D" -> T4C.initFastD | _ -> failwith "START is A, B, C or D"
let rec popn k l = if k = 0 then "" else let (b, r) = T4C.runs_pop l in (if b = S1 then "1" else "0") ^ popn (k-1) r
let rec rp k rt = if k = 0 then "" else let (b, rt') = T4C.popBitRTape rt in (if b = S1 then "1" else "0") ^ rp (k-1) rt'
let () =
  let ck = Sys.argv.(3) in
  let s = ref (init Sys.argv.(1)) and i = ref 0 and fin = ref false and inraw = ref true in
  let h : (string, int * int) Hashtbl.t ref = ref (Hashtbl.create 100) in
  if Sys.file_exists ck then begin
    let ic = open_in_bin ck in let (st, n, hh) : T4C.coq_FastState * int * (string, int * int) Hashtbl.t = Marshal.from_channel ic in
    close_in ic; s := st; i := n; h := hh; Printf.printf "resumed at fast step %d\n%!" n end;
  let save () = let oc = open_out_bin (ck ^ ".tmp") in Marshal.to_channel oc (!s, !i, !h) []; close_out oc; Sys.rename (ck ^ ".tmp") ck in
  let nextsave = ref (Unix.gettimeofday () +. 180.) in
  let lim = int_of_string Sys.argv.(2) in
  let t0 = Unix.gettimeofday () in
  let next = ref (t0 +. 60.) in
  let report what = Printf.printf "%s %d  %.1fs  runs %s  cells 2^%d  mode %s\n%!" what !i (Unix.gettimeofday () -. t0)
      (Big_int_Z.string_of_big_int (T4C.fs_size !s)) (bits (T4C.fs_cells !s) - 1) (mode !s) in
  while not !fin && !i < lim do
    (match T4C.fs_mode !s with
     | T4C.RAW (q, d) ->
       if not !inraw then begin
         let key = Printf.sprintf "%s%s L=%s R=%s" (qs q) (if d = L then "<" else ">") (popn 8 (T4C.fs_L !s)) (rp 8 (T4C.fs_R !s)) in
         (match Hashtbl.find_opt !h key with None -> Hashtbl.add !h key (1, !i); Printf.printf "new %d %s\n%!" !i key
          | Some (c, f) -> Hashtbl.replace !h key (c+1, f)) end;
       inraw := true
     | _ -> inraw := false);
    (match T4C.stepFast !s with None -> fin := true | Some s' -> s := s'; incr i);
    if not !fin && Unix.gettimeofday () > !nextsave then begin
      save (); nextsave := Unix.gettimeofday () +. 180.;
      Printf.printf "raw-entry counts at %d:" !i; Hashtbl.iter (fun k (c, f) -> Printf.printf " [%s]=%d" k c) !h; print_newline () end;
    if not !fin && (!i land (!i - 1) = 0 || !i mod 1000000 = 0 || Unix.gettimeofday () > !next) then (report "fast step"; next := Unix.gettimeofday () +. 60.)
  done;
  save ();
  if !fin then report "engine stopped (a halt) at fast step" else report "no stop by fast step";
  Hashtbl.iter (fun k (c, f) -> Printf.printf "%8d first %d  %s\n" c f k) !h
