(* Run the extracted T4 engine from a blank tape.  usage: run START MAXFAST [CHECKPOINT]   (START = B, C or D)
   With CHECKPOINT, the state is saved there (OCaml Marshal) every 10 minutes and the run resumes from it. *)
open T4ceng
let rec n2f = function N0 -> 0.0 | Npos p -> let rec pf = function XH -> 1.0 | XO q -> 2.0 *. pf q | XI q -> 2.0 *. pf q +. 1.0 in pf p
let rec bits = function N0 -> 0 | Npos p -> let rec pb = function XH -> 1 | XO q | XI q -> 1 + pb q in pb p
let qs = function A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F"
let mode s = match T4C.fs_mode s with T4C.MR -> "MR" | T4C.ML -> "ML" | T4C.MJ -> "MJ"
  | T4C.RAW (q, d) -> "RAW " ^ qs q ^ (if d = L then "L" else "R")
let init = function "A" -> T4C.initFastA | "B" -> T4C.initFastB | "C" -> T4C.initFastC | "D" -> T4C.initFastD | _ -> failwith "START is A, B, C or D"
let () =
  let ck = if Array.length Sys.argv > 3 then Some Sys.argv.(3) else None in
  let s = ref (init Sys.argv.(1)) and i = ref 0 and fin = ref false in
  (match ck with
   | Some f when Sys.file_exists f ->
     let ic = open_in_bin f in let (st, n) : T4C.coq_FastState * int = Marshal.from_channel ic in
     close_in ic; s := st; i := n; Printf.printf "resumed at fast step %d\n%!" n
   | _ -> ());
  let save () = match ck with
    | None -> ()
    | Some f -> let oc = open_out_bin (f ^ ".tmp") in Marshal.to_channel oc (!s, !i) []; close_out oc; Sys.rename (f ^ ".tmp") f in
  let nextsave = ref (Unix.gettimeofday () +. 600.) in
  let lim = int_of_string Sys.argv.(2) in
  let t0 = Unix.gettimeofday () in
  let next = ref (t0 +. 60.) in
  let report what = Printf.printf "%s %d  %.1fs  runs %.0f  cells 2^%d  mode %s\n%!" what !i (Unix.gettimeofday () -. t0) (n2f (T4C.fs_size !s)) (bits (T4C.fs_cells !s) - 1) (mode !s) in
  while not !fin && !i < lim do
    (match T4C.stepFast !s with None -> fin := true | Some s' -> s := s'; incr i);
    if not !fin && Unix.gettimeofday () > !nextsave then (save (); nextsave := Unix.gettimeofday () +. 600.);
    if not !fin && (!i land (!i - 1) = 0 || !i mod 1000000 = 0 || Unix.gettimeofday () > !next) then (report "fast step"; next := Unix.gettimeofday () +. 60.)
  done;
  (* stepFast = None: in the Coq file (H155900.v) stepFast_spec proves that the configuration then halts.
     The tape is far too long to decode here; peek.ml prints the stopped state from the checkpoint. *)
  if !fin then report "engine stopped (a halt) at fast step"
  else report "no stop by fast step"
