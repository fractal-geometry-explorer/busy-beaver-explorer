(* sdigest: the same state digest as zdigest.ml, for the engine of build.sh (Coq numbers as bit lists); used by cksdigest *)
open T4ceng
let rec pz = function XH -> Z.one | XO p -> Z.shift_left (pz p) 1 | XI p -> Z.succ (Z.shift_left (pz p) 1)
let ns x = match x with N0 -> "0" | Npos p -> Z.to_string (pz p)
let rec tl = function Nil -> [] | Cons (a, t) -> a :: tl t
let ds b l = List.iter (fun (Pair (a, k)) -> Buffer.add_string b (ns a ^ "^" ^ ns k ^ ",")) (tl l)
let sym = function S0 -> "0" | S1 -> "1"
let sw b = function
  | T4C.SW_raw l -> Buffer.add_string b ("r" ^ String.concat "" (List.map sym (tl l)))
  | T4C.SW_D n -> Buffer.add_string b ("D" ^ ns n) | T4C.SW_S n -> Buffer.add_string b ("S" ^ ns n)
  | T4C.SW_PL n -> Buffer.add_string b ("P" ^ ns n) | T4C.SW_DEF (a, k) -> Buffer.add_string b ("E" ^ ns a ^ "." ^ ns k)
  | T4C.SW_DF d -> Buffer.add_string b "F"; ds b d | T4C.SW_DB d -> Buffer.add_string b "B"; ds b d
let runs b l = List.iter (fun (Pair (w, n)) -> sw b w; Buffer.add_string b ("*" ^ ns n ^ ";")) (tl l)
let qs = function A->"A"|B->"B"|C->"C"|D->"D"|E->"E"|F->"F"
let st (s : T4C.coq_FastState) =
  let b = Buffer.create 100000 in
  runs b s.T4C.fs_L; Buffer.add_string b "|";
  runs b s.T4C.fs_R.T4C.r_raw; Buffer.add_string b "|"; ds b s.T4C.fs_R.T4C.d_front; Buffer.add_string b "|";
  ds b s.T4C.fs_R.T4C.d_back; Buffer.add_string b "|"; runs b s.T4C.fs_R.T4C.r_tail; Buffer.add_string b "|";
  Buffer.add_string b (match s.T4C.fs_mode with T4C.MR -> "MR" | T4C.ML -> "ML" | T4C.MJ -> "MJ"
    | T4C.RAW (q, d) -> "RAW" ^ qs q ^ (if d = L then "L" else "R"));
  Digest.to_hex (Digest.string (Buffer.contents b))
let init = function "A" -> T4C.initFastA | "B" -> T4C.initFastB | "C" -> T4C.initFastC | "D" -> T4C.initFastD | _ -> failwith "start"
let main () =
  let pts = List.map int_of_string (String.split_on_char ',' Sys.argv.(2)) in
  let s = ref (init Sys.argv.(1)) and i = ref 0 in
  let t0 = Unix.gettimeofday () in
  List.iter (fun p ->
    while !i < p do (match T4C.stepFast !s with None -> Printf.printf "STOP at %d\n%!" !i; exit 0 | Some s' -> s := s'; incr i) done;
    Printf.printf "%d %s %.1fs\n%!" p (st !s) (Unix.gettimeofday () -. t0)) pts
