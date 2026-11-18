(* Check the engine against direct simulation: after each fast step, run the source table (busycoq's src_tm,
   mirrored and renamed from the holdout) until it reaches exactly the engine's configuration.
   usage: validate START MAXFAST MAXDIRECT *)
open T4ceng
let src = "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---"
let tr = Array.make 12 (0,0,0) and halt = Array.make 12 false
let () = String.split_on_char '_' src |> List.iteri (fun q row ->
  for b = 0 to 1 do let t = String.sub row (3*b) 3 in
    if t.[0] = '-' then halt.(2*q+b) <- true
    else tr.(2*q+b) <- (Char.code t.[0] - 48, (if t.[1]='R' then 1 else -1), Char.code t.[2] - 65) done)
let w = 1 lsl 27
let tape = Bytes.make w '\000'
let p = ref (w/2) and q = ref 0 and ones = ref 0 and steps = ref 0
let tol l = let rec go acc = function Nil -> List.rev acc | Cons (x, r) -> go ((if x = S1 then 1 else 0) :: acc) r in go [] l
let qi = function A->0|B->1|C->2|D->3|E->4|F->5
let decode s =
  match T4C.fs_list s with Pair (Pair (Pair (l, st), hl), r) ->
    let l = tol l and r = tol r in
    let (lr, h, rr) = if hl = True then (match l with [] -> ([],0,r) | x::t -> (t,x,r))
                      else (match r with [] -> (l,0,[]) | x::t -> (l,x,t)) in
    (Array.of_list lr, h, Array.of_list rr, qi st)
let cnt a = Array.fold_left (+) 0 a
let matches (la,h,ra,st) tot =
  st = !q && tot = !ones && Char.code (Bytes.get tape !p) = h &&
  (let ok = ref true in
   Array.iteri (fun i x -> if !ok && Char.code (Bytes.get tape (!p-1-i)) <> x then ok := false) la;
   Array.iteri (fun i x -> if !ok && Char.code (Bytes.get tape (!p+1+i)) <> x then ok := false) ra; !ok)
let step () =
  let b = Char.code (Bytes.get tape !p) in
  let k = 2 * !q + b in
  if halt.(k) then false else begin
    let (nb, d, nq) = tr.(k) in
    ones := !ones + nb - b; Bytes.set tape !p (Char.chr nb); p := !p + d; q := nq; incr steps; true end
let () =
  let start = Sys.argv.(1) in
  q := (match start with "A" -> 0 | "B" -> 1 | "C" -> 2 | "D" -> 3 | _ -> failwith "START is A, B, C or D");
  let lim = int_of_string Sys.argv.(2) and maxdirect = int_of_string Sys.argv.(3) in
  let s = ref (match start with "A" -> T4C.initFastA | "B" -> T4C.initFastB | "C" -> T4C.initFastC | _ -> T4C.initFastD) in
  let i = ref 0 and stop = ref false in
  while not !stop && !i < lim do
    (match T4C.stepFast !s with
     | None -> Printf.printf "engine stopped at fast step %d\n" !i; stop := true
     | Some s' -> s := s');
    incr i;
    if not !stop then begin
      let (la,h,ra,_) as c = decode !s in
      let tot = cnt la + h + cnt ra in
      let found = ref (matches c tot) and halted = ref false in
      while not !found && not !halted && !steps < maxdirect do
        if step () then found := matches c tot else halted := true
      done;
      if !halted then (Printf.printf "direct run halted at step %d before fast step %d was reached\n" !steps !i; stop := true)
      else if not !found then (Printf.printf "agree: %d fast steps checked, %d direct steps\n" (!i - 1) !steps; stop := true)
      else if !i land (!i-1) = 0 then Printf.printf "fast %d = direct %d  (tape %d cells)\n%!" !i !steps (Array.length la + Array.length ra + 1)
    end
  done
