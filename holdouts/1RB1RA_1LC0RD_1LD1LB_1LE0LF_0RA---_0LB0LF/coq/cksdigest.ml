let () = let ic = open_in_bin Sys.argv.(1) in let (st, n) : T4ceng.T4C.coq_FastState * int = Marshal.from_channel ic in
  Printf.printf "%d %s\n" n (Sdigest.st st)
