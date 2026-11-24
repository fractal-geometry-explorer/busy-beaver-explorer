Require Export Ascii String.
Require Export PeanoNat NArith.
From BusyCoq Require Import RWLAcc BBinf.
From BusyCoq Require Import IndHint_inf.

Module RWLAcc_inf := RWLAcc BBinf.

Definition rexec (ls:list string) : unit :=
match ls with
| bsz::mnc::T::tms::nil =>
  let tm := TM'_from_str (pr tms tms) in
  let bsz := Nat.of_uint (Decimal_uint_of_str bsz) in
  let mnc := N.of_uint (Decimal_uint_of_str mnc) in
  let T := N.of_uint (Decimal_uint_of_str T) in
  if RWLAcc_inf.decide_nonhalt tm bsz 3200 true mnc T then pr tt "nonhalting" else
  match RWLAcc_inf.decide_halt tm bsz 3200 true mnc T with
  | Some _ => pr tt "halts"
  | None => pr tt "failed to decide"
  end
| _ => pr tt "usage: bsz mnc T tm"
end.

Require Import Extraction ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlNativeString.
Extract Constant PArray.array "'a" => "'a Parray.t".
Extraction NoInline PArray.array.
Extract Constant pr =>
  "fun x s ->
     Printf.printf ""[%.3f s] %s\n%!"" (Sys.time ()) s;
     x".
Time Extraction "RWLAccX" rexec.
