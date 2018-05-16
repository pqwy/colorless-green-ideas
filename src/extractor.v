Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Require Import Nat.
Require Prelude Sig Crypto Proto.

Extract Inductive Prelude.result => "result" ["Ok" "Error"].

(* Extraction "run/src/generated.ml" Proto.Make_proto. *)
Extraction "run/src/generated.ml" Proto.Make_proto Control.Coeff.

