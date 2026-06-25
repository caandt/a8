From Rewriter Require Import Rewrite.
Require Import Extraction ExtrOCamlInt63 ExtrOcamlBasic.

Extraction Language OCaml.
Set Extraction Output Directory ".".
Extract Constant List.map => "(fun f l -> Parmap.parmap f (Parmap.L l))".
Extract Constant Util.mapi => "(fun f l -> Parmap.parmapi (fun i -> f (Uint63.of_int i)) (Parmap.L l))".
(* Extract Constant Util.maybe_map => "(fun f l -> Parmap.parmapfold f (Parmap.L l) (maybe_op List.cons) (Some []) (maybe_op List.append))". *)
Extraction "Rewriter" rw.
