From Rewriter Require Import Rewrite.
Require Import Extraction ExtrOCamlInt63 ExtrOcamlBasic ExtrOCamlPArray ExtrOCamlPString PArray.

Extraction Language OCaml.
Extract Constant array "'a" => "'a Parray.t".
Extract Constant List.map => "(fun f l -> Parmap.parmap f (Parmap.L l))".
Extract Constant Util.mapi => "(fun f l -> Parmap.parmapi (fun i -> f (Uint63.of_int i)) (Parmap.L l))".
Extract Constant Util.len => "(fun x -> Uint63.of_int (List.length x))".
Extract Constant Hash.sort_uniq => "(List.sort_uniq (fun (a1,a2) (b1,b2) ->
  match Uint63.compare a1 a2 with
  | 0 -> Uint63.compare b2 b1
  | c -> c))".
(* Extract Constant Util.maybe_map => "(fun f l -> Parmap.parmapfold f (Parmap.L l) (maybe_op List.cons) (Some []) (maybe_op List.append))". *)

Set Extraction Output Directory ".".
Extraction "Rewriter" rw.
