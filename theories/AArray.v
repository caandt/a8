Require Import PArray PrimInt63 Uint63.

Open Scope uint63.

Record aarray A := {
  subarrs: array (array A);
  default: A;
  length: int
}.
Arguments subarrs {_}.
Arguments default {_}.
Arguments length {_}.
Definition lsrval := 21.
Definition subarrsz := 1 << lsrval.
Definition landval := pred subarrsz.
Definition make{A} length default :=
  let subarrs :=
    if is_zero length then PArray.make 0 (PArray.make 0 default)
    else PArray.make (succ (lsr (pred length) lsrval)) (@PArray.make A subarrsz default) in
  {| subarrs := subarrs; default := default; length := length |}.
Definition get{A} arr i :=
  let outer_idx := i >> lsrval in
  let inner_idx := i land landval in
  let subarr := PArray.get arr.(subarrs A) outer_idx in
  PArray.get subarr inner_idx.
Definition set{A} arr i v :=
  let outer_idx := i >> lsrval in
  let inner_idx := i land landval in
  let subarr := PArray.get arr.(subarrs A) outer_idx in
  let subarr' := PArray.set subarr inner_idx v in
  let subarrs := PArray.set arr.(subarrs A) outer_idx subarr' in
  {| subarrs := subarrs; default := default arr; length := length arr |}.
