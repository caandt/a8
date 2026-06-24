From Rewriter Require Import Rewrite.
Require Import Extraction ExtrOCamlInt63 ExtrOcamlBasic.

Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "Rewriter" rw.
