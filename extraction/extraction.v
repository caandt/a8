From a8 Require Import Rewrite.
Require Import Extraction ExtrOCamlInt63 ExtrOcamlBasic Uint63 Sint63.

Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "Rewrite" rw.
