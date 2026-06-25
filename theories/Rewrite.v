Require Import Util.
Require Hash Decode Asm.
Import Decode(ityp(..)).
Import ListNotations.

Structure data := {
  (* the base index of the original text segment *)
  bi: int;
  (* the base index to place the new text segment *)
  bi': int;
  (* the base index to place tables *)
  bti: int;
  (* the index of the abort handler *)
  ai: int;
  (* the original text segment *)
  code: list int;
  (* a mapping from indices to sets of destination indices,
     describing the policy to be enforced *)
  pol: int -> list int;
  (* a mapping from original indices to new indices *)
  rel: int -> int;
  (* a mapping from destination sets to table indices *)
  tc: list int -> option (int * Hash.hash);
}.
Structure i_data := {
  i: int;
  n: int;
}.
Definition sext n w := asr (n << (63 - w)) (63 - w).

(* Notation "a ? b" := (match b with None => None | Some x => Some (a x) end) (at level 10, format "a  ? b"). *)
Section Debug.
  Variable debug_hook : i_data -> ityp -> ityp.
Section InstRewriter.
  Variable dat : data.
  Variable isn : i_data.
  Notation rel := (rel dat).
  Notation i := (isn.(i)).
  Notation i' := (rel i).
  Notation h := (tc dat (pol dat i)).
  Section Length.
    Definition len_ADR imm Rd :=
      let dst := (i<<2) + sext imm 21 in
      of_nat (length (Asm.MOV dst Rd)).
    Definition len_ADRP imm Rd :=
      let dst := (i<<2 land 0xfff) + sext (imm << 12) 33 in
      of_nat (length (Asm.MOV dst Rd)).
    Definition len_inst :=
      match Decode.decode isn.(n) with
      | ADR imm Rd => len_ADR imm Rd
      | ADRP imm Rd => len_ADRP imm Rd
      | _ => 1
      end.
  End Length.
  Definition UDF := 0.
  Definition rw_ADR imm Rd :=
    let dst := (i<<2) + sext imm 21 in
    Asm.MOV dst Rd.
  Definition rw_ADRP imm Rd :=
    let dst := (i<<2 land 0xfff) + sext (imm << 12) 33 in
    Asm.MOV dst Rd.
  Definition rw_B imm :=
    let dst := i + sext imm 26 in
    Asm.B i' (rel dst).
  Definition rw_BL imm :=
    let dst := i + sext imm 26 in
    Asm.BL i' (rel dst).
  Definition goto_abort :=
    Asm.BL i' dat.(ai) orelse UDF.
  Definition rw_Bcond imm cond :=
    let dst := i + sext imm 19 in
    Asm.Bcond i' (rel dst) cond.
  Definition rw_CBZ sf op imm Rt :=
    let dst := i + sext imm 19 in
    Asm.CBZ sf op i' (rel dst) Rt.
  Definition rw_TBZ b5 op b40 imm Rt :=
    let dst := i + sext imm 14 in
    Asm.TBZ b5 op b40 i' (rel dst) Rt.

  (* Definition tbl_lookup Rdst Rtmp := *)
  (*   obind h (\(ti, h), *)
  (*     Hash.hash_code h Rdst ++ *)
  (*     Asm.MOV ti Rtmp ++ *)
  (*     Asm. *)
  (*   ). *)
  Definition rw_inst :=
    let t := debug_hook isn (Decode.decode isn.(n)) in
    match t with
    | ignore => Some [isn.(n)]
    | invalid => Some [goto_abort]
    | ADR imm Rd => Some (rw_ADR imm Rd)
    | ADRP imm Rd => Some (rw_ADRP imm Rd)
    | Bcond imm cond => Some [rw_Bcond imm cond orelse UDF]
    | B imm => Some [rw_B imm orelse UDF]
    | BL imm => Some [rw_BL imm orelse UDF]
    | CBZ sf op imm Rt => Some [rw_CBZ sf op imm Rt orelse UDF]
    | TBZ b5 op b40 imm Rt => Some [rw_TBZ b5 op b40 imm Rt orelse UDF]
    | BR Rn => Some []
    | BLR Rn => Some []
    | RET Rn => Some []
    end.
End InstRewriter.

Definition chunklen (n: int) :=
  match Decode.decode n with
  | ignore
  | invalid => 1
  | _ => 0
  end.
Definition compute_rel
           (code: list int)
           (bi bi': int)
           :=
  fun x:int => x.

Definition compute_tables
           (code: list int)
           :=
  Some ([[1]], \x: list int,None:option (int*Hash.hash)).
Definition rw
           (pol: int -> list int)
           (code: list int)
           (bi bi' bti ai: int)
           :=
  let isns := mapi (fun i n => {| i := bi + i; n := n |}) code in
  let rel := compute_rel code bi bi' in
  match compute_tables code with | None => None | Some (tables, tc) =>
    let d := {|
      bi := bi;
      bi' := bi';
      bti := bti;
      ai := ai;
      code := code;
      pol := pol;
      rel := rel;
      tc := tc;
    |} in
    match maybe_map (rw_inst d) isns, Some [[1]] with
    | Some code', Some tbl => Some (code', tbl, rel)
    | _, _ => None
    end
  end.
End Debug.
