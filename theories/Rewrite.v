Require Import Util.
Require Hash Decode Asm.
Import Decode(ityp(..),decode).
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

  (* the list of all sets of permitted destination indices *)
  dsets: list (list int);
  (* for each dset, (hash, table content, table index) *)
  tc: list (Hash.hash * list int * int);
  (* a mapping from instruction indices to an index of the dsets list,
     describing what destinations are permitted jump targets *)
  pol: int -> int;

  (* a mapping from original indices to new indices *)
  rel: int -> int;
}.
Structure i_data := {
  i: int;
  n: int;
  t: ityp;
}.
Definition sext n w := asr (n << (63 - w)) (63 - w).

Section InstRewriter.
  Variable hook : i_data -> option (list int) -> option (list int).
  Variable dat : data.
  Variable isn : i_data.
  Notation rel := dat.(rel).
  Notation i := (isn.(i)).
  Notation i' := (rel i).
  Notation lbl := (dat.(pol) i).
  Notation dset := (nth (to_nat lbl) dat.(dsets) nil).
  Notation tbl := (nth (to_nat lbl) dat.(tc) (Hash.H_UBFX 0 0, nil, 0)).
  Notation ti := (snd tbl).
  Notation h := (fst (fst tbl)).
  Section Length.
    Definition len_ADR imm Rd :=
      let dst := (i<<2) + sext imm 21 in
      of_nat (length (Asm.MOV dst Rd)).
    Definition len_ADRP imm Rd :=
      let dst := (i<<2 land 0xfff) + sext (imm << 12) 33 in
      of_nat (length (Asm.MOV dst Rd)).
    Definition len_inst :=
      match isn.(t) with
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

  Definition tbl_lookup Rdst Rtmp :=
    Hash.hash_code h Rdst ++
    Asm.MOV ti Rtmp ++
    nil.
  Definition rw_inst :=
    hook isn match isn.(t) with
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
Fixpoint csum acc base lst :=
  match lst with
  | nil => rev acc
  | a::t => csum (base+a::acc) (base+a) t
  end.
Definition compute_tables rel ai bti dsets :=
  maybe_map (\D,
    let D' := map rel D in
    Hash.find_hash D D' >>= \h,
    Some (h, Hash.compute_table_m h ai D D')
  ) dsets >>= \l,
    let lens := map (\x, len (snd x)) l in
    Some (combine l (csum [] bti lens)).
Definition rw hook pol dsets code bi bi' bti ai :=
  let isns := mapi (\i, \n, {| i := bi + i; n := n; t := decode n |}) code in
  let rel := compute_rel code bi bi' in
  compute_tables rel ai bti dsets >>= \tc,
  let d := {| bi := bi; bi' := bi'; bti := bti; ai := ai; code := code;
    pol := pol; dsets := dsets; rel := rel; tc := tc; |} in
  maybe_map (rw_inst hook d) isns >>= \code',
  let tbls := map (\(_,t,_),t) tc in
  Some (code', tbls, rel).
