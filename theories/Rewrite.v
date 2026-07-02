Require Import Util.
Require Hash Decode Asm.
Import Decode(ityp(..),decode).
Import ListNotations.

Structure i_data := {
  i: int;
  n: int;
  t: ityp;
}.
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
  isns: list i_data;

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

Section InstRewriter.
  Variable hook : data -> i_data -> option (list int) -> option (list int).
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
    Definition len_ADR imm :=
      let dst := (i<<2) + sext imm 21 in
      Asm.b16c dst.
    Definition len_ADRP imm :=
      let dst := (i<<2 land (max_int lxor 0xfff)) + sext (imm << 12) 33 in
      Asm.b16c dst.
    Definition len_inst :=
      match isn.(t) with
      | ADR imm Rd => len_ADR imm
      | ADRP imm Rd => len_ADRP imm
      | BR _ | BLR _ | RET _ => 10
      | _ => 1
      end.
  End Length.
  Definition UDF := 0.
  Definition NOP := 0xd503201f.
  Definition rw_ADR imm Rd :=
    let dst := (i<<2) + sext imm 21 in
    Asm.MOV dst Rd.
  Definition rw_ADRP imm Rd :=
    let dst := (i<<2 land (max_int lxor 0xfff)) + sext (imm << 12) 33 in
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
    Asm.MOV (ti<<2) Rtmp ++
    [Asm.LDR_r64 Rdst Rtmp Rdst].
  Definition rw_BR Rn :=
    rpad (
      [Asm.PUSH2 (Rn+1) (Rn+2)] ++
      tbl_lookup Rn (Rn+1) ++
      [Asm.POP2 (Rn+1) (Rn+2); isn.(n)]
    ) 10 UDF.
  Definition rw_BLR Rn :=
    rpad (
      [Asm.PUSH2 (Rn+1) (Rn+2)] ++
      tbl_lookup Rn (Rn+1) ++
      [Asm.POP2 (Rn+1) (Rn+2)]
    ) 9 NOP ++ [isn.(n)].
  Definition rw_RET Rn :=
    rpad (
      [Asm.PUSH2 (Rn-1) (Rn-2)] ++
      tbl_lookup Rn (Rn-1) ++
      [Asm.POP2 (Rn-1) (Rn-2); isn.(n)]
    ) 10 UDF.
  Definition rw_inst :=
    hook dat isn match isn.(t) with
    | ignore => Some [isn.(n)]
    | invalid => Some [goto_abort]
    | ADR imm Rd => Some (rw_ADR imm Rd)
    | ADRP imm Rd => Some (rw_ADRP imm Rd)
    | Bcond imm cond => Some [rw_Bcond imm cond orelse UDF]
    | B imm => Some [rw_B imm orelse UDF]
    | BL imm => Some [rw_BL imm orelse UDF]
    | CBZ sf op imm Rt => Some [rw_CBZ sf op imm Rt orelse UDF]
    | TBZ b5 op b40 imm Rt => Some [rw_TBZ b5 op b40 imm Rt orelse UDF]
    | BR Rn => Some (rw_BR Rn)
    | BLR Rn => Some (rw_BLR Rn)
    | RET Rn => Some (rw_RET Rn)
    end.
End InstRewriter.

Definition decode_isns code bi :=
  mapi (λ i n, {| i := bi + i; n := n; t := decode n |}) code.
Definition compute_idxs isns bi' :=
  let lens := map len_inst isns in
  csum bi' lens.
Definition compute_rel idxs bi :=
  let ei := bi + PArray.length idxs - 1 in
  λ x, if (bi <=? x) && (x <? ei)
       then PArray.get idxs (x - bi)
       else x.
Definition compute_tables rel ai bti dsets :=
  maybe_map (λ D,
    let D' := map rel D in
    Hash.find_hash D D' <&> λ h,
    (h, Hash.compute_table_a h ai D D')
  ) dsets <&> λ l,
    let lens := map (λ x, len (snd x)) l in
    combine l (list_of_array (csum bti lens)).

Definition global_data code bi bi' pol dsets abtlen :=
  let isns := decode_isns code bi in
  let idxs := compute_idxs isns bi' in
  let rel := compute_rel idxs bi in
  let ai := idxs.[PArray.length idxs - 1] in
  let bti := ai + abtlen in
  compute_tables rel ai bti dsets <&> λ tc,
  {| bi := bi; bi' := bi'; bti := bti; ai := ai;
    code := code; isns := isns; pol := pol; dsets := dsets;
    rel := rel; tc := tc; |}.
Definition rw hook d :=
  maybe_map (rw_inst hook d) d.(isns).
Definition null_rw := rw (λ _ _ x, x).
