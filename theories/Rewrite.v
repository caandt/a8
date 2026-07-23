From stdpp Require Import gmap.
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
  devs: list int;
  rets: list int;
}.

Fixpoint index{A} {eqd : EqDecision A} l x i :=
  match l with
  | nil => None
  | a::t => if eqd a x then Some i else index t x (succ i)
  end.

Section InstRewriter.
  Variable hook : data -> i_data -> option (list int) -> option (list int).
  Variable dat : data.
  Variable isn : i_data.
  Notation rel := dat.(rel).
  Notation i := (isn.(i)).
  Notation i' := (rel i).
  Notation lbl := (dat.(pol) i).
  Notation dset := (ith dat.(dsets) lbl orelse []).
  Notation tbl := (ith dat.(tc) lbl orelse (Hash.H_UBFX 0 1, nil, 0)).
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
  Definition tmpreg n := if n =? 0 then 1 else 0.
  Definition rw_BR Rn :=
    let tmp := tmpreg Rn in
    rpad (
      [Asm.PUSH2 tmp 31] ++
      tbl_lookup Rn tmp ++
      [Asm.POP2 tmp 31; isn.(n)]
    ) 10 UDF.
  Definition rw_BLR Rn :=
    let tmp := tmpreg Rn in
    rpad (
      [Asm.PUSH2 tmp 31] ++
      tbl_lookup Rn tmp ++
      [Asm.POP2 tmp 31]
    ) 9 NOP ++ [isn.(n)].
  Definition rw_RET Rn :=
    let tmp := tmpreg Rn in
    rpad (
      [Asm.PUSH2 tmp 31] ++
      tbl_lookup Rn tmp ++
      [Asm.POP2 tmp 31; isn.(n)]
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
  Section PolHook.
    Definition call_polhook Rn :=
      let call :=
        [ Asm.PUSH2 Rn 30
        ; Asm.PUSH2 0 1
        ; Asm.MOV_small ((index dat.(rets) i 0) orelse 999999999) 0
        ; Asm.BL (i'+3) (dat.(ai)+2) orelse UDF
        ; Asm.POP2 Rn (30 + (Rn =? 30)) ] in
      match isn.(t) with
      | BLR _ => rpad call 9 NOP ++ [isn.(n)]
      | _ => rpad (call ++ [isn.(n)]) 10 UDF
      end.
    Definition polhook chunk :=
      match isn.(t) with
      | BR Rn | BLR Rn | RET Rn => Some (call_polhook Rn)
      | _ => chunk
      end.
  End PolHook.
End InstRewriter.

Fixpoint retlist isns (i:int) l :=
  match isns with
  | nil => rev l
  | a::isns =>
      match a.(t) with
      | BR _ | BLR _ | RET _ =>
          retlist isns (i+1) (i::l)
      | _ => retlist isns (i+1) l
      end
  end.
Definition compute_rel idxs bi :=
  let ei := bi + PArray.length idxs - 1 in
  λ x, if (bi <=? x) && (x <? ei)
       then PArray.get idxs (x - bi)
       else x.
Definition compute_tables rel ai bti dsets :=
  maybe_map (λ D,
    let D' := map_single rel D in
    Hash.find_hash D D' <&> λ h,
    (h, Hash.compute_table_m h ai D D')
  ) dsets <&> λ l,
    let lens := map (λ x, len (snd x) << 1) l in
    combine l (list_of_array (csum bti lens)).
(* more efficient way to encode lens *)
Fixpoint deviations idx cum lens :=
  match lens with
  | nil => nil
  | size::t =>
      let dev := size - 1 in
      let next_cum_dev := cum + dev in
      if size =? 1 then deviations (idx+1) next_cum_dev t
      else idx::next_cum_dev::deviations (idx+1) next_cum_dev t
  end.
Definition global_data code bi bi' pol dsets abtlen :=
  let isns := mapi (λ i n, {| i := bi + i; n := n; t := decode n |}) code in
  let lens := map len_inst isns in
  let idxs := csum bi' lens in
  let rel := compute_rel idxs bi in
  let ai := pad_to idxs.[PArray.length idxs - 1] 10 in
  let bti := pad_to (ai + abtlen) 10 in
  let devs := deviations 0 0 lens in
  let rets := retlist isns bi [] in
  compute_tables rel ai bti dsets <&> λ tc,
  {| bi := bi; bi' := bi'; bti := bti; ai := ai;
    code := code; isns := isns; pol := pol; dsets := dsets;
    rel := rel; tc := tc; devs := devs; rets := rets; |}.
Definition rw hook d :=
  maybe_map (rw_inst hook d) d.(isns).
Definition null_rw := rw (λ _ _ x, x).
