From stdpp Require Import gmap.
Require Import Util.
Require Hash Decode Asm.
Import Decode(ityp(..),decode).
Import ListNotations.

Variant reloc :=
  | Raddr (i: int)
  | Rrt (i: int).
Variant isize :=
  | Sz1
  | Sz2
  | Sz3.
Definition intsize sz :=
  match sz with
  | Sz1 => 1
  | Sz2 => 2
  | Sz3 => 3
  end.
Variant list3 :=
  | Lst0
  | Lst1 (i1: int)
  | Lst2 (i1 i2: int)
  | Lst3 (i1 i2 i3: int).
Variant cinst :=
  | Inum (n: int)
  | Iimm (sz:isize) (r imm: int)
  | Itbl (r lbl: int)
  | Ihsh (r lbl: int)
  | Ib   (sz:isize) (t: ityp) (d: reloc).
Definition instsize inst :=
  match inst with
  | Inum _ => 1
  | Itbl _ _ | Ihsh _ _ => 2
  | Iimm sz _ _ | Ib sz _ _ => intsize sz
  end.
Record chunk A := C {
  cn: int;
  ci: int;
  ct: ityp;
  cd: A;
}.
Notation chunklist A := (list (chunk A)).
Arguments cn {_}.
Arguments ci {_}.
Arguments ct {_}.
Arguments cd {_}.
Arguments C {_}.

Record args := {
  code: list int;
  pol: int → int;
  dsets: list (list int);
  bi: int;
  bi': int;
  nrelax: nat;
  rtlen: int;
}.
Record data := {
  chunks: chunklist (list cinst);
  rel: int → int;
  ai: int;
  bti: int;
  tc: list (Hash.hash * list int * int);
  arg: args;
  rets: list int;
  devs: list int;
}.
Definition setd{A B} (c: chunk A) (d: B) := C c.(cn) c.(ci) c.(ct) (d).
Definition chunkmapi{A} rel (f: int -> cinst -> A) l :=
  map (λ c,
    let i := rel c.(ci) in
    let g j := f (i+j) in
    setd c (mapisz instsize g c.(cd))
  ) l.
Section ChunkGeneration.
  Variable a : args.
  Notation pol := a.(pol).
  Notation dsets := a.(dsets).
  Notation bi := a.(bi).
  Notation bi' := a.(bi').
  Section InstRewriter.
    Variable idx n : int.
    Notation i := (bi + idx).
    Notation t := (decode n).
    Notation lbl := (pol i).
    Notation dset := (ith dsets lbl orelse []).
    Definition rw_indirect Rn :=
      match dset with
      | [] => [Ib Sz1 (BL 0) (Rrt 0)]
      | [d] => [Iimm Sz3 Rn d; Inum n]
      | _ =>
          let Rtmp := b2i (is_zero Rn) in
          [ Inum (Asm.PUSH2 Rtmp 31)
          ; Ihsh Rn lbl
          ; Itbl Rtmp lbl
          ; Inum (Asm.LDR_r64 Rn Rtmp Rn)
          ; Inum (Asm.POP2 Rtmp 31)
          ; Inum n ]
      end.
    Definition rw_inst :=
      C n i t match t with
      | ignore => [Inum n]
      | invalid => [Ib Sz1 (BL 0) (Rrt 0)]
      | ADR imm Rd => [Iimm Sz2 Rd ((i<<2)+sext imm 21)]
      | ADRP imm Rd => [Iimm Sz3 Rd (clearlow12 (i<<2)+sext (imm<<12) 33)]
      | Bcond imm _ | CBZ _ _ imm _ => [Ib Sz2 t (Raddr (i+sext imm 19))]
      | B imm | BL imm => [Ib Sz1 t (Raddr (i+sext imm 26))]
      | TBZ _ _ _ imm _ => [Ib Sz2 t (Raddr (i+sext imm 14))]
      | BR Rn | BLR Rn | RET Rn => rw_indirect Rn
      end.
  End InstRewriter.
  Section Relaxation.
    Definition chunksize c := fold_left add (map_single instsize c.(cd)) 0.
    Definition makerel chunks :=
      let lens := map chunksize chunks in
      let idxs := csum bi' lens in
      let ei := bi + len chunks in
      λ x, if (bi <=? x) && (x <=? ei)
           then PArray.get idxs (x - bi)
           else x.
    Definition fits bw n := (lesb (-1<<(bw-1)) n) && (ltsb n (1<<(bw-1))).
    Definition relaxi rel i' inst :=
      match inst with
      | Iimm Sz1 _ _ => inst
      | Iimm _ r imm =>
          if (clearlow12 imm =? imm) && (fits 21 (asr imm 12-i'>>10)) then Iimm Sz1 r imm
          else if fits 21 (imm-i'<<2) then Iimm Sz1 r imm
          else if fits 21 (asr imm 12-i'>>10) then Iimm Sz2 r imm
          else if imm <? 1 << 32 then Iimm Sz2 r imm
          else inst
      | Ib Sz2 t (Raddr d) =>
          let bw := match t with
                    | Bcond _ _ | CBZ _ _ _ _ => 19
                    | TBZ _ _ _ _ _ => 14 | _ => 0 end in
          if fits bw (i'-rel d) then Ib Sz1 t (Raddr d)
          else inst
      | _ => inst
      end.
    Definition relax chunks :=
      let rel := makerel chunks in
      chunkmapi rel (relaxi rel) chunks.
  End Relaxation.
  Definition makechunks hook :=
    let c := hook (mapi rw_inst a.(code)) in
    Nat.iter a.(nrelax) relax (c).
  Definition compute_tables rel ai bti dsets :=
    maybe_map (λ D,
      let D' := map_single rel D in
      Hash.find_hash D D' <&> λ h,
      (h, Hash.compute_table_a h ai D D')
    ) dsets <&> λ l,
      let lens := map (λ x, len (snd x) << 1) l in
      combine l (list_of_array (csum bti lens)).
  Fixpoint retlist isns (i:int) l :=
    match isns with
    | nil => rev l
    | a::isns =>
        match decode a with
        | BR _ | BLR _ | RET _ => retlist isns (i+1) (i::l)
        | _ => retlist isns (i+1) l
        end
    end.
  Fixpoint deviations idx cum lens :=
    match lens with
    | nil => nil
    | size::t =>
        let dev := size - 1 in
        let next_cum_dev := cum + dev in
        if size =? 1 then deviations (idx+1) next_cum_dev t
        else idx::next_cum_dev::deviations (idx+1) next_cum_dev t
    end.
  Definition makedata hook :=
    let chunks := makechunks hook in
    let rel := makerel chunks in
    let ai := pad_to (rel (bi + len a.(code))) 10 in
    let bti := pad_to (ai + a.(rtlen)>>2) 10 in
    let rets := retlist a.(code) 0 [] in
    let devs := deviations 0 0 (map chunksize chunks) in
    tc ← compute_tables rel ai bti dsets;
    return {|
      arg := a; chunks := chunks; rel := rel;
      ai := ai; bti := bti; tc := tc;
      rets := rets; devs := devs;
    |}.
  Section PolHook.
    Fixpoint index{A} {eqd : EqDecision A} l x i :=
      match l with
      | nil => None
      | a::t => if eqd a x then Some i else index t x (succ i)
      end.
    Definition call_polhook (rets:list int) n i Rn :=
      [ Inum (Asm.PUSH2 Rn 30)
      ; Inum (Asm.PUSH2 0 1)
      ; Iimm Sz2 0 (index rets i 0 orelse 0)
      ; Ib Sz1 (BL 0) (Rrt 2)
      ; Inum (Asm.POP2 Rn (30 + (Rn =? 30)))
      ; Inum n ].
    Definition hook_indirect rets c :=
      match c.(ct) with
      | BR Rn | BLR Rn | RET Rn =>
          setd c (call_polhook rets c.(cn) c.(ci) Rn)
      | _ => c
      end.
    Definition polhook :=
      let rets := retlist a.(code) 0 [] in
      map (hook_indirect rets).
  End PolHook.
End ChunkGeneration.
Section InstSelection.
  Variable d : data.
  Notation ai := d.(ai).
  Notation tc := d.(tc).
  Notation rel := d.(rel).
  Definition mov2 r i' imm :=
    if fits 21 (asr imm 12-i'>>10) then
      Lst2 (Asm.ADRP i' imm r orelse Asm.UDF)
           (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
    else if imm >> 32 =? 0 then
      Lst2 (Asm.Encode.MOVZ 1 1 (imm >> 16) r)
           (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
    else Lst0.
  Definition hash_code h r :=
    match h with
    | Hash.H_UBFX lsb width => Lst2 Asm.NOP (Asm.UBFX true r r lsb width)
    | Hash.H_EOR_UBFX shift lsb width => Lst2 (Asm.EOR_lsr r r r shift) (Asm.UBFX true r r lsb width)
    end.
  Definition isel i' inst :=
    match inst with
    | Inum n => Lst1 n
    | Ihsh r lbl => hash_code (fst (fst (ith tc lbl orelse (Hash.H_UBFX 0 0, [0], 0)))) r
    | Iimm Sz1 r imm =>
        (Lst1 <$> Asm.ADRP i' imm r) orelse
        ((Lst1 <$> Asm.ADR i' imm r) orelse Lst0)
    | Itbl r lbl => mov2 r i' (4 * snd (ith tc lbl orelse (Hash.H_UBFX 0 0, [0], 0)))
    | Iimm Sz2 r imm => mov2 r i' imm
    | Iimm Sz3 r imm =>
        if i' >> 46 =? imm >> 48 then
          Lst3 (Asm.ADRP (i' land (0xffff_ffff>>2)) (imm land 0xffff_ffff) r orelse Asm.UDF)
               (Asm.Encode.MOVK 1 2 ((imm >> 32) land 0xffff) r)
               (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
        else if imm >> 48 =? 0 then
          Lst3 (Asm.Encode.MOVZ 1 2 ((imm >> 32) land 0xffff) r)
               (Asm.Encode.MOVK 1 1 ((imm >> 16) land 0xffff) r)
               (Asm.Encode.MOVK 1 0 (imm land 0xffff) r)
        else Lst0
    | Ib Sz1 (B _) (Raddr d) =>
        (Lst1 <$> Asm.B i' (rel d)) orelse (Lst1 Asm.UDF)
    | Ib Sz1 (BL _) (Raddr d) =>
        (Lst1 <$> Asm.BL i' (rel d)) orelse (Lst1 Asm.UDF)
    | Ib Sz1 (BL _) (Rrt n) =>
        (Lst1 <$> Asm.BL i' (ai+n)) orelse (Lst1 Asm.UDF)
    | Ib Sz1 (Bcond _ cond) (Raddr d) =>
        (Lst1 <$> Asm.Bcond i' (rel d) cond) orelse Lst0
    | Ib Sz1 (CBZ sf op _ Rt) (Raddr d) =>
        (Lst1 <$> Asm.CBZ sf op i' (rel d) Rt) orelse Lst0
    | Ib Sz1 (TBZ b5 op b40 _ Rt) (Raddr d) =>
        (Lst1 <$> Asm.TBZ b5 op b40 i' (rel d) Rt) orelse Lst0
    | Ib Sz2 (Bcond _ cond) (Raddr d) =>
        let inv := (Asm.Bcond i' (i'+2) (cond lxor 1)) orelse Asm.UDF in
        (Lst2 inv <$> Asm.B (i'+1) (rel d)) orelse Lst0
    | Ib Sz2 (CBZ sf op _ Rt) (Raddr d) =>
        let inv := (Asm.CBZ sf (b2i (is_zero op)) i' (i'+2) Rt) orelse Asm.UDF in
        (Lst2 inv <$> Asm.B (i'+1) (rel d)) orelse Lst0
    | Ib Sz2 (TBZ b5 op b40 _ Rt) (Raddr d) =>
        let inv := (Asm.TBZ b5 (b2i (is_zero op)) b40 i' (i'+2) Rt) orelse Asm.UDF in
        (Lst2 inv <$> Asm.B (i'+1) (rel d)) orelse Lst0
    | _ => Lst0
    end.
  Definition emit chunks :=
    maybe_map (λ c,
      fold_left (λ a s,
        match a, s with
        | Some l, Lst1 a => Some (a::l)
        | Some l, Lst2 a b => Some (b::a::l)
        | Some l, Lst3 a b c => Some (c::b::a::l)
        | _, _ => None
        end)
      (c.(cd)) (Some nil) <&> @rev int <&> setd c
    ) chunks.
  Definition rw :=
    emit (chunkmapi rel isel d.(chunks)).
End InstSelection.
