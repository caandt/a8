From coqutil Require Import bitblast.
Require Import Util PString Lia Strl Rewrite ZArith.
From RecordUpdate Require Import RecordUpdate.

Notation getu8 := slget.
Definition getu16 s i := (getu8 s i) + (getu8 s (i+1)) << 8.
Definition getu32 s i := (getu16 s i) + (getu16 s (i+2)) << 16.
Definition getu64 s i :=
  assert negb (bit (getu8 s (i+7)) 7);
  return (getu32 s i) + (getu32 s (i+4)) << 32.
Definition u8 i := i land 0xff::nil.
Definition u16 i :=  u8 i ++  u8 (i >> 8).
Definition u32 i := u16 i ++ u16 (i >> 16).
Definition u64 i := u32 i ++ u32 (i >> 32).

Definition u8_equiv : forall {s s' i} (E: s ≡ s'), getu8 s i = getu8 s' i := equiv_get.
Definition u16_equiv : forall {s s' i} (E: s ≡ s'), getu16 s i = getu16 s' i.
Proof. intros. unfold getu16. now rewrite !(u8_equiv E). Qed.
Definition u32_equiv : forall {s s' i} (E: s ≡ s'), getu32 s i = getu32 s' i.
Proof. intros. unfold getu32. now rewrite !(u16_equiv E). Qed.
Definition u64_equiv : forall {s s' i} (E: s ≡ s'), getu64 s i = getu64 s' i.
Proof. intros. unfold getu64. now rewrite (u8_equiv E), !(u32_equiv E). Qed.
Definition u8_before : forall s i j (J: i <? j = true), getu8 s i = getu8 (slsub s 0 j) i := get_before.
Definition u16_before : forall s i j (I: (to_Z i < wB - 1)%Z) (J: i + 1 <? j = true), getu16 s i = getu16 (slsub s 0 j) i.
Proof. intros. unfold getu16. now rewrite (u8_before s i j), (u8_before s (i+1) j) by lia. Qed.
Definition u32_before : forall s i j (I: (to_Z i < wB - 3)%Z) (J: i + 3 <? j = true), getu32 s i = getu32 (slsub s 0 j) i.
Proof. intros. unfold getu32. now rewrite (u16_before s i j), (u16_before s (i+2) j) by lia. Qed.
Definition u64_before : forall s i j (I: (to_Z i < wB - 7)%Z) (J: i + 7 <? j = true), getu64 s i = getu64 (slsub s 0 j) i.
Proof. intros. unfold getu64. now rewrite (u32_before s i j), (u32_before s (i+4) j), (u8_before s (i+7) j) by lia. Qed.

Definition ELFMAG := 0x464c457f.
Definition ELFCLASS64 := 2.
Definition EV_CURRENT := 1.
Definition PT_NULL := 0.
Definition PT_LOAD := 1.
Definition PT_NOTE := 4.
Definition PF_RX := 5.

Record Eident := {
  ei_mag: int;
  ei_class: int;
  ei_data: int;
  ei_version: int;
  ei_osabi: int;
  ei_abiversion: int;
}.
Record Ehdr := {
  e_ident: Eident;
  e_type: int;
  e_machine: int;
  e_version: int;
  e_entry: int;
  e_phoff: int;
  e_shoff: int;
  e_flags: int;
  e_ehsize: int;
  e_phentsize: int;
  e_phnum: int;
  e_shentsize: int;
  e_shnum: int;
  e_shstrndx: int;
}.
Record Phdr := {
  p_type: int;
  p_flags: int;
  p_offset: int;
  p_vaddr: int;
  p_paddr: int;
  p_filesz: int;
  p_memsz: int;
  p_align: int;
}.
Record ELF := {
  ehdr: Ehdr;
  phdrs: list Phdr;
  data: list string;
}.

Definition parse_eident bin :=
  let ei_mag := getu32 bin 0 in
  let ei_class := getu8 bin 4 in
  let ei_data := getu8 bin 5 in
  let ei_version := getu8 bin 6 in
  let ei_osabi := getu8 bin 7 in
  let ei_abiversion := getu8 bin 8 in
  assert ei_mag =? ELFMAG;
  assert ei_class =? ELFCLASS64;
  assert ei_version =? EV_CURRENT;
  return {|
    ei_mag := ei_mag;
    ei_class := ei_class;
    ei_data := ei_data;
    ei_version := ei_version;
    ei_osabi := ei_osabi;
    ei_abiversion := ei_abiversion;
  |}.
Definition parse_ehdr bin :=
  e_ident ← parse_eident bin;
  let e_type := getu16 bin 16 in
  let e_machine := getu16 bin 18 in
  let e_version := getu32 bin 20 in
  e_entry ← getu64 bin 24;
  e_phoff ← getu64 bin 32;
  assert 64 <=? e_phoff;
  e_shoff ← getu64 bin 40;
  let e_flags := getu32 bin 48 in
  let e_ehsize := getu16 bin 52 in
  let e_phentsize := getu16 bin 54 in
  assert e_phentsize =? 56;
  let e_phnum := getu16 bin 56 in
  assert e_phoff <? e_phoff + 56 * e_phnum;
  let e_shentsize := getu16 bin 58 in
  let e_shnum := getu16 bin 60 in
  let e_shstrndx := getu16 bin 62 in
  return {|
    e_ident := e_ident;
    e_type := e_type;
    e_machine := e_machine;
    e_version := e_version;
    e_entry := e_entry;
    e_phoff := e_phoff;
    e_shoff := e_shoff;
    e_flags := e_flags;
    e_ehsize := e_ehsize;
    e_phentsize := e_phentsize;
    e_phnum := e_phnum;
    e_shentsize := e_shentsize;
    e_shnum := e_shnum;
    e_shstrndx := e_shstrndx;
  |}.
Definition parse_phdr_at bin i :=
  let p_type := getu32 bin i in
  let p_flags := getu32 bin (i+4) in
  p_offset ← getu64 bin (i+8);
  p_vaddr ← getu64 bin (i+16);
  p_paddr ← getu64 bin (i+24);
  p_filesz ← getu64 bin (i+32);
  p_memsz ← getu64 bin (i+40);
  p_align ← getu64 bin (i+48);
  return {|
    p_type := p_type;
    p_flags := p_flags;
    p_offset := p_offset;
    p_vaddr := p_vaddr;
    p_paddr := p_paddr;
    p_filesz := p_filesz;
    p_memsz := p_memsz;
    p_align := p_align;
  |}.
Function range step i n {measure to_nat n} :=
  if (n =? 0) then nil else i::range step (i+step) (n-1).
Proof. lia. Defined.
Lemma range_len:
  forall step i n, List.length (range step i n) = to_nat n.
Proof.
  intros. apply range_ind; intros. simpl. lia. simpl. rewrite H. lia.
Qed.
Definition phdr_offsets := range 56.
Definition to_words sl := map (getu32 sl) (range 4 0 (sllength sl >> 2)).
Definition of_chunks32 (lli: list (list int)) := map (λ x, of_list (List.concat (map_single u32 x))) lli.
Definition of_chunks64 (lli: list (list int)) := flat_map (λ x, (map (λ y, of_list (u64 y)) x)) lli.
Definition parse_phdr bin ehdr :=
  let n := ehdr.(e_phnum) in
  assert negb (n =? 0xffff);
  maybe_map (parse_phdr_at bin) (phdr_offsets ehdr.(e_phoff) n).
Definition parse_elf data :=
  assert 64 <? sllength data;
  ehdr ← parse_ehdr data;
  phdrs ← parse_phdr data ehdr;
  return {| ehdr := ehdr; phdrs := phdrs; data := data |}.

Fixpoint findn {A} (f:A -> bool) l n :=
  match l with | nil => None | a::t => if (f a) then Some n else findn f t (n+1) end.
Lemma findn_bound:
  forall A f l n m, findn f l m = Some n -> to_nat n < to_nat m + @List.length A l.
Proof.
  induction l; simpl; intros.
    easy.
    destruct f.
      injection H. lia.
      apply IHl in H. lia.
Qed.
Definition is_txt_seg p := (p.(p_type) =? PT_LOAD) && (bit p.(p_flags) 0).

Definition replaceable_seg phdrs :=
  match findn (λ x, x.(p_type) =? PT_NULL) phdrs 0 with
  | None => (findn (λ x, x.(p_type) =? PT_NOTE) phdrs 0)
  | Some n => Some n
  end.
Lemma replaceable_seg_bound:
  forall phdrs n, replaceable_seg phdrs = Some n -> to_nat n < List.length phdrs.
Proof.
  intros. unfold replaceable_seg in H. destruct findn eqn:E.
    apply findn_bound in E. injection H. lia.
    now apply findn_bound in H.
Qed.
Definition txt_seg elf := find is_txt_seg elf.(phdrs).
Definition load_seg offset vaddr content :=
  Build_Phdr PT_LOAD PF_RX offset vaddr vaddr (sllength content) (sllength content) 0x1000.
Definition phdr_data p :=
  map of_list (
    u32 p.(p_type)::
    u32 p.(p_flags)::
    u64 p.(p_offset)::
    u64 p.(p_vaddr)::
    u64 p.(p_paddr)::
    u64 p.(p_filesz)::
    u64 p.(p_memsz)::
    u64 p.(p_align)::nil
  ).
Lemma landland:
  forall a b, a land b land b = a land b.
Proof. zify. apply Z.bits_inj. intro. rewrite !Z.land_spec. lia. Qed.
Lemma phdr_data_len:
  forall p, List.length (LO (phdr_data p)) = 56%nat.
Proof.
  intros. unfold list_of_strl, phdr_data. 
  cbv [map]. rewrite !to_of_list.
  all: easy || unfold u64, u32, u16, u8, char63_valid; repeat constructor.
  all: now rewrite landland.
Qed.
Lemma addl: forall i j, i <? i + j = true -> (to_Z i + to_Z j < wB)%Z.
Proof. lia. Qed.
Definition listreplace {A} l n (x:A) := firstn n l++x::skipn (S n) l.
Definition replace_phdr elf phdr i :=
  let phdr_offset := elf.(ehdr).(e_phoff) + 56 * i in
  elf <| phdrs ::= λ p, listreplace p (to_nat i) phdr |>
      <| data ::= λ d, slsplice d phdr_offset (phdr_data phdr) |>.
Definition map_phdrs (f: Phdr -> option Phdr) elf :=
  let g '(e,i) p := match f p with None => (e,i+1) | Some p => (replace_phdr e p i, i+1) end in
  fst (fold_left g elf.(phdrs) (elf, 0)).
Definition with_load_seg elf content vaddr :=
  idx ← replaceable_seg elf.(phdrs);
  assert elf.(ehdr).(e_phoff) + 56 * idx <? sllength elf.(data);
  let padding := (0x1000 - sllength elf.(data) land 0xfff) land 0xfff in
  let offset := sllength elf.(data) + padding in
  let elf := replace_phdr elf (load_seg offset vaddr content) idx in
  return elf <| data ::= λ d, slcat d (make padding 0::content) |>.
Definition set_nx := map_phdrs (λ p,
  assert is_txt_seg p;
  return p <| p_flags ::= Uint63.pred |>
).
Definition set_entrypoint elf entry :=
  elf <| ehdr; e_entry := entry |>
      <| data ::= λ d, slsplice d 24 (of_list (u64 entry)::nil) |>.
Definition get_page_after elf :=
  let f p := p.(p_vaddr) + p.(p_memsz) in
  let m := fold_left Uint63.max (map f elf.(phdrs)) 0 in
  ((m >> 12) + 2) << 10.
Definition phdr_content elf phdr :=
  slsub elf.(data) phdr.(p_offset) phdr.(p_filesz).
Definition add_code bin code addr :=
  elf ← parse_elf bin;
  assert (64 <? elf.(ehdr).(e_phoff));
  with_load_seg elf code addr <&> data.

Ltac unfold_first x H :=
  match x with
  | ?a _ => unfold_first a H
  | _ => unfold x in H; simpl in H
  end.
Ltac so H :=
  match type of H with
  | (assert _; _) = Some _ =>
      let A := fresh "A" in
      let B := fresh "B" in
      apply bind_Some in H as (A&B&H);
      destruct (_:bool) eqn:? in B; try easy; clear A B
  | _ ≫= _ = Some _ => apply bind_Some in H as (?&?&H)
  | _ <&> _ = Some _ => apply fmap_Some in H as (?&?&H)
  | (return _) = Some _ => injection H as H
  | Some _ = Some _ => injection H as H
  | (?a = Some _) => unfold_first a H
  end.
Ltac sog :=
  match goal with
  | |- (assert ?E; _) = Some _ => replace E with true; simpl
  | |- (return _) = Some _ => f_equal
  | |- (?E <&> _) = Some _ =>
      let H := fresh "H" in eenough (E = Some _) as H; rewrite ?H; simpl
  | |- (?E ≫= _) = Some _ =>
      let H := fresh "H" in eenough (E = Some _) as H; rewrite ?H; simpl
  end.
Lemma parse_elf_data:
  forall {bin elf} (E: parse_elf bin = Some elf),
    data elf = bin.
Proof.
  intros. repeat so E. now subst.
Qed.
Lemma add_0_int: forall i, i = 0 + i. Proof. lia. Qed.
Lemma eident_same {bin eident bin'}
  (E: parse_eident bin = Some eident)
  (S: slsub bin 0 64 ≡ slsub bin' 0 64):
  parse_eident bin' = Some eident.
Proof.
  unfold parse_eident in *.
  repeat so E. repeat sog; subst;
  f_equal; unfold getu32, getu16; simpl;
    repeat match goal with
           | |- context [getu8 _ ?A] =>
               lazymatch A with
               | 0 + _ => fail
               | _ => rewrite (add_0_int A)
               end
           end;
    rewrite !(sub_equiv_get bin' bin 0 64); auto; lia.
Qed.
Lemma ehdr_same {bin ehdr bin'}
  (E: parse_ehdr bin = Some ehdr)
  (S: slsub bin 0 64 ≡ slsub bin' 0 64):
  parse_ehdr bin' = Some ehdr.
Proof.
  unfold parse_ehdr in *.
  repeat so E. rewrite <-E. rewrite (eident_same H S). repeat sog;
  f_equal; unfold getu64, getu32, getu16; simpl;
    repeat match goal with
           | |- context [getu8 _ ?A] =>
               lazymatch A with
               | 0 + _ => fail
               | _ => rewrite (add_0_int A)
               end
           end;
    try (rewrite !(sub_equiv_get bin' bin 0 64); auto); lia.
Qed.
Lemma maybe_map_len:
  forall A B (f: A -> option B) l l', maybe_map f l = Some l' -> List.length l' = List.length l.
Proof.
  intros. unfold maybe_map, mapfold in H.
  generalize l l' H. clear. induction l; intros. now inversion H.
  repeat so H. apply IHl in H1. subst. simpl. lia.
Qed.

Lemma phdr_len:
  forall s ehdr p, parse_phdr s ehdr = Some p -> List.length p = to_nat ehdr.(e_phnum).
Proof.
  intros. do 2 so H. apply maybe_map_len in H. unfold phdr_offsets in H. now rewrite range_len in H.
Qed.
Variant IsPhoff (data: list string) : int -> Prop :=
  | isphoff i (I: getu64 data 32 = Some i) : IsPhoff data i.
Variant IsPhnum (data: list string) : int -> Prop :=
  | isphnum i (I: getu16 data 56 = i) : IsPhnum data i.
Variant IsPhdr (data: list string) : list string -> Prop :=
  | isphdr phoff phnum i p
      (O: IsPhoff data phoff)
      (N: IsPhnum data phnum)
      (I: i <? phnum = true)
      (P: slsub data (phoff + 56 * i) 56 ≡ p) : IsPhdr data p.
Variant IsLoad (seg: list string) : Prop :=
  | isload (S: getu32 seg 0 = PT_LOAD).
Variant IsRX (seg: list string) : Prop :=
  | isrx (S: getu32 seg 4 = PF_RX).
Variant HasOffset (seg: list string) : int -> Prop :=
  | hasoffset offset (S: getu64 seg 8 = Some offset) : HasOffset seg offset.
Variant IsAt (seg: list string) : int -> Prop :=
  | isat vaddr (S: getu64 seg 16 = Some vaddr) : IsAt seg vaddr.
Variant HasSize (seg: list string) : int -> Prop :=
  | haslength filesz (S: getu64 seg 32 = Some filesz) : HasSize seg filesz.
Variant HasContent (data: list string) (seg: list string) : list string -> Prop :=
  | hascontent content offset vaddr filesz
      (S: IsPhdr data seg)
      (O: HasOffset seg offset)
      (V: IsAt seg vaddr)
      (F: HasSize seg filesz)
      (C: slsub data offset filesz ≡ content) : HasContent data seg content.
Lemma getu8_bound:
  forall sl i, getu8 sl i <? 256 = true.
Proof.
  induction sl. easy. intros. simpl. destruct (ltb i). pose proof (get_char63_valid a i).
  unfold char63_valid in H. zify. change 255%Z with (Z.ones 8) in H. rewrite Z.land_ones in H. lia. lia.
  easy.
Qed.
Lemma getu16_bound:
  forall sl i, getu16 sl i <? 0x10000 = true.
Proof.
  unfold getu16. intros. pose (getu8_bound sl i). pose (getu8_bound sl (i+1)). lia.
Qed.
Require I2N.
Import I2N.notations.
Require Import FunctionalExtensionality.
Lemma getu64_sub:
  forall sl i, (to_Z i + 8 <= wB)%Z -> getu64 sl i = getu64 (slsub sl i 8) 0.
Proof.
  intros. unfold getu64, getu32, getu16.
  rewrite <-!add_assoc. simpl.
  repeat match goal with |- context [getu8 sl (i + ?k)] => rewrite (get_sub sl (i + k) 8 (i)) end.
  rewrite (get_sub sl i 8 i).
  all: try lia.
  remember (negb _). remember (negb _) in |-*. replace b0 with b. destruct b. simpl. 
  repeat f_equal; lia. easy. subst. repeat f_equal. lia.
Qed.
Lemma getu64_equiv:
  forall sl sl2 i, sl ≡ sl2 -> getu64 sl i = getu64 sl2 i.
Proof.
  intros. unfold getu64, getu32, getu16. now rewrite !(equiv_get _ _ _ H).
Qed.
Lemma makeu8:
  forall a, of_list (u8 a) = make 1 a.
Proof.
  intros. simpl. apply to_list_inj. now rewrite cat_spec, !make_spec, landland.
Qed.
Lemma getu8_u8:
  forall a, getu8 [of_list (u8 a)] 0 = a land 255.
Proof.
  intros. cbv.
  now rewrite get_spec, length_spec_int, !cat_spec, make_spec, landland. 
Qed.
(* Infix ">>" := N.shiftr. *)
(* Infix "<<" := N.shiftl. *)
(* Infix ".&" := N.land (at level 30). *)
From coqutil Require Import prove_Zeq_bitwise.
(* Lemma getu16_u16: *)
(*   forall a, getu16 [of_list (u16 a)] 0 = a land 0xffff. *)
(* Proof. *)
(*   intros. unfold getu16, u16. rewrite of_list_app, !makeu8. *)
(*   rewrite !list_get. simpl. cbv[list_of_strl map concat]. *)
(*   rewrite cat_spec_valid_length, !make_spec, app_nil_r by (rewrite !make_length_spec; lia). simpl. *)
(*   I2N.zify. *)
(*   unfold wB. *)
(*   rewrite <-!Z.land_ones by lia. *)
(*   rewrite <-!Z.or_to_plus. *)
(*   prove_Zeq_bitwise. *)
(*   prove_Zeq_bitwise. *)
(* Qed. *)
Lemma byte: forall i mask s, ((i >> s) land mask) << s = i land (mask << s).
Proof.
  intros. I2N.zify.
  unfold wB. rewrite <-!Z.land_ones by lia.
  prove_Zeq_bitwise. repeat f_equal. lia.
Qed.
Lemma lsl_add: forall a b s, (a + b) << s = a << s + b << s.
Proof.
  intros. I2N.zify. rewrite !Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma lsr_lsr: forall a b c, (to_Z b + to_Z c < wB)%Z -> a >> b >> c = a >> (b + c).
Proof.
  intros. I2N.zify. unfold wB. rewrite Z.mod_small by lia.
  prove_Zeq_bitwise.
Qed.
Lemma add_lor: forall a b, a land b = 0 -> a + b = a lor b.
Proof.
  intros. I2N.zify. apply eq_int_inj in H. rewrite I2N.I2Z.inj_land in H.
  rewrite <-Z.or_to_plus by lia. unfold wB. rewrite <-Z.land_ones by lia.
  rewrite Z.land_lor_distr_l. f_equal; rewrite Z.land_ones; lia.
Qed.
Lemma land2: forall a b c, (a land b) land (a land c) = a land (b land c).
Proof. intros. now rewrite !landA, (landC a b), landland. Qed.
Lemma lan: forall a b c d, (a land b) land (c land d) = (a land c) land (b land d).
Proof. intros. I2N.zify. prove_Zeq_bitwise. Qed.
Lemma getu64_u64: 
  forall a, getu64 [of_list (u64 a)] 0 = Some a.
Proof.
  intros. unfold getu64, getu32, getu16, getu8.
  remember (length _). simpl in Heqi.
  rewrite length_spec_int in Heqi.
  rewrite !cat_spec, !make_spec in Heqi. simpl in Heqi. cbv in Heqi.
  subst i. cbv[ add ltb].
  simpl.
  rewrite !get_spec, !cat_spec, !nth_firstn, !make_spec.
  repeat replace (_ <? _)%nat with true by lia.
  repeat match goal with |- context[Nat.min ?a _] => replace (Nat.min a _) with a by lia end.
  simpl. rewrite !landland. sog. sog. shelve.
  rewrite land_spec, andb_true_r, !bit_lsr. simpl. rewrite bit_M by lia. lia. Unshelve.
  rewrite !byte. rewrite !lsl_add, !byte.
  rewrite !add_assoc. 
  rewrite (add_lor (a land 255)) by now rewrite land2, land0_r.
  rewrite (add_lor (_ lor _)). 
  rewrite (add_lor (_ lor _)). 
  rewrite (add_lor (_ lor _)). 
  rewrite (add_lor (_ lor _)). 
  rewrite (add_lor (_ lor _)). 
  rewrite (add_lor (_ lor _)). 
  I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia. 
  change (to_Z 0) with Z0. 
 replace (to_Z a) with (Z.land (to_Z a) (Z.ones 63)) by (rewrite Z.land_ones; lia).
  (* prove_Zeq_bitwise. *)
  (* I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia.  *)
  (* change (to_Z 0) with Z0. prove_Zeq_bitwise. *)
  (* I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia.  *)
  (* change (to_Z 0) with Z0. prove_Zeq_bitwise. *)
  (* I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia.  *)
  (* change (to_Z 0) with Z0. prove_Zeq_bitwise. *)
  (* I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia.  *)
  (* change (to_Z 0) with Z0. prove_Zeq_bitwise. *)
  (* I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia.  *)
  (* change (to_Z 0) with Z0. prove_Zeq_bitwise. *)
  (* I2N.zify. unfold wB. rewrite <-!Z.land_ones by lia.  *)
  (* change (to_Z 0) with Z0. prove_Zeq_bitwise. *)
Admitted.
Theorem add_code_correct:
  forall bin bin' content addr
    (B: add_code bin content addr = Some bin'),
  exists seg,
    IsPhdr bin' seg /\
    IsLoad seg /\
    IsRX seg /\
    IsAt seg addr /\
    HasContent bin' seg content.
Proof.
  intros. repeat so B. repeat so H0.
  remember (phdr_data _). exists l.
  repeat so H. repeat so H2.

  assert (IsPhdr bin' l).
  { subst x0 x. simpl in B.
    apply replaceable_seg_bound in H1. simpl in H1. apply phdr_len in H3.
    assert (slsub bin' 0 64 ≡ slsub bin 0 64).
    { subst x2. simpl in *. 
      pose proof (getu16_bound bin 56).
      subst bin'. rewrite sub_cat1. erewrite splice_before. easy. easy. rewrite <-H. lia.
      simpl. rewrite Zlength_correct, list_splice, length_app, length_firstn.
      rewrite list_length in Heqb0. lia. }
    econstructor.
    + apply (isphoff _ x2.(e_phoff)).
      erewrite (u64_before _ _ 64), u64_equiv, <-(u64_before _ _ 64), H6; lia || auto. now subst.
    + apply (isphnum _ x2.(e_phnum)). 
      erewrite (u16_before _ _ 64), u16_equiv, <-(u16_before _ _ 64); try lia. now subst. easy.
    + assert (x1 <? e_phnum x2 = true). rewrite H3 in H1. lia. apply H0.
    + rewrite B. rewrite sub_cat1, sub_splice. easy.
      easy. subst l. rewrite Zlength_correct, phdr_data_len. easy.
      rewrite Zlength_correct, list_splice, !length_app, length_firstn.
      rewrite list_length in Heqb0. simpl in *. 
      replace (Nat.min _ _) with (to_nat (e_phoff x2 + 56 * x1)) by lia.
      subst l.
      rewrite phdr_data_len. lia. }
  assert (getu64 l 16 = Some addr).
  { rewrite getu64_sub. rewrite (getu64_equiv _ (of_list (u64 addr)::nil)).
    apply getu64_u64.
    subst l.
    rewrite list_sub. unfold list_of_strl, phdr_data.
    cbv[map]. rewrite !to_of_list.
  all: easy || unfold u64, u32, u16, u8, char63_valid; repeat constructor.
  all: now rewrite landland.
  }
  repeat split.
  - easy.
  - subst. easy.
  - subst. easy.
  - easy. 
  - eapply (hascontent _ _ _ _ addr (sllength content)). easy.
    econstructor. rewrite getu64_sub by lia. erewrite (getu64_equiv _ (of_list (u64 _)::nil)).
    apply getu64_u64. subst l.

    rewrite list_sub. unfold list_of_strl, phdr_data.
    cbv[map]. rewrite !to_of_list.
  all: easy || unfold u64, u32, u16, u8, char63_valid; repeat constructor.
  all: try now rewrite landland.
     rewrite getu64_sub by lia. rewrite (getu64_equiv _ (of_list (u64 (sllength content))::nil)).
    apply getu64_u64.
    subst l.
    rewrite list_sub. unfold list_of_strl, phdr_data.
    cbv[map]. rewrite !to_of_list.
  all: easy || unfold u64, u32, u16, u8, char63_valid; repeat constructor.
  all: try now rewrite landland.
    subst bin' x0. simpl.
    erewrite equiv_sub; [|erewrite cat_splice; try reflexivity]. admit.
    (* lia. *)
    (* rewrite sub_cat2. *)
    (* admit. rewrite Zlength_correct. rewrite list_splice, !length_app, length_firstn, length_skipn. *)
    (* rewrite cat_splice. rewrite  *)
Admitted.

Definition rw_elf bin pol dsets abort :=
  elf ← parse_elf bin;
  ts ← txt_seg elf;
  let code := phdr_content elf ts in
  let bi := ts.(p_vaddr) >> 2 in
  let bi' := get_page_after elf in
  d ← global_data (to_words code) bi bi' pol dsets (sllength abort >> 2);
  code' ← null_rw d;
  let content := of_chunks32 code' ++ abort ++ of_chunks64 (map (λ '(_,x,_),x) d.(tc)) in
  let elf := set_nx elf in
  let elf := set_entrypoint elf (d.(rel) (elf.(ehdr).(e_entry) >> 2) << 2) in
  with_load_seg elf content (bi'<<2) <&> data.
