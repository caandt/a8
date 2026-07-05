Require Import Util PString Lia Strl Rewrite.
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

Definition parse_eident s :=
  let ei_mag := getu32 s 0 in
  let ei_class := getu8 s 4 in
  let ei_data := getu8 s 5 in
  let ei_version := getu8 s 6 in
  let ei_osabi := getu8 s 7 in
  let ei_abiversion := getu8 s 8 in
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
Definition parse_ehdr s :=
  e_ident ← parse_eident s;
  let e_type := getu16 s 16 in
  let e_machine := getu16 s 18 in
  let e_version := getu32 s 20 in
  e_entry ← getu64 s 24;
  e_phoff ← getu64 s 32;
  e_shoff ← getu64 s 40;
  let e_flags := getu32 s 48 in
  let e_ehsize := getu16 s 52 in
  let e_phentsize := getu16 s 54 in
  assert e_phentsize =? 56;
  let e_phnum := getu16 s 56 in
  let e_shentsize := getu16 s 58 in
  let e_shnum := getu16 s 60 in
  let e_shstrndx := getu16 s 62 in
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
Definition parse_phdr_at s i :=
  let p_type := getu32 s i in
  let p_flags := getu32 s (i+4) in
  p_offset ← getu64 s (i+8);
  p_vaddr ← getu64 s (i+16);
  p_paddr ← getu64 s (i+24);
  p_filesz ← getu64 s (i+32);
  p_memsz ← getu64 s (i+40);
  p_align ← getu64 s (i+48);
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
Definition phdr_offsets := range 56.
Definition to_words sl := map (getu32 sl) (range 4 0 (sllength sl >> 2)).
Definition of_chunks32 (lli: list (list int)) := map (λ x, of_list (List.concat (map_single u32 x))) lli.
Definition of_chunks64 (lli: list (list int)) := flat_map (λ x, (map (λ y, of_list (u64 y)) x)) lli.
Definition parse_phdr s ehdr :=
  let n := ehdr.(e_phnum) in
  assert negb (n =? 0xffff);
  maybe_map (parse_phdr_at s) (phdr_offsets ehdr.(e_phoff) n).
Definition parse_elf data :=
  ehdr ← parse_ehdr data;
  phdrs ← parse_phdr data ehdr;
  return {| ehdr := ehdr; phdrs := phdrs; data := data |}.

Fixpoint findn {A} (f:A -> bool) l n :=
  match l with | nil => None | a::t => if (f a) then Some n else findn f t (n+1) end.
Definition is_txt_seg p := (p.(p_type) =? PT_LOAD) && (bit p.(p_flags) 0).

Definition replaceable_seg phdrs :=
  match findn (λ x, x.(p_type) =? PT_NULL) phdrs 0 with
  | None => (findn (λ x, x.(p_type) =? PT_NOTE) phdrs 0)
  | Some n => Some n
  end.
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
               | _ => replace A with (0 + A) by lia
               end
           end;
    rewrite !(sub_equiv bin' bin 0 64); auto; lia.
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
               | _ => replace A with (0 + A) by lia
               end
           end;
    rewrite !(sub_equiv bin' bin 0 64); auto; lia.
Qed.

Theorem add_code_correct:
  forall bin bin' content addr
    (B: add_code bin content addr = Some bin'),
  match parse_elf bin' with
  | Some elf => Exists (λ s,
      s.(p_type) = PT_LOAD
      ∧ s.(p_flags) = PF_RX
      ∧ s.(p_vaddr) = addr
      ∧ slsub bin' s.(p_offset) s.(p_filesz) = content) elf.(phdrs)
  | None => False
  end.
Proof.
  intros.
  repeat so B.
  repeat so H0.
  unfold parse_elf.
  rewrite <-H0 in B. clear H0.
  rewrite (parse_elf_data H) in B. simpl in B.
  so H. so H.
  epose proof (ehdr_same H0 _). rewrite H2. simpl.
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
