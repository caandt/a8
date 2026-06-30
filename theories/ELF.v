Require Import Util PString Lia.
Definition getu16 s i := (get s i) + (get s (i+1)) << 8.
Definition getu32 s i := (getu16 s i) + (getu16 s (i+2)) << 16.
Definition getu64 s i := if Uint63.bit (get s (i+7)) 7 then None else Some ((getu32 s i) + (getu32 s (i+4)) << 32).
Definition u8 i := i land 0xff::nil.
Definition u16 i :=  u8 i ++  u8 (i >> 8).
Definition u32 i := u16 i ++ u16 (i >> 16).
Definition u64 i := u32 i ++ u32 (i >> 32).

Definition ELFMAG := 0x464c457f.
Definition ELFCLASS64 := 2.
Definition EV_CURRENT := 1.

Structure Eident := {
  ei_mag: int;
  ei_class: int;
  ei_data: int;
  ei_version: int;
  ei_osabi: int;
  ei_abiversion: int;
}.
Structure Ehdr := {
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
Structure Phdr := {
  p_type: int;
  p_flags: int;
  p_offset: int;
  p_vaddr: int;
  p_paddr: int;
  p_filesz: int;
  p_memsz: int;
  p_align: int;
}.
Definition parse_eident s :=
  let ei_mag := getu32 s 0 in
  let ei_class := get s 4 in
  let ei_data := get s 5 in
  let ei_version := get s 6 in
  let ei_osabi := get s 7 in
  let ei_abiversion := get s 8 in
  if (ei_mag =? ELFMAG) && (ei_class =? ELFCLASS64) && (ei_version =? EV_CURRENT) then Some {|
    ei_mag := ei_mag;
    ei_class := ei_class;
    ei_data := ei_data;
    ei_version := ei_version;
    ei_osabi := ei_osabi;
    ei_abiversion := ei_abiversion; |}
  else None.
Definition parse_ehdr s :=
  parse_eident s >>= \e_ident,
  let e_type := getu16 s 16 in
  let e_machine := getu16 s 18 in
  let e_version := getu32 s 20 in
  getu64 s 24 >>= \e_entry,
  getu64 s 32 >>= \e_phoff,
  getu64 s 40 >>= \e_shoff,
  let e_flags := getu32 s 48 in
  let e_ehsize := getu16 s 52 in
  let e_phentsize := getu16 s 54 in
  let e_phnum := getu16 s 56 in
  let e_shentsize := getu16 s 58 in
  let e_shnum := getu16 s 60 in
  let e_shstrndx := getu16 s 62 in Some {|
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
  getu64 s (i+8) >>= \p_offset,
  getu64 s (i+16) >>= \p_vaddr,
  getu64 s (i+24) >>= \p_paddr,
  getu64 s (i+32) >>= \p_filesz,
  getu64 s (i+40) >>= \p_memsz,
  getu64 s (i+48) >>= \p_align, Some {|
    p_type := p_type;
    p_flags := p_flags;
    p_offset := p_offset;
    p_vaddr := p_vaddr;
    p_paddr := p_paddr;
    p_filesz := p_filesz;
    p_memsz := p_memsz;
    p_align := p_align;
  |}.
Function phdr_offsets i n {measure to_nat n} :=
  if (n =? 0) then nil else i::phdr_offsets (i+56) (n-1).
Proof. lia. Defined.
Definition parse_phdr s ehdr :=
  let n := ehdr.(e_phnum) in
  if (n =? 0xffff) then None else
  maybe_map (parse_phdr_at s) (phdr_offsets ehdr.(e_phoff) n).
Definition PT_NULL := 0.
Definition PT_LOAD := 1.
Definition PT_NOTE := 4.
Definition PFLAG_RX := 5.
Fixpoint findn {A} (f:A -> bool) l n :=
  match l with | nil => None | a::t => if (f a) then Some n else findn f t (n+1) end.
Definition replaceable_seg phdrs :=
  match findn (\x, x.(p_type) =? PT_NULL) phdrs 0 with
  | None => (findn (\x, x.(p_type) =? PT_NOTE) phdrs 0)
  | Some n => Some n
  end.
Definition load_seg offset vaddr content :=
  of_list (
    u32 PT_LOAD ++
    u32 PFLAG_RX ++
    u64 offset ++
    u64 vaddr ++
    u64 vaddr ++
    u64 (length content) ++
    u64 (length content) ++
    u64 0x1000
  ).
Definition replace_segment elf content vaddr :=
  parse_ehdr elf >>= \ehdr,
  parse_phdr elf ehdr >>= \phdrs,
  replaceable_seg phdrs >>=s \n,
  let phdr_off := ehdr.(e_phoff) + 56 * n in
  let padding := (0x1000 - length elf land 0xfff) land 0xfff in
  let offset := length elf + padding in
  let elf' := sub elf 0 phdr_off in
  let elf' := cat elf' (load_seg offset vaddr content) in
  let elf' := cat elf' (sub elf (phdr_off+56) (length elf)) in
  let elf' := cat elf' (make padding 0) in
  let elf' := cat elf' content in
  elf'.
Definition set_entrypoint elf entry :=
  let elf' := sub elf 0 24 in
  let elf' := cat elf' (of_list (u64 entry)) in
  let elf' := cat elf' (sub elf 32 (length elf)) in
  elf'.
