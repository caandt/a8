Require Import Util Sint63.
Require Import Lia ZifyUint63.

Module Encode.
  Definition Bcond imm19 cond :=
    (84 << 24) lor (imm19 << 5) lor (cond).
  Definition B imm26 :=
    (5 << 26) lor (imm26).
  Definition BL imm26 :=
    (1 << 31) lor (5 << 26) lor (imm26).
  Definition ADR immlo immhi Rd :=
    (immlo << 29) lor (16 << 24) lor (immhi << 5) lor (Rd).
  Definition ADRP immlo immhi Rd :=
    (1 << 31) lor (immlo << 29) lor (16 << 24) lor (immhi << 5) lor (Rd).
  Definition MOVK sf hw imm16 Rd :=
    (sf << 31) lor (0xe5 << 23) lor (hw << 21) lor (imm16 << 5) lor (Rd).
  Definition MOVZ sf hw imm16 Rd :=
    (sf << 31) lor (0xa5 << 23) lor (hw << 21) lor (imm16 << 5) lor (Rd).
  Definition CBZ sf op imm19 Rt :=
    (sf << 31) lor (0x34 << 24) lor (op << 24) lor (imm19 << 5) lor (Rt).
  Definition TBZ b5 op b40 imm14 Rt :=
    (b5 << 31) lor (0x36 << 24) lor (op << 24) lor (b40 << 19) lor (imm14 << 5) lor (Rt).
  Definition UBFX sf N immr imms Rn Rd :=
    (sf << 31) lor (0xa6 << 23) lor (N << 22) lor (immr << 16) lor (imms << 10) lor (Rn << 5) lor (Rd).
  Definition LDR_r size Rm option S Rn Rt :=
    (size << 30) lor (0x1c3 << 21) lor (Rm << 16) lor (option << 13) lor (S << 12) lor (2 << 10) lor (Rn << 5) lor (Rt).
End Encode.
Definition bounded x bw :=
  let bound := 1<<(bw-1) in
  if ((-bound <=? x) && (x <? bound))%sint63
  then Some (x land (1<<bw-1))
  else None.
Definition Bcond src dst cond :=
  bounded (dst - src) 19 >>=s \imm19, Encode.Bcond imm19 cond.
Definition B src dst :=
  bounded (dst - src) 26 >>=s \imm26, Encode.B imm26.
Definition BL src dst :=
  bounded (dst - src) 26 >>=s \imm26, Encode.BL imm26.
Definition CBZ sf op src dst Rt :=
  bounded (dst - src) 19 >>=s \imm19, Encode.CBZ sf op imm19 Rt.
Definition TBZ b5 op b40 src dst Rt :=
  bounded (dst - src) 14 >>=s \imm14, Encode.TBZ b5 op b40 imm14 Rt.
Definition ADR imm Rd :=
  Encode.ADR (imm[0,2]) (imm[2,21]) Rd.
Definition ADRP imm Rd :=
  Encode.ADRP (imm[0,2]) (imm[2,21]) Rd.
Function b16s imm hw {measure (\x, to_nat (4 - x)) hw} :=
  if (hw <? 4)
  then let rest := b16s (imm >> 16) (succ hw) in
       if (imm land 0xffff =? 0)
       then rest
       else (imm land 0xffff, hw)::rest
  else nil.
Proof. all: lia. Defined.
Definition MOV imm Rd :=
  match b16s imm 0 with
  | nil => Encode.MOVZ 1 0 0 Rd::nil
  | (imm, sf)::t =>
      Encode.MOVZ 1 sf imm Rd
      ::map (\(imm, sf), Encode.MOVK 1 sf imm Rd) t
  end.
Definition UBFX is64 Rd Rn lsb width :=
  Encode.UBFX (b2i is64) (b2i is64) lsb (lsb+width-1) Rn Rd.
Definition LDR_r64 Rt Rn Rm :=
  Encode.LDR_r 3 Rm 3 1 Rn Rt.
