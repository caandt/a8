Require Import Util.
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
End Encode.
Definition bounded x bound :=
  match -bound ?= x, x ?= bound with
  | Gt, Lt => Some x
  | _, _ => None
  end.
Definition Bcond src dst cond :=
  match bounded (dst - src) (1<<18) with
  | Some imm19 => Some (Encode.Bcond imm19 cond)
  | None => None
  end.
Definition B src dst :=
  match bounded (dst - src) (1<<25) with
  | Some imm26 => Some (Encode.B imm26)
  | None => None
  end.
Definition BL src dst :=
  match bounded (dst - src) (1<<25) with
  | Some imm26 => Some (Encode.BL imm26)
  | None => None
  end.
Definition ADR imm Rd :=
  Encode.ADR (imm[0,2]) (imm[2,21]) Rd.
Definition ADRP imm Rd :=
  Encode.ADRP (imm[0,2]) (imm[2,21]) Rd.
Function b16s imm hw {measure (fun x => to_nat (4 - x)) hw} :=
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
      ::map (fun '(imm, sf) => Encode.MOVK 1 sf imm Rd) t
  end.

