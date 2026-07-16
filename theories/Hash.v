Require Import Util.
Require Asm.
Require Import ZArith Orders Lia ZifyUint63 MSetRBT PArray.
Import ListNotations.

Section Hashing.
  Variant hash :=
    | H_UBFX (lsb width: int).
  Definition hash_size h :=
    match h with
    | H_UBFX lsb width => 1 << width
    end.
  Definition hash_func h :=
    match h with
    | H_UBFX lsb width => λ v, (v >> lsb) mod (1 << width)
    end.
  Definition hash_code h r :=
    match h with
    | H_UBFX lsb width => [Asm.UBFX true r r lsb width]
    end.
  Fixpoint valid_hash h D D' s :=
    match D, D' with
    | i::t, i'::t' =>
        let k1 := hash_func h (4*i) in
        let k2 := hash_func h (4*i') in
        if (MSet.mem k1 s) || (MSet.mem k2 s)
        then false
        else let s' := MSet.add k2 (MSet.add k1 s) in
             valid_hash h t t' s'
    | _, _ => true
    end.
  Function find_ubfx_hash' width lsb D D' {measure to_nat lsb} :=
    if (lsb <=? 0) then None
    else if valid_hash (H_UBFX lsb width) D D' MSet.empty
         then Some (H_UBFX lsb width)
         else find_ubfx_hash' width (lsb-1) D D'.
  Proof. lia. Defined.
  Function find_ubfx_hash width D D' {measure (λ width, to_nat (33 - width)) width} :=
    if (32 <=? width) || (width <? 0) then None
    else match find_ubfx_hash' width 32 D D' with
         | Some h => Some h
         | None => find_ubfx_hash (width+1) D D'
         end.
  Proof. lia. Defined.
  Definition find_hash D D' :=
    find_ubfx_hash 1 D D'.
End Hashing.

Module Order.
  Definition t := (int * int)%type.
  Definition leb (a b: t) := fst b <=? fst a.
  Lemma leb_total: forall x y : t, leb x y = true \/ leb y x = true.
  Proof. unfold leb. lia. Qed.
End Order.
Require Import Sorting.Mergesort.
Module Sort := Sort Order.
Remark iieq_dec: forall x y : int * int, {x = y} + {x <> y}.
Proof. intros; destruct _, _. decide equality; apply eqs. Defined.
Definition sort_uniq lst := nodup iieq_dec (Sort.sort lst).
Section Table.
  Fixpoint assign_table h a D D' :=
    match D, D' with
    | i::t, i'::t' =>
        assign_table h a.[hash_func h (4*i)<-4*i'].[hash_func h (4*i')<-4*i'] t t'
    | _, _ => a
    end.
  Definition compute_table_a h ai D D' :=
    list_of_array (assign_table h (make (hash_size h) (4*ai)) D D').
  Function _list_of_entries entries lst n (default: int) {measure to_nat n} :=
    if (0 <? n) then
      match entries with
      | e::t =>
          if (fst e =? n-1)
          then _list_of_entries t (snd e::lst) (n-1) default
          else _list_of_entries entries (default::lst) (n-1) default
      | _ => _list_of_entries entries (default::lst) (n-1) default
      end
    else lst.
  Proof. all: lia. Defined.
  Definition list_of_entries entries sz default := _list_of_entries entries nil sz default.
  Definition compute_table_m h ai D D' :=
    let entries := (map (λ '(i, i'), (hash_func h (4*i), 4*i')) (combine D D')) in
    let entries' := (map (λ i', (hash_func h (4*i'), 4*i')) D') in
    let all_entries := sort_uniq (entries++entries') in
    list_of_entries all_entries (hash_size h) (4*ai).

End Table.
