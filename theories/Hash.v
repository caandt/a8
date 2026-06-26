Require Import Util.
Require Asm.
Require Import ZArith Orders Lia ZifyUint63 MSetRBT PArray.
Import ListNotations.

Module IntOT <: UsualOrderedType.
  Definition t := int.
  Definition eq := @eq int.
  Definition eq_equiv := @eq_equivalence int.
  Definition lt x y := (x <? y = true).
  Definition lt_strorder : StrictOrder lt.
  Proof.
    unfold lt. split. intros x LT. lia.
    intros x y z LT LT2. lia.
  Defined.
  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  Proof.
    intros a b EQ x y EQ2. unfold lt. subst. lia.
  Defined.
  Definition compare := Uint63.compare.
  Definition compare_spec : forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y. unfold compare, lt.
    rewrite Uint63.compare_spec.
    destruct (Z.compare_spec (to_Z x) (to_Z y)); constructor; auto; lia.
  Defined.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros x y. destruct (x =? y) eqn:E. left. lia. right. lia.
  Defined.
End IntOT.
Module MSet := Make IntOT.
Section HashTable.
  Variable t: Type.
  Variable In: int -> t -> Prop.
  Definition Complete T (D: t) h (rel: int -> int) :=
    forall a, In a D -> nth_error T (h a) = Some (rel a).
  Definition Idempotent T (D: t) h (rel: int -> int) :=
    forall a, In a D -> nth_error T (h (rel a)) = Some (rel a).
  Definition Safe T (D: t) h rel (ai: int) :=
    forall n, (~exists a, In a D /\ (h a = n \/ h (rel a) = n)) -> nth n T ai = ai.
End HashTable.

Section Hashing.
  Variant hash :=
    | H_UBFX (lsb width: int).
  Definition hash_size h :=
    match h with
    | H_UBFX lsb width => 1 << width
    end.
  Definition hash_func h :=
    match h with
    | H_UBFX lsb width => \v, (v >> lsb) mod (1 << width)
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
  Function find_ubfx_hash width D D' {measure (\width, to_nat (33 - width)) width} :=
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
    list_of_array (assign_table h (make (hash_size h) ai) D D').
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
    let entries := (map (\(i, i'), (hash_func h (4*i), 4*i')) (combine D D')) in
    let entries' := (map (\i', (hash_func h (4*i'), 4*i')) D') in
    let all_entries := sort_uniq (entries++entries') in
    list_of_entries all_entries (hash_size h) ai.

End Table.
