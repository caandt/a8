Require Export Uint63 List Bool Recdef PArray.
Require Import ZArith Lia ZifyUint63.
Open Scope uint63.

Definition xb (n i j: int) :=
  (n >> i) land (1 << (j - i) - 1).
Notation "n [ i , j ]" := (xb n i j) (at level 30, format "n [ i ,  j ]").
Notation "n [ b ]" := (xb n b%uint63 (b%uint63 + 1)) (at level 30, format "n [ b ]").

Variant bit := O | I.
Variant bits4 := b4 (b3 b2 b1 b0 : bit).
Definition tobit (n: int) := if is_zero n then O else I.
Definition tob4 (n: int) :=
  b4 (tobit (n land 8)) (tobit (n land 4)) (tobit (n land 2)) (tobit (n land 1)).

Notation "0b0000" := (b4 O O O O).
Notation "0b0001" := (b4 O O O I).
Notation "0b0010" := (b4 O O I O).
Notation "0b0011" := (b4 O O I I).
Notation "0b0100" := (b4 O I O O).
Notation "0b0101" := (b4 O I O I).
Notation "0b0110" := (b4 O I I O).
Notation "0b0111" := (b4 O I I I).
Notation "0b1000" := (b4 I O O O).
Notation "0b1001" := (b4 I O O I).
Notation "0b1010" := (b4 I O I O).
Notation "0b1011" := (b4 I O I I).
Notation "0b1100" := (b4 I I O O).
Notation "0b1101" := (b4 I I O I).
Notation "0b1110" := (b4 I I I O).
Notation "0b1111" := (b4 I I I I).

Definition orelse {A} (x: option A) y :=
  match x with
  | Some x => x
  | None => y
  end.
Notation "x 'orelse' y" := (orelse x y) (at level 10).

Fixpoint _mapi {A B} acc i f (l: list A) : list B :=
  match l with
  | nil => rev acc
  | a::t => _mapi (f i a::acc) (i+1) f t
  end.
Definition mapi {A B} := @_mapi A B nil 0.

Notation "\ x , y" := (fun x => y) (at level 100, x pattern, right associativity, format "\ x ,  y").
Notation "\ x : t , y" := (fun x : t => y) (at level 100, x pattern, right associativity, format "\ x : t ,  y").

Definition maybe_bind {A B} o (f: A -> option B) :=
  match o with
  | None => None
  | Some x => f x
  end.
Infix ">>=" := maybe_bind (at level 100).
Definition maybe_binds {A B} o (f:A->B) := maybe_bind o (\x, Some (f x)).
Infix ">>=s" := maybe_binds (at level 100).
Definition maybe_op {A B C} (op: A -> B -> C) x y := x >>= \x, y >>= \y, Some (op x y).
Definition mapfold {A B C} op (f:A->B) l b : C := fold_right op b (map f l).
Definition maybe_map {A B} (f:A->option B) l := mapfold (maybe_op cons) f l (Some nil).

(* extract as List.length *)
Definition len {A} (l:list A) := of_nat (List.length l).


Function _list_of_array{T} (arr: array T) lst n {measure to_nat n} :=
  if (n =? 0)
  then arr.[n]::lst
  else _list_of_array arr (arr.[n]::lst) (n-1).
Proof. lia. Defined.
Definition list_of_array{T} arr := _list_of_array T arr nil (length arr - 1).
Fixpoint _array_of_list{T} (arr: array T) n lst :=
  match lst with
  | nil => arr
  | a::t => _array_of_list arr.[n<-a] (n+1) t
  end.
Definition array_of_list{T} d (lst: list T) := _array_of_list (make (len lst) d) 0 lst.

Function init n (x:int) {measure to_nat n} :=
  if (n =? 0) then nil else x::init (n-1) x.
Proof. lia. Defined.
Definition rpad l n :=
  let len := len l in
  if len <? n then l ++ init (n - len) 0 else l.
