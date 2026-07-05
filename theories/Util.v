Require Export Uint63 List Bool Recdef Lia ZifyUint63.
From stdpp Require Export option.
Require PArray PrimString.
Export PArray.PArrayNotations PArray(array) PrimString.PStringNotations PrimString(string).
Open Scope uint63.

Definition xb (n i j: int) := (n >> i) land (1 << (j - i) - 1).
Notation "n `[ i , j ]" := (xb n i j) (at level 30, format "n `[ i ,  j ]").
Notation "n `[ b ]" := (xb n b%uint63 (b%uint63 + 1)) (at level 30, format "n `[ b ]").

Notation "m <&> f" := (fmap f m) (at level 61, left associativity).
Notation "'return' x " := (mret x) (at level 10000).
Definition asrt (x:bool) : option unit := if x then Some tt else None.
Notation "'assert' x ; f" := (_ ← asrt x; f) (at level 100).
Notation "x 'orelse' y" := (default y x) (at level 10).

Fixpoint _mapi {A B} acc i f (l: list A) : list B :=
  match l with
  | nil => rev acc
  | a::t => _mapi (f i a::acc) (i+1) f t
  end.
Definition mapi {A B} := @_mapi A B nil 0.

Definition maybe_op {A B C} (op: A -> B -> C) x y := x ≫= λ x, y ≫= λ y, Some (op x y).
Definition mapfold {A B C} op (f:A->B) l b : C := fold_right op b (map f l).
Definition maybe_map {A B} (f:A->option B) l := mapfold (maybe_op cons) f l (Some nil).

Definition len {A} (l:list A) := of_nat (List.length l).

Function _list_of_array{T} (arr: array T) lst n {measure to_nat n} :=
  if (n =? 0)
  then arr.[n]::lst
  else _list_of_array arr (arr.[n]::lst) (n-1).
Proof. lia. Defined.
Definition list_of_array{T} arr := if (PArray.length arr =? 0) then nil else _list_of_array T arr nil (PArray.length arr - 1).
Fixpoint _array_of_list{T} (arr: array T) n lst :=
  match lst with
  | nil => arr
  | a::t => _array_of_list arr.[n<-a] (n+1) t
  end.
Definition array_of_list{T} d (lst: list T) := _array_of_list (PArray.make (len lst) d) 0 lst.

Function init n (x:int) {measure to_nat n} :=
  if (n =? 0) then nil else x::init (n-1) x.
Proof. lia. Defined.
Definition rpad l n x :=
  let len := len l in
  if len <? n then l ++ init (n - len) x else l.

Variant _letintoken := _letintokenIN | _letintokenEXTRACTION.
Definition _letin{A B} (a:A) (_:{x:_letintoken|x=_letintokenIN}) (b:A->B) (_:{x:_letintoken|x=_letintokenEXTRACTION}) := b a.
Notation "'let*' x := y 'in' z" :=
  (_letin y (exist _ _ eq_refl) (fun x => z) (exist _ _ eq_refl))
  (at level 30, x pattern).
Extract Inductive _letintoken => "" ["in" "_ROCQ_LET_IN_EXTRACTION"].
Extract Inlined Constant _letin => "let _ROCQ_LET_IN_EXTRACTION =".

Axiom print_endline : string -> unit.
Extract Constant print_endline => "(fun x -> print_endline (Pstring.to_string x))".

Definition csum base lst :=
  let len := len lst in
  let arr := PArray.make (len+1) 0 in
  let f '(a, b, i) x := (a.[i<-b], b+x, i+1) in
  let '(res, b, i) := fold_left f lst (arr, base, 0) in
  res.[i<-b].
Fixpoint csum_fix base lst :=
  match lst with
  | nil => nil
  | a::t => base::csum_fix (base+a) t
  end.

Definition sext n w := asr (n << (63 - w)) (63 - w).

(* copy of map, to avoid using parmap extraction *)
Fixpoint map_single {A B} (f:A->B) l :=
  match l with
  | nil => nil
  | a::t => f a::map_single f t
  end.
