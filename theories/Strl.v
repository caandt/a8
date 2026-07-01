Require Import List Uint63 PString Recdef Lia ZifyUint63.
Open Scope uint63.
Open Scope pstring.

Definition strl := {x: list string | Forall (fun x => x <> "") x}.
Fixpoint _slget sl i :=
  match sl with
  | nil => 0
  | a::t =>
      if (i <? length a)
      then get a i
      else _slget t (i - length a)
  end.
Definition slget (sl:strl) i := _slget (proj1_sig sl) i.
Definition _slcat := @app string.
Definition slcat (sl1 sl2: strl) : strl.
Proof.
  inversion sl1. inversion sl2.
  exists (x++x0). now apply Forall_app.
Defined.
Fixpoint _slsub sl i n :=
  if (n =? 0) then nil else
  match sl with
  | nil => nil
  | a::t =>
      if (i <? length a) then
        let x := sub a i n in
        x::_slsub t 0 (n - length x)
      else
        _slsub t (i - length a) n
  end.
Definition slsub (sl: strl) (i n: int) : strl.
Proof.
  inversion sl. exists (_slsub x i n).
  generalize n i. induction x; intros; simpl.
  - now destruct eqb.
  - destruct eqb eqn:NE; auto. apply Forall_inv_tail in H.
    destruct ltb eqn:LT; [| now apply IHx].
    constructor; [| now apply IHx].
    intro S; apply (f_equal to_list) in S.
    rewrite sub_spec in S.
    apply (f_equal (@List.length _)) in S; cbv [to_list] in S.
    rewrite length_firstn, length_skipn, length_map, length_seq in S.
    simpl in S. lia.
Defined.
Definition _sllength sl := List.fold_left add (map length sl) 0.
Definition sllength (sl: strl) := _sllength (proj1_sig sl).
Definition strl_of_list (sl: list string) : strl.
Proof.
  exists (filter (fun x => match compare x "" with | Eq => false | _ => true end) sl).
  apply Forall_forall. intros. apply filter_In in H as [_ H].
  intro. now rewrite H0 in H.
Defined.
Definition strl_of_string (s: string) : strl.
Proof.
  destruct (compare s "") eqn:E. now exists nil.
  all: exists (s::nil); constructor; try easy; intro; now rewrite H in E.
Defined.
Definition slsplice sl i sl2 :=
  slcat (slcat (slsub sl 0 i) sl2) (slsub sl (i + sllength sl2) (sllength sl)).
