Require Import List Uint63 PString Recdef Lia ZifyUint63.
Open Scope uint63.
Open Scope pstring.

Fixpoint slget sl i :=
  match sl with
  | nil => 0
  | a::t =>
      if (i <? length a)
      then get a i
      else slget t (i - length a)
  end.
Definition slcat := @app string.
Fixpoint slsub sl i n :=
  if (n =? 0) then nil else
  match sl with
  | nil => nil
  | a::t =>
      if (i <? length a) then
        let x := sub a i n in
        x::slsub t 0 (n - length x)
      else
        slsub t (i - length a) n
  end.
Definition sllength sl := List.fold_left add (map length sl) 0.
Definition slsplice sl i sl2 :=
  slcat (slcat (slsub sl 0 i) sl2) (slsub sl (i + sllength sl2) (sllength sl)).
Definition list_of_strl sl := List.concat (map to_list sl).
Notation "'LO'" := list_of_strl.
Definition slequiv sl1 sl2 := list_of_strl sl1 = list_of_strl sl2.
Infix "~" := slequiv (at level 10).
Lemma list_get:
  forall sl i, slget sl i = nth (to_nat i) (LO sl) 0.
Proof.
  induction sl; intros; unfold list_of_strl.
    simpl. now destruct (_:nat).
    simpl. destruct ltb eqn:LT.
      rewrite app_nth1. apply get_spec.
      rewrite <-length_spec. lia.
    rewrite IHsl. rewrite app_nth2, <-length_spec. f_equal. lia.
    rewrite <-length_spec. lia.
Qed.
Lemma list_cat:
  forall sl1 sl2, LO (slcat sl1 sl2) = LO sl1 ++ LO sl2.
Proof.
  intros. unfold slcat, list_of_strl. now rewrite map_app, concat_app.
Qed.
Lemma list_sub:
  forall sl i n, LO (slsub sl i n) = firstn (to_nat n) (skipn (to_nat i) (LO sl)).
Proof.
  unfold list_of_strl. induction sl; intros; simpl.
    destruct eqb; now rewrite skipn_nil, firstn_nil.
    destruct eqb eqn:EQ.
      apply eqb_correct in EQ. now rewrite EQ.
      destruct ltb eqn:LT.
      - simpl. rewrite IHsl, skipn_app, firstn_app.
        f_equal. apply sub_spec.
        f_equal. rewrite length_spec_int, sub_spec, length_firstn, length_skipn. lia.
        f_equal. rewrite <-length_spec. lia.
      - rewrite IHsl, skipn_app.
        f_equal. rewrite (skipn_all2 (to_list a)), app_nil_l.
        f_equal. rewrite <-length_spec. lia.
        rewrite <-length_spec. lia.
Qed.
Lemma fold_add:
  forall l n, fold_left add l n = fold_left add l 0 + n.
Proof.
  induction l. simpl. lia. simpl. intro. rewrite IHl, (IHl (0+a)). lia.
Qed.
Lemma list_length:
  forall sl, sllength sl = of_nat (List.length (LO sl)).
Proof.
  intros. unfold list_of_strl.
  induction sl. easy.
  unfold sllength in *. simpl. rewrite fold_add.
  rewrite IHsl. rewrite length_app. rewrite <-length_spec. lia.
Qed.
(* Lemma list_splice: *)
(*   forall sl1 i sl2, LO (slsplice sl1 i sl2) = *)
(*     firstn (to_nat i) (LO sl1)++LO sl2++skipn (to_nat (i + sllength sl2)) (LO sl1). *)
(* Proof. *)
(*   intros. destruct sl1, sl2. unfold slsplice, sllength, slsub, list_of_strl. simpl. clear f f0. *)
  

Lemma equiv_get:
  forall sl1 sl2 i, sl1 ~ sl2 -> slget sl1 i = slget sl2 i.
Proof.
  intros. now rewrite !list_get, H.
Qed.
