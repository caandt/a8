Require Import List Uint63 PString Recdef Lia ZifyUint63 ZArith Utf8.
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
Fixpoint sldrop sl n :=
  if (n =? 0) then sl else
  match sl with
  | nil => nil
  | a::t =>
      if (n <? length a) then
        sub a n (length a)::t
      else
        sldrop t (n - length a)
  end.
Fixpoint sllt sl n :=
  if (n =? 0) then false else
  match sl with
  | nil => true
  | a::t =>
      if (n <? length a) then false
      else sllt t (n - length a)
  end.
Definition slsplice sl i sl2 :=
  slcat (slcat (slsub sl 0 i) sl2) (sldrop sl (i + sllength sl2)).
Definition list_of_strl sl := List.concat (map to_list sl).
Notation "'LO'" := list_of_strl.
Notation slequiv sl1 sl2 := (list_of_strl sl1 = list_of_strl sl2).
Infix "≡" := slequiv.
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
Lemma list_drop:
  forall sl n, LO (sldrop sl n) = skipn (to_nat n) (LO sl).
Proof.
  unfold list_of_strl. induction sl; intros; simpl.
    destruct eqb; now rewrite skipn_nil.
    destruct eqb eqn:EQ.
      apply eqb_correct in EQ. now rewrite EQ.
      destruct ltb eqn:LT.
      - simpl. rewrite sub_spec, firstn_all2, skipn_app, <-length_spec.
        now replace (_ - _)%nat with O by lia.
        rewrite length_skipn, <-length_spec. lia.
      - rewrite IHsl, skipn_app, <-length_spec, (skipn_all2 (to_list a)).
        simpl. f_equal. lia.
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
Lemma list_splice:
  forall sl1 i sl2,
    LO (slsplice sl1 i sl2) =
    firstn (to_nat i) (LO sl1)++LO sl2++skipn (to_nat (i + sllength sl2)) (LO sl1).
Proof.
  intros. unfold slsplice.
  rewrite !list_cat, !list_sub, list_drop, skipn_O, app_assoc. f_equal.
Qed.

Lemma equiv_get:
  forall sl1 sl2 i, sl1 ≡ sl2 -> slget sl1 i = slget sl2 i.
Proof.
  intros. now rewrite !list_get, H.
Qed.
Lemma sub_equiv_get:
  forall sl1 sl2 i j, slsub sl1 i j ≡ slsub sl2 i j ->
  (to_Z i + to_Z j < wB)%Z ->
  forall k, k <? j = true ->
  slget sl1 (i+k) = slget sl2 (i+k).
Proof.
  intros. rewrite !list_get. rewrite !list_sub in H.
  replace (to_nat _) with (to_nat i + to_nat k)%nat by lia.
  rewrite <-!nth_skipn.
  apply (f_equal (λ l, nth (to_nat k) l 0)) in H.
  rewrite !nth_firstn in H.
  now replace _ with true in H by lia.
Qed.
Definition get_before:
  forall sl i j, i <? j = true -> slget sl i = slget (slsub sl 0 j) i.
Proof.
  intros. replace i with (0 + i). erewrite sub_equiv_get. easy.
  now rewrite !list_sub, !skipn_O, firstn_firstn, Nat.min_id.
  all: lia.
Qed.
Definition get_sub:
  forall sl i j k, k <=? i = true -> i - k <? j = true -> slget sl i = slget (slsub sl k j) (i - k).
Proof.
  intros. rewrite !list_get, list_sub.
  rewrite nth_firstn. replace (_ <? _)%nat with true by lia.
  rewrite nth_skipn. f_equal. lia.
Qed.
Lemma splice_before:
  forall sl1 sl2 i j, i <? sllength sl1 = true -> i <? j = true ->
  slsub (slsplice sl1 j sl2) 0 i ≡ slsub sl1 0 i.
Proof.
  intros. unfold slsplice.
  rewrite !list_sub, !list_cat, !list_sub, !skipn_O, <-app_assoc.
  rewrite firstn_app, length_firstn, firstn_firstn.
  replace (_ - _)%nat with O by (rewrite list_length in H; lia).
  rewrite firstn_O, app_nil_r. f_equal. lia.
Qed.
Lemma sub_splice:
  forall sl1 sl2 i j,
    i <? sllength sl1 = true -> 
    to_Z j = Zlength (LO sl2) ->
    slsub (slsplice sl1 i sl2) i j ≡ sl2.
Proof.
  intros. rewrite list_sub, list_splice.
  rewrite skipn_app, length_firstn, skipn_firstn_comm, Nat.sub_diag, firstn_O, app_nil_l.
  rewrite list_length in H. replace (_-_)%nat with O by lia.
  rewrite skipn_O, firstn_app. rewrite Zlength_correct in H0.
  replace (_-_)%nat with O by lia. rewrite firstn_O, app_nil_r, firstn_all2.
  easy. lia.
Qed.

Lemma equiv_sub:
  forall sl1 sl2 i j, sl1 ≡ sl2 -> slsub sl1 i j ≡ slsub sl2 i j.
Proof.
  intros. now rewrite !list_sub, H.
Qed.
Lemma cat_splice:
  forall sl1 sl2 sl3 i, i + sllength sl2 <? sllength sl1 = true ->
  (to_Z i + Zlength (LO sl2) < wB)%Z ->
  slcat (slsplice sl1 i sl2) sl3 ≡ slsplice (slcat sl1 sl3) i sl2.
Proof.
  intros. rewrite list_cat, !list_splice, list_cat, <-!app_assoc.
  rewrite Zlength_correct in H0.
  f_equal. rewrite firstn_app. rewrite !list_length in H. replace (_ - _)%nat with O. now rewrite app_nil_r. lia.
  rewrite skipn_app. replace (_ - _)%nat with O. easy.
  rewrite !list_length in *. lia.
Qed.
Lemma sub_cat:
  forall sl1 sl2 i j, i+j <? sllength sl1 = true ->
  (to_Z i + to_Z j < wB)%Z ->
  slsub (slcat sl1 sl2) i j ≡ slsub sl1 i j.
Proof.
  intros. rewrite !list_sub, list_cat.
  rewrite skipn_app, firstn_app.
  replace (_ - _)%nat with O.
  now rewrite firstn_O, app_nil_r.
  rewrite length_skipn. rewrite list_length in H. lia.
Qed.
Lemma sub_cat1:
  forall sl1 sl2 i j,
  (to_Z i + to_Z j <= Zlength (LO sl1))%Z ->
  slsub (slcat sl1 sl2) i j ≡ slsub sl1 i j.
Proof.
  intros. rewrite !list_sub, list_cat.
  rewrite skipn_app, firstn_app.
  replace (_ - _)%nat with O.
  now rewrite firstn_O, app_nil_r.
  rewrite length_skipn. rewrite Zlength_correct in H. lia.
Qed.
Lemma sub_cat2:
  forall sl1 sl2 i j,
  (Zlength (LO sl1) <= to_Z i)%Z ->
  slsub (slcat sl1 sl2) i j ≡ slsub sl2 (i - sllength sl1) j.
Proof.
  intros. rewrite !list_sub, list_cat.
  rewrite Zlength_correct in H.
  rewrite skipn_app, skipn_all2, app_nil_l by lia.
  repeat f_equal. rewrite list_length. lia.
Qed.
Lemma slltl:
  forall sl n, sllt sl n = true <-> (Zlength (LO sl) < to_Z n)%Z.
Proof.
  setoid_rewrite Zlength_correct.
  induction sl; intros; simpl.
    destruct eqb eqn:E; lia.
    destruct eqb eqn:E. lia.
      unfold list_of_strl in *.
      rewrite map_cons, concat_cons, length_app, <-length_spec.
      destruct ltb eqn:L. lia.
        split; intro.
          apply IHsl in H. lia.
          apply IHsl. lia.
Qed.
Lemma length_splice:
  forall sl1 i sl2, i + sllength sl2 <? sllength sl1 = true ->
  (to_Z i + Zlength (LO sl2) < wB)%Z ->
  sllength (slsplice sl1 i sl2) = sllength sl1.
Proof.
  intros. rewrite Zlength_correct, !list_length in *.
  rewrite list_splice, !length_app, length_firstn, length_skipn, !list_length in *. lia.
Qed.
Lemma length_splice':
  forall sl1 i sl2, i + sllength sl2 <? sllength sl1 = true ->
  (to_Z i + Zlength (LO sl2) < wB)%Z ->
  List.length (LO (slsplice sl1 i sl2)) = List.length (LO sl1).
Proof.
  intros. rewrite Zlength_correct, !list_length in *.
  rewrite list_splice, !length_app, length_firstn, length_skipn, !list_length in *. lia.
Qed.
Lemma equiv_trans:
  forall sl1 sl2 sl3, sl1 ≡ sl2 -> sl2 ≡ sl3 -> sl1 ≡ sl3.
Proof. intros. now rewrite H. Qed.
