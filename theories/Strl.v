Require Import List Uint63 PString Recdef Lia ZifyUint63.
Open Scope uint63.
Open Scope pstring.

Definition strl := list string.
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
Definition sllength sl :=
  List.fold_left add (map length sl) 0.

Lemma sub_len_0:
  forall off sl, slsub sl off 0 = nil.
Proof. now destruct sl. Qed.
Lemma sub_full:
  forall sl, slsub sl 0 (sllength sl) = sl.
Proof. induction sl. easy. simpl. unfold sllength.

Import ListNotations.
Compute (slget ["01";"2345";"6789";"012345";"6"] 17).
Compute slget ["1"] 1.
