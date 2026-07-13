From Picinae Require Import theory.
Require Import ZArith NArith Uint63 Lia ZifyUint63 ZifyN.

Open Scope uint63.

Module notations.
Notation toN a := (Z.to_N (to_Z a)).
Notation ofN a := (of_Z (Z.of_N a)).
Notation wN := (2 ^ N.of_nat size).
Notation "% n" := (N.modulo n wN) (at level 1, format "% n") : N_scope.
Notation "% z" := (Z.modulo z wB) (at level 1, format "% z") : Z_scope.
End notations.
Import notations.

Section I2N.
  Variable i j: int.
  Notation x := (to_Z i).
  Notation y := (to_Z j).
  Notation n := (toN i).
  Notation m := (toN j).

  Lemma id: ofN n = i. Proof. lia. Qed.
  Lemma inj: n = m -> i = j. Proof. lia. Qed.
  Lemma inj_iff: n = m <-> i = j. Proof. lia. Qed.

  Lemma inj_add: toN (i + j) = %(n + m). Proof. lia. Qed.
  Lemma inj_sub: toN (i - j) = msub 63 n m.
  Proof.
    apply N2Z.inj. rewrite sub_spec, Z2N.id, N2Z_msub by lia. lia.
  Qed.
  Lemma inj_mul: toN (i * j) = %(n * m). Proof. lia. Qed.
  Lemma inj_mod: toN (i mod j) = (n mod m)%N.
  Proof. now rewrite mod_spec, Z2N.inj_mod by lia. Qed.

  Lemma inj_lsl: toN (i << j) = %(N.shiftl n m).
  Proof.
    now rewrite lsl_spec, N.shiftl_mul_pow2, Z2N.inj_mod, Z2N.inj_mul, Z2N.inj_pow by lia.
  Qed.
  Lemma inj_lsr: toN (i >> j) = N.shiftr n m.
  Proof.
    now rewrite lsr_spec, <-Z.shiftr_div_pow2, Z2N_inj_shiftr by lia.
  Qed.
  Lemma inj_land: toN (i land j) = N.land n m.
  Proof. now rewrite land_spec', Z2N_inj_land by lia. Qed.
  Lemma inj_lor: toN (i lor j) = N.lor n m.
  Proof. now rewrite lor_spec', Z2N_inj_lor by lia. Qed.
  Lemma inj_lxor: toN (i lxor j) = N.lxor n m.
  Proof. now rewrite lxor_spec', Z2N_inj_lxor by lia. Qed.
  Lemma inj_bit: bit i j = N.testbit n m.
  Proof. rewrite bitE, <-N2Z.inj_testbit. f_equal; lia. Qed.

  Lemma inj_compare: compare i j = N.compare n m.
  Proof. now rewrite compare_spec, Z2N.inj_compare by lia. Qed.
  Lemma inj_succ: toN (succ i) = %(N.succ n). Proof. lia. Qed.
  Lemma inj_pred: toN (pred i) = msub 63 n 1.
  Proof. apply N2Z.inj. rewrite pred_spec, Z2N.id, N2Z_msub by lia. lia. Qed.
  Lemma inj_min: toN (min i j) = N.min n m.
  Proof. rewrite min_spec. lia. Qed.
  Lemma inj_max: toN (max i j) = N.max n m.
  Proof. rewrite max_spec. lia. Qed.
  Lemma inj_lt: i <? j = true <-> n < m. Proof. lia. Qed.
  Lemma inj_le: i <=? j = true <-> n <= m. Proof. lia. Qed.
End I2N.
Module I2Z. Section I2Z.
  Open Scope Z.
  Variable i j: int.
  Notation x := (to_Z i).
  Notation y := (to_Z j).

  Definition id := of_to_Z i.
  Definition inj := to_Z_inj i j.

  Definition inj_add := add_spec i j.
  Definition inj_sub := sub_spec i j.
  Definition inj_mul := mul_spec i j.
  Definition inj_mod := mod_spec i j.

  Lemma inj_lsl: to_Z (i << j) = %(Z.shiftl x y).
  Proof.
    now rewrite lsl_spec, Z.shiftl_mul_pow2 by lia.
  Qed.
  Lemma inj_lsr: to_Z (i >> j) = Z.shiftr x y.
  Proof.
    now rewrite lsr_spec, Z.shiftr_div_pow2 by lia.
  Qed.
  Definition inj_land := land_spec' i j.
  Definition inj_lor := lor_spec' i j.
  Definition inj_lxor := lxor_spec' i j.
  Definition inj_bit := bitE i j.
End I2Z. End I2Z.

Ltac nify :=
  repeat match goal with
  | |- @eq int _ _ => apply inj
  | |- ?i <? ?j = true => apply inj_lt
  | |- ?i <=? ?j = true => apply inj_le
  | |- context[toN (?i + ?j)] => rewrite (inj_add i j)
  | |- context[toN (?i - ?j)] => rewrite (inj_sub i j)
  | |- context[toN (?i * ?j)] => rewrite (inj_mul i j)
  | |- context[toN (?i mod ?j)] => rewrite (inj_mod i j)
  | |- context[toN (?i << ?j)] => rewrite (inj_lsl i j)
  | |- context[toN (?i >> ?j)] => rewrite (inj_lsr i j)
  | |- context[toN (?i land ?j)] => rewrite (inj_land i j)
  | |- context[toN (?i lor ?j)] => rewrite (inj_lor i j)
  | |- context[toN (?i lxor ?j)] => rewrite (inj_lxor i j)
  | |- context[bit ?i ?j] => rewrite (inj_bit i j)
  | |- context[compare ?i ?j] => rewrite (inj_compare i j)
  end.
Ltac zify :=
  repeat match goal with
  | |- @eq int _ _ => apply I2Z.inj
  (* | |- ?i <? ?j = true => apply inj_lt *)
  (* | |- ?i <=? ?j = true => apply inj_le *)
  | |- context[to_Z (?i + ?j)] => rewrite (I2Z.inj_add i j)
  | |- context[to_Z (?i - ?j)] => rewrite (I2Z.inj_sub i j)
  | |- context[to_Z (?i * ?j)] => rewrite (I2Z.inj_mul i j)
  | |- context[to_Z (?i mod ?j)] => rewrite (I2Z.inj_mod i j)
  | |- context[to_Z (?i << ?j)] => rewrite (I2Z.inj_lsl i j)
  | |- context[to_Z (?i >> ?j)] => rewrite (I2Z.inj_lsr i j)
  | |- context[to_Z (?i land ?j)] => rewrite (I2Z.inj_land i j)
  | |- context[to_Z (?i lor ?j)] => rewrite (I2Z.inj_lor i j)
  | |- context[to_Z (?i lxor ?j)] => rewrite (I2Z.inj_lxor i j)
  | |- context[bit ?i ?j] => rewrite (I2Z.inj_bit i j)
  | |- context[to_Z 0xff] => change (to_Z 0xff) with (Z.ones 8)
  | |- context[to_Z 0xffff] => change (to_Z 0xffff) with (Z.ones 16)
  | |- context[to_Z 0xffffff] => change (to_Z 0xffffff) with (Z.ones 24)
  | |- context[to_Z 0xffffffff] => change (to_Z 0xffffffff) with (Z.ones 32)
  (* | |- context[compare ?i ?j] => rewrite (I2Z.inj_compare i j) *)
  end.
