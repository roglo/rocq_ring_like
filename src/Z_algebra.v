(** * Z_algebra

    This module ([RingLike.Z_algebra]) provides an instantiation of
    the [ring_like] structure over the integers ([Z]).

    It defines:
    - [Z_ring_like_op]: the standard operations on [Z] (+, ×, 0, 1);
    - [Z_ring_like_ord]: the order relation and its properties;
    - [Z_ring_like_prop]: the algebraic axioms satisfied by [nat].

    This serves as a concrete test case to validate the consistency
    and generality of the abstract [ring_like] theory.
*)

Set Nested Proofs Allowed.
Require Import Stdlib.ZArith.ZArith.
Require Import Utf8 Core.

Notation "x ≤ y" := (x <= y)%Z (at level 70, y at next level) : Z_scope.
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%Z (at level 70, y at next level) :
  Z_scope.

Instance Z_ring_like_op : ring_like_op Z :=
  {| rngl_zero := 0%Z;
     rngl_one := 1%Z;
     rngl_add := Z.add;
     rngl_mul := Z.mul;
     rngl_opt_opp_or_psub := Some (inl Z.opp);
     rngl_opt_inv_or_pdiv := Some (inr Z.quot);
     rngl_opt_is_zero_divisor := None;
     rngl_opt_eq_dec := Some Z.eq_dec;
     rngl_opt_leb := Some Z.leb |}.

Theorem Z_eq_mul_0 :  ∀ n m, (n * m)%Z = 0%Z → n = 0%Z ∨ m = 0%Z.
Proof. now apply Z.eq_mul_0. Qed.

Theorem Z_integral :
  ∀ a b : Z,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
apply Z_eq_mul_0 in Hab.
now destruct Hab; [ left | right; left ].
Qed.

Theorem Z_characteristic_prop : ∀ i, rngl_mul_nat 1 (S i) ≠ 0%Z.
Proof.
intros.
cbn - [ Z.add ].
assert (Hz : ∀ i, (0 <= rngl_mul_nat 1 i)%Z). {
  clear i; intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat.
  cbn - [ Z.add ].
  induction i; [ easy | ].
  cbn - [ Z.add ].
  now destruct (List.fold_right _ _ _).
}
intros H.
specialize (Hz i).
apply Z.nlt_ge in Hz; apply Hz.
rewrite <- H.
apply Z.lt_sub_lt_add_r.
now rewrite Z.sub_diag.
Qed.

Theorem Z_mul_le_compat_nonneg :
  ∀ a b c d : Z,
  (0 <=? a)%Z = true ∧ (a <=? c)%Z = true
  → (0 <=? b)%Z = true ∧ (b <=? d)%Z = true
  → (a * b <=? c * d)%Z = true.
Proof.
intros * (Hza, Hac) (Hzb, Hbd).
apply Z.leb_le in Hza, Hac, Hzb, Hbd.
apply Z.leb_le.
now apply Z.mul_le_mono_nonneg.
Qed.

Theorem Z_mul_le_compat_nonpos :
  ∀ a b c d : Z,
  (c <=? a)%Z = true ∧ (a <=? 0)%Z = true
  → (d <=? b)%Z = true ∧ (b <=? 0)%Z = true
  → (a * b <=? c * d)%Z = true.
Proof.
intros * (Hac, Haz) (Hbd, Hbz).
apply Z.leb_le in Hac, Haz, Hbd, Hbz.
apply Z.leb_le.
now apply Z.mul_le_mono_nonpos.
Qed.

Theorem Z_not_le :
  ∀ a b : Z, (a <=? b)%Z ≠ true → a ≠ b ∧ (b <=? a)%Z = true.
Proof.
intros * Hab.
apply Bool.not_true_iff_false in Hab.
apply Z.leb_gt in Hab.
split; [ now intros H; subst b; apply Z.lt_irrefl in Hab | ].
now apply Z.leb_le, Z.lt_le_incl.
Qed.

Theorem Z_opt_le_dec : ∀ a b : Z, {(a <=? b)%Z = true} + {(a <=? b)%Z ≠ true}.
Proof.
intros.
specialize (Z_le_dec a b) as H1.
destruct H1 as [H1| H1]; [ left | right ]. {
  now apply Z.leb_le.
} {
  intros H2.
  now apply Z.leb_le in H2.
}
Qed.

Theorem Z_le_refl : ∀ a : Z, (a <=? a)%Z = true.
Proof.
intros.
apply Z.leb_le, Z.le_refl.
Qed.

Theorem Z_le_antisymm :
  ∀ a b : Z, (a <=? b)%Z = true → (b <=? a)%Z = true → a = b.
Proof.
intros * Hab Hba.
apply Z.leb_le in Hab, Hba.
now apply Z.le_antisymm.
Qed.

Theorem Z_le_trans :
  ∀ a b c : Z, (a <=? b)%Z = true → (b <=? c)%Z = true → (a <=? c)%Z = true.
Proof.
intros * Hab Hbc.
apply Z.leb_le in Hab, Hbc.
apply Z.leb_le.
now apply (Z.le_trans _ b).
Qed.

Theorem Z_add_le_mono_l :
  ∀ a b c, (b <=? c)%Z = true ↔ (a + b <=? a + c)%Z = true.
Proof.
intros.
split; intros Hbc. {
  apply Z.leb_le in Hbc.
  apply Z.leb_le.
  now apply Z.add_le_mono_l.
} {
  apply Z.leb_le in Hbc.
  apply Z.leb_le.
  now apply Z.add_le_mono_l in Hbc.
}
Qed.

(* code borrowed from my application "coq_real" *)

Theorem nat_archimedean : ∀ a b, (0 < a → ∃ₜ n, (n * a > b)%nat).
Proof.
intros * Ha.
exists (S b); simpl.
induction b; [ now rewrite Nat.add_0_r | ].
simpl; rewrite <- Nat.add_1_l.
now apply Nat.add_le_lt_mono.
Qed.

Theorem Pos2Nat_neq_0 : ∀ a, Pos.to_nat a ≠ 0%nat.
Proof.
intros.
specialize (Pos2Nat.is_pos a) as Ha.
now intros H; rewrite H in Ha.
Qed.

Theorem Pos_archimedean : ∀ a b, ∃ₜ n, (Pos.of_nat n * a > b)%positive.
Proof.
intros.
specialize (Pos2Nat.is_pos a) as Ha.
specialize (nat_archimedean (Pos.to_nat a) (Pos.to_nat b) Ha) as (m, Hm).
exists m.
replace a with (Pos.of_nat (Pos.to_nat a)) by apply Pos2Nat.id.
rewrite <- Pos2Nat.id.
rewrite <- Nat2Pos.inj_mul.
 unfold Pos.gt.
 rewrite <- Nat2Pos.inj_compare; [ now apply Nat.compare_gt_iff | | ].
  destruct m; [ easy | ].
  apply Nat.neq_mul_0.
  split; [ apply Nat.neq_succ_0 | ].
  apply Pos2Nat_neq_0.

  apply Pos2Nat_neq_0.

 intros H; rewrite H in Hm; simpl in Hm.
 apply Nat.nle_gt in Hm; apply Hm.
 apply Nat.lt_le_incl.
 apply Pos2Nat.is_pos.

 apply Pos2Nat_neq_0.
Qed.

Theorem Z_archimedean' : ∀ a b, (0 < a → ∃ₜ n, Z.of_nat n * a > b)%Z.
Proof.
intros * Ha.
destruct b as [| b| b].
 exists 1%nat.
 rewrite Z.mul_1_l.
 now apply Z.lt_gt.

 destruct a as [| a| a]; [ easy | | ].
  specialize (Pos_archimedean a b) as (m, Hm).
  destruct m; [ now exists 1%nat | ].
  exists (S m).
  apply Pos2Nat.inj_gt in Hm.
  rewrite Pos2Nat.inj_mul in Hm.
  rewrite Nat2Pos.id in Hm; [ | apply Nat.neq_succ_0 ].
  rewrite <- positive_nat_Z.
  rewrite <- Nat2Z.inj_mul.
  rewrite <- positive_nat_Z.
  now apply Nat2Z.inj_gt.

  apply Z.nle_gt in Ha.
  exfalso; apply Ha.
  apply Pos2Z.neg_is_nonpos.

 exists 1%nat.
 rewrite Z.mul_1_l.
 apply Z.lt_gt.
 eapply Z.lt_trans; [ | eassumption ].
 apply Pos2Z.neg_is_neg.
Qed.

(* end borrowed code *)

Theorem rngl_mul_nat_Z : ∀ z n, rngl_mul_nat z n = (Z.of_nat n * z)%Z.
Proof.
intros.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction n; intros; [ easy | ].
cbn - [ "*"%Z ].
rewrite IHn.
rewrite <- (Z.mul_1_l z) at 1.
rewrite <- Z.mul_add_distr_r.
f_equal.
rewrite Z.add_1_l.
now rewrite <- Nat2Z.inj_succ.
Qed.

Theorem Z_archimedean :
  ∀ a b : Z, (0 < a)%L → ∃ₜ n : nat, (b < rngl_mul_nat a n)%L.
Proof.
intros * Ha *.
apply Z.leb_gt in Ha.
cbn in Ha.
specialize (Z_archimedean' a b Ha) as H1.
destruct H1 as (m & Hm).
exists m; cbn.
apply Z.compare_gt_iff in Hm.
apply Z.leb_gt.
now rewrite rngl_mul_nat_Z.
Qed.

Definition Z_ring_like_ord :=
  {| rngl_ord_le_dec := Z_opt_le_dec;
     rngl_ord_le_refl := Z_le_refl;
     rngl_ord_le_antisymm := Z_le_antisymm;
     rngl_ord_le_trans := Z_le_trans;
     rngl_ord_add_le_mono_l := Z_add_le_mono_l;
     rngl_ord_mul_le_compat_nonneg := Z_mul_le_compat_nonneg;
     rngl_ord_mul_le_compat_nonpos := Z_mul_le_compat_nonpos;
     rngl_ord_not_le := Z_not_le |}.

Definition Z_ring_like_prop : ring_like_prop Z :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Z.add_comm;
     rngl_add_assoc := Z.add_assoc;
     rngl_add_0_l := Z.add_0_l;
     rngl_mul_assoc := Z.mul_assoc;
     rngl_mul_1_l := Z.mul_1_l;
     rngl_mul_add_distr_l := Z.mul_add_distr_l;
     rngl_opt_mul_comm := Z.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_diag_l := Z.add_opp_diag_l;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := Z.quot_mul;
     rngl_opt_integral := Z_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := Z_characteristic_prop;
     rngl_opt_ord := Z_ring_like_ord;
     rngl_opt_archimedean := Z_archimedean |}.
