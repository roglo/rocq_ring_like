(** * Mul_with_order

Theorems about multiplication, when order relation exists.

A ring-like has an order when the variable [rngl_is_ordered]
is [true].

See the module [[RingLike.Core]] for the general description
of the ring-like library.

In general, it is not necessary to import the present module. The
normal usage is to do:
<<
    Require Import RingLike.Core.
>>
which imports the present module and some other ones.
 *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Require Import Structures.
Require Import Order.
Require Import Add.
Require Import Add_with_order.
Require Import Mul.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_mul_le_compat_nonneg :
  rngl_is_ordered T = true →
  ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
apply rngl_ord_mul_le_compat_nonneg.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_is_ordered T = true →
  ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
apply rngl_ord_mul_le_compat_nonpos.
Qed.

Theorem rngl_mul_le_compat_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d,
  (0 ≤ c ≤ a)%L
  → (b ≤ d ≤ 0)%L
  → (a * b ≤ c * d)%L.
Proof.
intros Hop Hor * Had Hcd.
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_r Hop).
apply (rngl_mul_le_compat_nonneg Hor); [ easy | ].
split.
now apply (rngl_opp_nonneg_nonpos Hop Hor).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_mul_nonneg_nonneg :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%L.
Proof.
intros * Hos Hor * Ha Hb.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonpos_nonpos :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → 0 ≤ a * b)%L.
Proof.
intros * Hos Hor * Ha Hb.
specialize (rngl_mul_le_compat_nonpos Hor) as H1.
specialize (H1 0 0 a b)%L.
assert (H : (a ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
assert (H : (b ≤ 0 ≤ 0)%L) by now split; [ | apply (rngl_le_refl Hor) ].
specialize (H1 H); clear H.
now rewrite (rngl_mul_0_l Hos) in H1.
Qed.

Theorem rngl_mul_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ 0 → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 0 0 a (- b))%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ - b)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Hb.
  now rewrite (rngl_opp_0 Hop) in Hb.
}
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_r Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_mul_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → 0 ≤ b → a * b ≤ 0)%L.
Proof.
intros * Hop Hor * Ha Hb.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 0 0 (- a) b)%L.
assert (H : (0 ≤ 0 ≤ - a)%L). {
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ apply (rngl_le_refl Hor) | ].
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_l Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_0_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (0 ≤ 1)%L.
Proof.
intros Hon Hos Hor.
destruct (rngl_le_dec Hor 0%L 1%L) as [| H1]; [ easy | ].
apply (rngl_not_le Hor) in H1.
destruct H1 as (H1, H2).
specialize (rngl_mul_nonpos_nonpos Hos Hor) as H3.
specialize (H3 1 1 H2 H2)%L.
now rewrite (rngl_mul_1_l Hon) in H3.
Qed.

Theorem rngl_0_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 1)%L.
Proof.
intros Hon Hos Hc1 Hor.
apply (rngl_le_neq Hor).
split; [ apply (rngl_0_le_1 Hon Hos Hor) | ].
apply not_eq_sym.
now apply (rngl_1_neq_0_iff Hon).
Qed.

Theorem rngl_0_leb_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (0 ≤? 1)%L = true.
Proof.
intros * Hon Hos Hor.
apply rngl_leb_le.
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_1_le_2 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (1 ≤ 2)%L.
Proof.
intros Hon Hos Hor.
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_mul_diag_nonneg :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a * a)%L.
Proof.
intros Hos Hor *.
destruct (rngl_le_dec Hor 0%L a) as [Hap| Han]. {
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
} {
  apply (rngl_not_le Hor) in Han.
  now apply (rngl_mul_nonpos_nonpos Hos Hor).
}
Qed.

Theorem rngl_squ_abs :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (rngl_abs a) = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_abs.
destruct (a ≤? 0)%L; [ | easy ].
apply (rngl_squ_opp Hop).
Qed.

Theorem rngl_squ_nonneg :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a²)%L.
Proof.
intros Hos Hor *.
apply (rngl_mul_diag_nonneg Hos Hor).
Qed.

Theorem rngl_0_le_squ :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ n, (0 ≤ n * n)%L.
Proof.
intros Hos Hor *.
apply (rngl_squ_nonneg Hos Hor).
Qed.

Theorem rngl_0_lt_2 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (0 < 2)%L.
Proof.
intros Hon Hos Hc1 Hor.
apply (rngl_le_lt_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hos Hor).
}
apply (rngl_lt_add_r Hos Hor).
apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_0_le_2 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (0 ≤ 2)%L.
Proof.
intros Hon Hos Hor.
apply (rngl_le_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hon Hos Hor).
}
apply (rngl_1_le_2 Hon Hos Hor).
Qed.

Theorem rngl_2_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  (2 ≠ 0)%L.
Proof.
intros Hon Hos Hc1 Hor.
specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as H5.
intros H; rewrite H in H5.
now apply (rngl_lt_irrefl Hor) in H5.
Qed.

Theorem rngl_opp_1_le_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (-1 ≤ 0)%L.
Proof.
intros Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_opp_nonpos_nonneg Hop Hor).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_opp_1_lt_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 0)%L.
Proof.
intros Hon Hop Hor Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_opp_neg_pos Hop Hor).
apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_opp_1_lt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 1)%L.
Proof.
intros Hon Hop Hor Hc1.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_lt_le_trans Hor _ 0)%L.
apply (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_opp_1_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (-1 ≤ 1)%L.
Proof.
intros Hon Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_trans Hor _ 0). {
  apply (rngl_opp_1_le_0 Hon Hop Hor).
} {
  apply (rngl_0_le_1 Hon Hos Hor).
}
Qed.

Theorem rngl_of_nat_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ n, (0 ≤ rngl_of_nat n)%L.
Proof.
intros Hon Hos Hor.
intros.
induction n; [ apply (rngl_le_refl Hor) | ].
rewrite rngl_of_nat_succ.
eapply (rngl_le_trans Hor); [ apply IHn | ].
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hon Hos Hor).
Qed.

Theorem rngl_of_nat_inj_le :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i ≤ j ↔ (rngl_of_nat i ≤ rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
apply (rngl_mul_nat_inj_le Hop Hor).
apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_of_nat_inj_lt :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ i j, i < j ↔ (rngl_of_nat i < rngl_of_nat j)%L.
Proof.
intros Hon Hop Hc1 Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
apply (rngl_mul_nat_inj_lt Hop Hor).
apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_abs_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (rngl_abs 1 = 1)%L.
Proof.
intros Hon Hos Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (rngl_abs 1)%L), (H1 1%L).
}
progress unfold rngl_abs.
remember (1 ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply rngl_leb_le in Hc.
apply rngl_nlt_ge in Hc.
exfalso; apply Hc.
apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_abs_2 :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (rngl_abs 2 = 2)%L.
Proof.
intros Hon Hos Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1; apply H1.
}
progress unfold rngl_abs.
remember (2 ≤? 0)%L as tz eqn:Htz.
symmetry in Htz.
destruct tz; [ | easy ].
apply rngl_leb_le in Htz.
apply rngl_nlt_ge in Htz.
exfalso; apply Htz.
apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_add_squ_nonneg :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a² + b²)%L.
Proof.
intros Hos Hor *.
apply (rngl_le_0_add Hor); apply (rngl_squ_nonneg Hos Hor).
Qed.

Theorem rngl_mul_le_mono_nonneg_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ a)%L → (b ≤ c)%L → (a * b ≤ a * c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonneg_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ c → a ≤ b → a * c ≤ b * c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonpos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ 0)%L → (b ≤ c)%L → (a * c ≤ a * b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonpos_nonpos Hos Hor); [ easy | ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_mul_le_mono_nonpos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (c ≤ 0 → a ≤ b → b * c ≤ a * c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonpos_nonpos Hos Hor); [ | easy ].
apply (rngl_le_sub_0 Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_lt_mul_0_if :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a * b < 0)%L → (a < 0 < b)%L ∨ (0 < a)%L ∧ (b < 0)%L.
Proof.
intros Hos Hor.
intros * Hab.
remember (a <? 0)%L as az eqn:Haz.
symmetry in Haz.
destruct az. {
  apply rngl_ltb_lt in Haz.
  left.
  split; [ easy | ].
  remember (0 <? b)%L as zb eqn:Hzb.
  symmetry in Hzb.
  destruct zb; [ now apply rngl_ltb_lt in Hzb | exfalso ].
  apply (rngl_ltb_ge_iff Hor) in Hzb.
  apply rngl_nle_gt in Hab.
  apply Hab; clear Hab.
  apply (rngl_mul_nonpos_nonpos Hos Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor) in Haz.
}
apply (rngl_ltb_ge_iff Hor) in Haz.
right.
split. {
  apply (rngl_le_neq Hor).
  split; [ easy | ].
  intros H; subst a.
  rewrite (rngl_mul_0_l Hos) in Hab.
  now apply (rngl_lt_irrefl Hor) in Hab.
}
apply (rngl_nle_gt_iff Hor).
intros Hzb.
apply rngl_nle_gt in Hab.
apply Hab; clear Hab.
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_pow_ge_1 :
  rngl_has_opp_or_subt T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a n, (1 ≤ a → 1 ≤ a ^ n)%L.
Proof.
intros Hos Hon Hor * Hza.
induction n; [ apply (rngl_le_refl Hor) | cbn ].
rewrite <- (rngl_mul_1_l Hon 1%L).
apply (rngl_mul_le_compat_nonneg Hor). {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hos Hor).
} {
  split; [ | easy ].
  apply (rngl_0_le_1 Hon Hos Hor).
}
Qed.

Theorem rngl_pow_le_mono_l :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a b n, (0 ≤ a)%L → (a ≤ b)%L → (a ^ n ≤ b ^ n)%L.
Proof.
intros Hop Hon Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1a Hmn.
induction n; [ apply (rngl_le_refl Hor) | cbn ].
apply (rngl_mul_le_compat_nonneg Hor); [ easy | ].
split; [ | easy ].
clear IHn.
induction n; cbn; [ apply (rngl_0_le_1 Hon Hos Hor) | ].
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_pow_le_mono_r :
  rngl_has_opp T = true →
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a m n, (1 ≤ a)%L → m ≤ n → (a ^ m ≤ a ^ n)%L.
Proof.
intros Hop Hon Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * H1a Hmn.
revert n Hmn.
induction m; intros; cbn. {
  now apply (rngl_pow_ge_1 Hos Hon Hor).
}
destruct n; [ easy | cbn ].
apply Nat.succ_le_mono in Hmn.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_le_trans Hor _ 1%L); [ | easy ].
  apply (rngl_0_le_1 Hon Hos Hor).
}
now apply IHm.
Qed.

Theorem rngl_abs_le_squ_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs a ≤ rngl_abs b → a² ≤ b²)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hab.
progress unfold rngl_squ.
progress unfold rngl_abs in Hab.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hab.
    now apply (rngl_mul_le_compat_nonpos Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop).
    apply (rngl_lt_le_incl Hor) in Hbz.
    now apply (rngl_mul_le_compat_nonneg Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b).
    apply (rngl_lt_le_incl Hor) in Haz.
    now apply (rngl_mul_le_compat_nonneg Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_mul_le_compat_nonneg Hor).
  }
}
Qed.

Theorem int_part :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ a, ∃ₜ n, (rngl_of_nat n ≤ rngl_abs a < rngl_of_nat (n + 1))%L.
Proof.
intros Hon Hop Hc1 Hor Har.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
assert (Heo : rngl_has_eq_dec_or_order T = true). {
  progress unfold rngl_has_eq_dec_or_order.
  rewrite Hor.
  apply Bool.orb_true_r.
}
intros a.
destruct (rngl_lt_dec Hor 1 (rngl_abs a))%L as [Hx1| Hx1]. {
  apply (rngl_archimedean_ub Har Hor).
  split; [ apply (rngl_0_lt_1 Hon Hos Hc1 Hor) | easy ].
}
apply (rngl_nlt_ge_iff Hor) in Hx1.
destruct (rngl_eq_dec Heo (rngl_abs a) 1) as [Ha1| Ha1]. {
  exists 1.
  rewrite Ha1; cbn.
  rewrite rngl_add_0_r.
  split; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_le_neq Hor).
  split; [ apply (rngl_1_le_2 Hon Hos Hor) | ].
  intros H12.
  apply (f_equal (λ b, rngl_sub b 1))%L in H12.
  rewrite (rngl_sub_diag Hos) in H12.
  rewrite (rngl_add_sub Hos) in H12.
  symmetry in H12; revert H12.
  apply (rngl_1_neq_0_iff Hon), Hc1.
}
exists 0; cbn.
rewrite rngl_add_0_r.
split; [ apply (rngl_abs_nonneg Hop Hor) | ].
now apply (rngl_le_neq Hor).
Qed.

End a.
