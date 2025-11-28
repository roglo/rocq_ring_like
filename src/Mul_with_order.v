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

Require Import Stdlib.Arith.Arith.
Require Import Utf8 Structures Order Add Add_with_order Mul.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Tactic Notation "pauto" := progress auto.
Hint Resolve rngl_le_refl : core.

Theorem rngl_mul_le_compat_nonneg :
  rngl_is_ordered T = true →
  ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr after rp.
apply rngl_ord_mul_le_compat_nonneg.
Qed.

Theorem rngl_mul_le_compat_nonpos :
  rngl_is_ordered T = true →
  ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr after rp.
apply rngl_ord_mul_le_compat_nonpos.
Qed.

Theorem rngl_mul_le_compat_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b c d,
  (0 ≤ c ≤ a)%L
  → (b ≤ d ≤ 0)%L
  → (a * b ≤ c * d)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Had Hcd.
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_r Hop).
apply (rngl_mul_le_compat_nonneg Hor); [ easy | ].
split.
now apply (rngl_opp_nonneg_nonpos Hop Hto).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_mul_nonneg_nonneg :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a * b)%L.
Proof.
intros Hos Hor.
intros * Ha Hb.
rewrite <- (rngl_mul_0_l Hos 0)%L.
apply (rngl_mul_le_compat_nonneg Hor).
split; [ pauto | easy ].
split; [ pauto | easy ].
Qed.

Theorem rngl_mul_nonpos_nonpos :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → 0 ≤ a * b)%L.
Proof.
intros Hos Hor.
intros * Ha Hb.
rewrite <- (rngl_mul_0_l Hos 0)%L.
apply (rngl_mul_le_compat_nonpos Hor).
split; [ easy | pauto ].
split; [ easy | pauto ].
Qed.

Theorem rngl_mul_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ 0 → a * b ≤ 0)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha Hb.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 0 0 a (- b))%L.
assert (H : (0 ≤ 0 ≤ a)%L) by now split; [ pauto | ].
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ - b)%L). {
  split; [ pauto | ].
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
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤ 0 → 0 ≤ b → a * b ≤ 0)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha Hb.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 0 0 (- a) b)%L.
assert (H : (0 ≤ 0 ≤ - a)%L). {
  split; [ pauto | ].
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
specialize (H1 H); clear H.
assert (H : (0 ≤ 0 ≤ b)%L) by now split; [ pauto | ].
specialize (H1 H); clear H.
rewrite (rngl_mul_0_l Hos) in H1.
rewrite (rngl_mul_opp_l Hop) in H1.
apply (rngl_opp_le_compat Hop Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
now rewrite (rngl_opp_0 Hop) in H1.
Qed.

Theorem rngl_0_le_1 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  (0 ≤ 1)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (rngl_leb_dec 0 1) as [| H1]; [ now apply rngl_leb_le | ].
apply rngl_leb_nle in H1.
apply (rngl_not_le Hto) in H1.
destruct H1 as (H1, H2).
specialize (rngl_mul_nonpos_nonpos Hos Hor) as H3.
specialize (H3 1 1 H2 H2)%L.
now rewrite rngl_mul_1_l in H3.
Qed.

Theorem rngl_0_lt_1 :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  (0 < 1)%L.
Proof.
intros Hos Hc1 Hto.
apply rngl_le_neq.
split; [ apply (rngl_0_le_1 Hos Hto) | ].
apply not_eq_sym.
now apply (rngl_1_neq_0_iff).
Qed.

Theorem rngl_0_leb_1 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  (0 ≤? 1)%L = true.
Proof.
intros * Hos Hto.
apply rngl_leb_le.
apply (rngl_0_le_1 Hos Hto).
Qed.

Theorem rngl_1_le_2 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  (1 ≤ 2)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
apply (rngl_le_add_l Hos Hor).
apply (rngl_0_le_1 Hos Hto).
Qed.

Theorem rngl_0_le_2 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  (0 ≤ 2)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
apply (rngl_le_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hos Hto).
}
apply (rngl_1_le_2 Hos Hto).
Qed.

Theorem rngl_0_lt_2 :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  (0 < 2)%L.
Proof.
intros Hos Hc1 Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
apply (rngl_le_lt_trans Hor _ 1)%L. {
  apply (rngl_0_le_1 Hos Hto).
}
apply (rngl_lt_add_r Hos Hto).
apply (rngl_0_lt_1 Hos Hc1 Hto).
Qed.

Theorem rngl_2_neq_0 :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  (2 ≠ 0)%L.
Proof.
intros Hos Hc1 Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_0_lt_2 Hos Hc1 Hto) as H5.
intros H; rewrite H in H5.
now apply rngl_lt_irrefl in H5.
Qed.

Theorem rngl_0_lt_3 :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
 (0 < 3)%L.
Proof.
intros Hos Hc1 Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
apply (rngl_lt_le_trans Hor _ 1).
apply (rngl_0_lt_1 Hos Hc1 Hto).
apply (rngl_le_add_l Hos Hor).
apply (rngl_0_le_2 Hos Hto).
Qed.

Theorem rngl_3_neq_0 :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  (3 ≠ 0)%L.
Proof.
intros Hos Hc1 Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_0_lt_3 Hos Hc1 Hto) as H.
intros H1; rewrite H1 in H.
now apply rngl_lt_irrefl in H.
Qed.

Theorem rngl_opp_1_le_0 :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  (-1 ≤ 0)%L.
Proof.
intros Hop Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
apply (rngl_opp_nonpos_nonneg Hop Hto).
apply (rngl_0_le_1 Hos Hto).
Qed.

Theorem rngl_opp_1_lt_0 :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 0)%L.
Proof.
intros Hop Hto Hc1.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
apply (rngl_opp_neg_pos Hop Hto).
apply (rngl_0_lt_1 Hos Hc1 Hto).
Qed.

Theorem rngl_opp_1_lt_1 :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  rngl_characteristic T ≠ 1 →
  (-1 < 1)%L.
Proof.
intros Hop Hto Hc1.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
apply (rngl_lt_le_trans Hor _ 0).
apply (rngl_opp_1_lt_0 Hop Hto Hc1).
apply (rngl_0_le_1 Hos Hto).
Qed.

Theorem rngl_opp_1_le_1 :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  (-1 ≤ 1)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
apply (rngl_le_trans Hor _ 0).
apply (rngl_opp_1_le_0 Hop Hto).
apply (rngl_0_le_1 Hos Hto).
Qed.

Theorem rngl_mul_diag_nonneg :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (0 ≤ a * a)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
destruct (rngl_leb_dec 0 a) as [Hap| Han]. {
  apply rngl_leb_le in Hap.
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
} {
  apply rngl_leb_nle in Han.
  apply (rngl_not_le Hto) in Han.
  now apply (rngl_mul_nonpos_nonpos Hos Hor).
}
Qed.

Theorem rngl_squ_nonneg :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (0 ≤ a²)%L.
Proof.
intros Hos Hto *.
apply (rngl_mul_diag_nonneg Hos Hto).
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

Theorem rngl_of_nat_nonneg :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ n, (0 ≤ rngl_of_nat n)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
induction n; [ pauto | ].
rewrite rngl_of_nat_succ.
eapply (rngl_le_trans Hor); [ apply IHn | ].
apply (rngl_le_add_l Hos Hor).
apply (rngl_0_le_1 Hos Hto).
Qed.

(******)

Theorem rngl_of_nat_inj_le :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  ∀ i j, i ≤ j ↔ (rngl_of_nat i ≤ rngl_of_nat j)%L.
Proof.
intros Hos Hc1 Hto *.
apply (rngl_mul_nat_inj_le Hos Hto).
apply (rngl_0_lt_1 Hos Hc1 Hto).
Qed.

Theorem rngl_of_nat_inj_lt :
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  ∀ i j, i < j ↔ (rngl_of_nat i < rngl_of_nat j)%L.
Proof.
intros Hos Hc1 Hto *.
apply (rngl_mul_nat_inj_lt Hos Hto).
apply (rngl_0_lt_1 Hos Hc1 Hto).
Qed.

Theorem rngl_abs_1 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  (rngl_abs 1 = 1)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  now rewrite (H1 (rngl_abs 1)%L), (H1 1%L).
}
progress unfold rngl_abs.
remember (1 ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | easy ].
apply rngl_leb_le in Hc.
apply (rngl_nlt_ge Hor) in Hc.
exfalso; apply Hc.
apply (rngl_0_lt_1 Hos Hc1 Hto).
Qed.

Theorem rngl_abs_2 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  (rngl_abs 2 = 2)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1; apply H1.
}
progress unfold rngl_abs.
remember (2 ≤? 0)%L as tz eqn:Htz.
symmetry in Htz.
destruct tz; [ | easy ].
apply rngl_leb_le in Htz.
apply (rngl_nlt_ge Hor) in Htz.
exfalso; apply Htz.
apply (rngl_0_lt_2 Hos Hc1 Hto).
Qed.

Theorem rngl_add_squ_nonneg :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (0 ≤ a² + b²)%L.
Proof.
intros Hos Hto.
intros *.
apply (rngl_le_0_add Hos Hto); apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem rngl_mul_le_mono_nonneg_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ a)%L → (b ≤ c)%L → (a * b ≤ a * c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; pauto ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_le_0_sub Hop Hor).
now apply rngl_lt_le_incl.
Qed.

Theorem rngl_mul_le_mono_nonneg_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ c → a ≤ b → a * c ≤ b * c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; pauto ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
apply (rngl_le_0_sub Hop Hor).
now apply rngl_lt_le_incl.
Qed.

Theorem rngl_mul_le_mono_nonpos_l :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b c, (a ≤ 0)%L → (b ≤ c)%L → (a * c ≤ a * b)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha Hbc.
apply (rngl_lt_eq_cases Hor) in Hbc.
destruct Hbc as [Hbc| Hbc]; [ | subst b; pauto ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_l Hop).
apply (rngl_mul_nonpos_nonpos Hos Hor); [ easy | ].
apply (rngl_le_sub_0 Hop Hor).
now apply rngl_lt_le_incl.
Qed.

Theorem rngl_mul_le_mono_nonpos_r :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b c, (c ≤ 0 → a ≤ b → b * c ≤ a * c)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hc Hab.
apply (rngl_lt_eq_cases Hor) in Hab.
destruct Hab as [Hab| Hab]; [ | subst b; pauto ].
apply (rngl_le_0_sub Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_mul_nonpos_nonpos Hos Hor); [ | easy ].
apply (rngl_le_sub_0 Hop Hor).
now apply rngl_lt_le_incl.
Qed.

Theorem rngl_lt_mul_0_if :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a * b < 0)%L → (a < 0 < b)%L ∨ (0 < a)%L ∧ (b < 0)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hab.
remember (a <? 0)%L as az eqn:Haz.
symmetry in Haz.
destruct az. {
  apply (rngl_ltb_lt Heo) in Haz.
  left.
  split; [ easy | ].
  remember (0 <? b)%L as zb eqn:Hzb.
  symmetry in Hzb.
  destruct zb; [ now apply (rngl_ltb_lt Heo) in Hzb | exfalso ].
  apply (rngl_ltb_ge_iff Hto) in Hzb.
  apply (rngl_nle_gt Hor) in Hab.
  apply Hab; clear Hab.
  apply (rngl_mul_nonpos_nonpos Hos Hor); [ | easy ].
  now apply rngl_lt_le_incl in Haz.
}
apply (rngl_ltb_ge_iff Hto) in Haz.
right.
split. {
  apply rngl_le_neq.
  split; [ easy | ].
  intros H; subst a.
  rewrite (rngl_mul_0_l Hos) in Hab.
  now apply rngl_lt_irrefl in Hab.
}
apply (rngl_nle_gt_iff Hto).
intros Hzb.
apply (rngl_nle_gt Hor) in Hab.
apply Hab; clear Hab.
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_pow_ge_1 :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ a n, (1 ≤ a → 1 ≤ a ^ n)%L.
Proof.
intros Hos Hto * Hza.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
induction n; [ pauto | cbn ].
rewrite <- (rngl_mul_1_l 1%L).
apply (rngl_mul_le_compat_nonneg Hor). {
  split; [ | easy ].
  apply (rngl_0_le_1 Hos Hto).
} {
  split; [ | easy ].
  apply (rngl_0_le_1 Hos Hto).
}
Qed.

Theorem rngl_pow_le_mono_l :
  rngl_has_opp_or_psub T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b n, (0 ≤ a)%L → (a ≤ b)%L → (a ^ n ≤ b ^ n)%L.
Proof.
intros Hos Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * H1a Hmn.
induction n; [ pauto | cbn ].
apply (rngl_mul_le_compat_nonneg Hor); [ easy | ].
split; [ | easy ].
clear IHn.
induction n; cbn; [ apply (rngl_0_le_1 Hos Hto) | ].
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_pow_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a m n, (1 ≤ a)%L → m ≤ n → (a ^ m ≤ a ^ n)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * H1a Hmn.
revert n Hmn.
induction m; intros; cbn. {
  now apply (rngl_pow_ge_1 Hos Hto).
}
destruct n; [ easy | cbn ].
apply Nat.succ_le_mono in Hmn.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_le_trans Hor _ 1%L); [ | easy ].
  apply (rngl_0_le_1 Hos Hto).
}
now apply IHm.
Qed.

Theorem rngl_abs_le_squ_le :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (rngl_abs a ≤ rngl_abs b → a² ≤ b²)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
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
    apply (rngl_leb_gt_iff Hto) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop).
    apply rngl_lt_le_incl in Hbz.
    now apply (rngl_mul_le_compat_nonneg Hor).
  }
} {
  apply (rngl_leb_gt_iff Hto) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b).
    apply rngl_lt_le_incl in Haz.
    now apply (rngl_mul_le_compat_nonneg Hor).
  } {
    apply (rngl_leb_gt_iff Hto) in Hbz.
    apply rngl_lt_le_incl in Haz, Hbz.
    now apply (rngl_mul_le_compat_nonneg Hor).
  }
}
Qed.

Theorem int_part :
  rngl_has_opp T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_totally_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ a, ∃ₜ n, (rngl_of_nat n ≤ rngl_abs a < rngl_of_nat (n + 1))%L.
Proof.
intros Hop Hc1 Hto Har.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros a.
destruct (rngl_ltb_dec 1 (rngl_abs a))%L as [Hx1| Hx1]. {
  apply (rngl_ltb_lt Heo) in Hx1.
  apply (rngl_archimedean_ub Har Hto).
  split; [ apply (rngl_0_lt_1 Hos Hc1 Hto) | easy ].
}
apply (rngl_ltb_ge_iff Hto) in Hx1.
destruct (rngl_eqb_dec (rngl_abs a) 1) as [Ha1| Ha1]. {
  apply (rngl_eqb_eq Heo) in Ha1.
  exists 1.
  rewrite Ha1; cbn.
  rewrite rngl_add_0_r.
  split; [ pauto | ].
  apply rngl_le_neq.
  split; [ apply (rngl_1_le_2 Hos Hto) | ].
  intros H12.
  apply (f_equal (λ b, rngl_sub b 1))%L in H12.
  rewrite (rngl_sub_diag Hos) in H12.
  rewrite (rngl_add_sub Hos) in H12.
  symmetry in H12; revert H12.
  apply (rngl_1_neq_0_iff), Hc1.
}
apply (rngl_eqb_neq Heo) in Ha1.
exists 0; cbn.
rewrite rngl_add_0_r.
split; [ apply (rngl_abs_nonneg Hop Hto) | ].
now apply rngl_le_neq.
Qed.

(* on the usefulness of rngl_ord_mul_le_compat_nonpos *)
Theorem rngl_ord_mul_le_compat_nonneg_mul_le_compat_nonpos :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  (∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L).
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hca Hdb.
destruct Hca as (Hca, Haz).
destruct Hdb as (Hdb, Hbz).
apply (rngl_opp_le_compat Hop Hor) in Hca, Haz, Hdb, Hbz.
rewrite (rngl_opp_0 Hop) in Haz, Hbz.
assert (H3 : (0 ≤ - a ≤ - c)%L) by easy.
assert (H4 : (0 ≤ - b ≤ - d)%L) by easy.
rewrite <- (rngl_mul_opp_opp Hop a).
rewrite <- (rngl_mul_opp_opp Hop c).
now apply (rngl_mul_le_compat_nonneg Hor).
Qed.

End a.
