(** * RealLike

Specific properties of real numbers: existence of nth roots.
*)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8.

Require Import Core.

Class real_like_prop T {ro : ring_like_op T} {rp : ring_like_prop T} :=
  { rl_nth_root : nat → T → T;
    rl_nth_root_pow : ∀ n a, (0 ≤ a → rl_nth_root n a ^ n = a)%L;
    rl_nth_root_mul :
      ∀ n a b, (0 ≤ a)%L → (0 ≤ b)%L →
      (rl_nth_root n (a * b) = rl_nth_root n a * rl_nth_root n b)%L;
    rl_nth_root_inv :
      ∀ n a, (0 < a → rl_nth_root n a⁻¹ = (rl_nth_root n a)⁻¹)%L;
    rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ rl_nth_root 2 a)%L }.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition rl_sqrt a := rl_nth_root 2 a.

End a.

Arguments rl_sqrt {T ro rp rl} a%_L.
Notation "'√' a" := (rl_sqrt a) (at level 2, format "√ a").

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem rngl_squ_sqrt :
  rngl_has_1 T = true →
  ∀ a, (0 ≤ a)%L → rngl_squ (√a) = a.
Proof.
intros Hon *.
specialize (rl_nth_root_pow 2 a) as H1.
cbn in H1.
rewrite (rngl_mul_1_r Hon) in H1.
now apply H1.
Qed.

Theorem rngl_abs_sqrt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a)%L → rngl_abs (√a) = (√a)%L.
Proof.
intros Hop Hor.
intros * Haz.
progress unfold rngl_abs.
remember (√a ≤? 0)%L as az eqn:Halz.
symmetry in Halz.
destruct az; [ | easy ].
apply rngl_leb_le in Halz.
apply rl_sqrt_nonneg in Haz.
apply rngl_le_antisymm in Haz; [ | easy | easy ].
progress unfold rl_sqrt.
rewrite Haz.
apply (rngl_opp_0 Hop).
Qed.

Theorem rl_sqrt_mul :
  ∀ a b,
  (0 ≤ a)%L
  → (0 ≤ b)%L
  → rl_sqrt (a * b)%L = (rl_sqrt a * rl_sqrt b)%L.
Proof.
intros * Ha Hb.
progress unfold rl_sqrt.
now rewrite rl_nth_root_mul.
Qed.

Theorem rl_sqrt_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (√(a / b) = √a / √b)%L.
Proof.
intros Hon Hop Hiv Hor * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
rewrite rl_sqrt_mul; [ | easy | ]. 2: {
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_inv_pos Hon Hop Hiv Hor).
}
f_equal.
now apply rl_nth_root_inv.
Qed.

Theorem rl_sqrt_squ :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (√a²)%L = rngl_abs a.
Proof.
intros Hon Hop Hor *.
progress unfold rngl_squ.
progress unfold rngl_abs.
progress unfold rl_sqrt.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Haz.
  rewrite <- (rngl_mul_opp_opp Hop).
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite (rngl_squ_pow_2 Hon).
  now apply rl_nth_root_pow.
} {
  apply (rngl_leb_gt_iff Hor) in Haz.
  apply (rngl_lt_le_incl Hor) in Haz.
  rewrite rl_nth_root_mul; [ | easy | easy ].
  rewrite fold_rngl_squ.
  rewrite (rngl_squ_pow_2 Hon).
  now apply rl_nth_root_pow.
}
Qed.

Theorem rl_sqrt_0 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_pdiv T)%bool = true →
  rl_sqrt 0%L = 0%L.
Proof.
intros Hon Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rl_nth_root_pow 2 0%L (rngl_le_refl Hor _)) as H1.
rewrite <- (rngl_squ_0 Hos) in H1 at 2.
rewrite <- (rngl_squ_pow_2 Hon) in H1.
apply (eq_rngl_squ_rngl_abs Hop Hor Hii) in H1. 2: {
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_mul_0_r Hos).
}
rewrite (rngl_abs_0 Hop) in H1.
rewrite (rngl_abs_nonneg_eq Hop Hor) in H1; [ easy | ].
apply rl_sqrt_nonneg, (rngl_le_refl Hor).
Qed.

Theorem eq_rl_sqrt_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  ∀ a, (0 ≤ a)%L → rl_sqrt a = 0%L → a = 0%L.
Proof.
intros Hon Hos * Hza Ha.
apply (f_equal rngl_squ) in Ha.
rewrite (rngl_squ_sqrt Hon) in Ha; [ | easy ].
progress unfold rngl_squ in Ha.
now rewrite (rngl_mul_0_l Hos) in Ha.
Qed.

Definition rl_modl x y := (√(x² + y²))%L.

Theorem fold_rl_modl : ∀ x y, √(x² + y²) = rl_modl x y.
Proof. easy. Qed.

Theorem rl_modl_add_le :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (rl_modl (a + c) (b + d) ≤ rl_modl a b + rl_modl c d)%L.
Proof.
intros Hic Hon Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
progress unfold rl_modl.
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_0_add Hos Hor). {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hos Hor).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hos Hor).
  }
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (√_))%L. 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hos Hor).
}
apply (rngl_squ_le_abs_le Hon Hop Hiq Hor).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
rewrite (rngl_squ_add Hic Hon (√_))%L.
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
apply (rngl_le_sub_le_add_r Hop Hor).
apply -> (rngl_le_sub_le_add_l Hop Hor).
do 2 rewrite (rngl_squ_add Hic Hon)%L.
rewrite rngl_add_assoc.
rewrite (rngl_sub_add_distr Hos _ c²)%L.
rewrite (rngl_sub_sub_swap Hop _ c²)%L.
rewrite (rngl_add_sub Hos).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite rngl_add_assoc.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_sub_swap Hop).
rewrite rngl_add_add_swap.
rewrite (rngl_add_sub Hos).
rewrite <- rngl_add_assoc.
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
do 3 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  apply (rngl_0_le_2 Hon Hos Hor).
}
eapply (rngl_le_trans Hor); [ apply (rngl_le_abs_diag Hop Hor) | ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hos Hor).
  } {
    apply rl_sqrt_nonneg.
    apply (rngl_add_squ_nonneg Hos Hor).
  }
}
apply (rngl_squ_le_abs_le Hon Hop Hiq Hor).
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
rewrite (rngl_squ_sqrt Hon). 2: {
  apply (rngl_add_squ_nonneg Hos Hor).
}
rewrite (Brahmagupta_Fibonacci_identity_2 Hic Hon Hop).
apply (rngl_le_add_r Hor).
apply (rngl_squ_nonneg Hos Hor).
Qed.

Theorem euclidean_distance_triangular :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ x1 y1 x2 y2 x3 y3,
  (rl_modl (x3 - x1) (y3 - y1)
   ≤ rl_modl (x2 - x1) (y2 - y1) + rl_modl (x3 - x2) (y3 - y2))%L.
Proof.
intros Hic Hon Hop Hiv Hor *.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
progress unfold rl_modl.
rewrite (rngl_add_comm (√((x2 - x1)² + (y2 - y1)²)))%L.
replace (x3 - x1)%L with ((x3 - x2) + (x2 - x1))%L. 2: {
  rewrite (rngl_add_sub_assoc Hop).
  now rewrite (rngl_sub_add Hop).
}
replace (y3 - y1)%L with ((y3 - y2) + (y2 - y1))%L. 2: {
  rewrite (rngl_add_sub_assoc Hop).
  now rewrite (rngl_sub_add Hop).
}
apply (rl_modl_add_le Hic Hon Hop Hiv Hor).
Qed.

Theorem rl_sqrt_le_rl_sqrt :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b,
  (0 ≤ a)%L
  → (a ≤ b)%L
  → (√ a ≤ √ b)%L.
Proof.
intros Hon Hop Hiq Hor.
intros * Ha Hab.
apply (rngl_nlt_ge_iff Hor).
intros H1.
specialize (rngl_mul_lt_mono_nonneg Hon Hop Hiq Hor) as H2.
specialize (H2 (√b) (√a) (√b) (√a))%L.
assert (H : (0 ≤ √b < √a)%L). {
  split; [ | easy ].
  apply rl_sqrt_nonneg.
  now apply (rngl_le_trans Hor _ a).
}
specialize (H2 H H).
do 2 rewrite fold_rngl_squ in H2.
rewrite (rngl_squ_sqrt Hon) in H2. 2: {
  now apply (rngl_le_trans Hor _ a).
}
rewrite (rngl_squ_sqrt Hon) in H2; [ | easy ].
now apply rngl_nle_gt in Hab.
Qed.

Theorem rl_sqrt_lt_rl_sqrt :
  rngl_has_1 T = true →
  rngl_is_ordered T = true →
  ∀ a b,
  (0 ≤ a)%L
  → (a < b)%L
  → (√ a < √ b)%L.
Proof.
intros Hon Hor * Ha Hab.
apply (rngl_nle_gt_iff Hor).
intros H1.
specialize (rngl_mul_le_compat_nonneg Hor) as H2.
specialize (H2 (√b) (√b) (√a) (√a))%L.
assert (H : (0 ≤ √b ≤ √a)%L). {
  split; [ | easy ].
  apply rl_sqrt_nonneg.
  apply (rngl_le_trans Hor _ a); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
specialize (H2 H H).
do 2 rewrite fold_rngl_squ in H2.
rewrite (rngl_squ_sqrt Hon) in H2. 2: {
  apply (rngl_le_trans Hor _ a); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
rewrite (rngl_squ_sqrt Hon) in H2; [ | easy ].
now apply rngl_nle_gt in Hab.
Qed.

Theorem rl_sqrt_pos :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → (0 < √a)%L.
Proof.
intros Hon Hos Hor.
intros a Ha.
apply (rngl_le_neq Hor).
split. {
  apply rl_sqrt_nonneg.
  now apply (rngl_lt_le_incl Hor).
}
intros H; symmetry in H.
apply (eq_rl_sqrt_0 Hon Hos) in H; [ | now apply (rngl_lt_le_incl Hor) ].
subst a.
now apply (rngl_lt_irrefl Hor) in Ha.
Qed.

Theorem rl_sqrt_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  rl_sqrt 1%L = 1%L.
Proof.
intros Hon Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_or_pdiv_r Hon Hiq) as Hii.
specialize (rngl_0_le_1 Hon Hos Hor) as Hz1.
progress unfold rl_sqrt.
specialize (rl_nth_root_pow 2 1%L Hz1) as H1.
rewrite <- (rngl_squ_1 Hon) in H1 at 2.
rewrite <- (rngl_squ_pow_2 Hon) in H1.
apply (eq_rngl_squ_rngl_abs Hop Hor Hii) in H1. 2: {
  rewrite (rngl_mul_1_l Hon).
  apply (rngl_mul_1_r Hon).
}
rewrite (rngl_abs_nonneg_eq Hop Hor) in H1. 2: {
  now apply rl_sqrt_nonneg.
}
now rewrite (rngl_abs_1 Hon Hos Hor) in H1.
Qed.

End a.

Arguments rl_modl {T ro rp rl} (x y)%_L.
