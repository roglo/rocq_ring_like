(** * Div_with_order

Theorems about inverse and division, in the case when order
relation exists.

Division can be either:
- multiplication by the inverse ([ab⁻¹]) or
- partial division (with the property [ab/b=a]).

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

Require Import Utf8 Structures Order Add Mul Div.
Require Import Add_with_order Mul_with_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_inv_pos :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (0 < a → 0 < a⁻¹)%L.
Proof.
intros * Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hza.
assert (Haz : a ≠ 0%L). {
  intros H; subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
specialize (rngl_inv_neq_0 Hos Hiv) as H1.
destruct (rngl_leb_dec 0 a⁻¹)%L as [H2| H2]. {
  apply rngl_leb_le in H2.
  apply (rngl_le_neq Hto).
  split; [ easy | ].
  intros H; symmetry in H; revert H.
  now apply H1.
}
apply rngl_leb_nle in H2.
apply (rngl_not_le Hto) in H2.
destruct H2 as (H2, H3).
specialize (rngl_mul_nonneg_nonpos Hop Hto) as H4.
assert (H : (0 ≤ a)%L) by now apply (rngl_le_neq Hto) in Hza.
specialize (H4 _ _ H H3); clear H.
rewrite (rngl_mul_inv_diag_r Hiv a Haz) in H4.
specialize (rngl_0_le_1 Hos Hto) as H5.
specialize (rngl_le_antisymm Hor _ _ H4 H5) as H6.
clear H4 H5.
apply (rngl_1_eq_0_iff Hos) in H6.
specialize (rngl_characteristic_1 Hos H6) as H4.
exfalso; apply Haz, H4.
Qed.

Theorem rngl_inv_neg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (a < 0 → a⁻¹ < 0)%L.
Proof.
intros * Hop Hiv Hto.
intros * Hza.
specialize (rngl_inv_pos Hop Hiv Hto) as H2.
specialize (H2 (- a))%L.
apply (rngl_opp_lt_compat Hop Hto).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_opp_inv Hop Hiv); [ | now apply rngl_le_neq ].
apply H2.
apply (rngl_opp_lt_compat Hop Hto) in Hza.
now rewrite (rngl_opp_0 Hop) in Hza.
Qed.

Theorem rngl_div_le_1 :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (b ≠ 0 → 0 ≤ a ≤ b → a / b ≤ 1)%L.
Proof.
intros * Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hbz (Hza, Hab).
unfold rngl_div.
rewrite Hiv.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 a b⁻¹ b b⁻¹)%L.
assert (H : (0 ≤ a ≤ b)%L) by easy.
specialize (H1 H); clear H.
assert (H : (0 ≤ b⁻¹ ≤ b⁻¹)%L). {
  split; [ | apply (rngl_le_refl Hor) ].
  apply (rngl_lt_le_incl Hto).
  apply (rngl_inv_pos Hop Hiv Hto).
  apply (rngl_le_neq Hto).
  split; [ | congruence ].
  now apply (rngl_le_trans Hor _ a).
}
specialize (H1 H); clear H.
now rewrite (rngl_mul_inv_diag_r Hiv) in H1.
Qed.

Theorem rngl_one_sub_half :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  (1 - 2⁻¹ = 2⁻¹)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  now rewrite (H1 (_ - _))%L, H1.
}
assert (Hc2 : (2 ≠ 0)%L). {
  specialize (rngl_0_lt_2 Hos Hc1 Hto) as H2.
  intros H; rewrite H in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
apply (rngl_mul_cancel_r Hi1) with (c := 2%L); [ easy | ].
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_inv_diag_l Hiv); [ | easy ].
rewrite rngl_mul_1_l.
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_integral :
  rngl_has_opp_or_psub T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_or_pdiv T && rngl_has_eq_dec_or_order T)%bool = true →
  ∀ a b, (a * b = 0)%L → a = 0%L ∨ b = 0%L.
Proof.
intros Hmo Hdo * Hab.
remember (rngl_is_integral_domain T) as id eqn:Hid.
symmetry in Hid.
destruct id. {
  apply rngl_opt_integral in Hab.
  destruct Hab as [Hab| [Hab| Hab]]; [ now left | now right | ].
  destruct Hab as [Hab| Hab]. {
    progress unfold rngl_is_zero_divisor in Hab.
    progress unfold rngl_is_integral_domain in Hid.
    now destruct (rngl_opt_is_zero_divisor T).
  } {
    progress unfold rngl_is_zero_divisor in Hab.
    progress unfold rngl_is_integral_domain in Hid.
    now destruct (rngl_opt_is_zero_divisor T).
  }
}
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  apply Bool.andb_true_iff in Hdo.
  destruct Hdo as (Hiq, Heo).
  cbn.
  assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%L). {
    now rewrite <- rngl_mul_assoc, Hab.
  }
  destruct (rngl_eqb_dec a 0) as [Haz| Haz]; [ left | right ].
  now apply (rngl_eqb_eq Heo) in Haz.
  apply (rngl_eqb_neq Heo) in Haz.
  rewrite rngl_mul_inv_diag_l in H; [ | easy | easy ].
  rewrite rngl_mul_1_l in H; rewrite H.
  apply (rngl_mul_0_r Hmo).
} {
  apply andb_prop in Hdo.
  destruct Hdo as (Hdi, Heo).
  specialize rngl_mul_div as H1.
  rewrite Hdi in H1.
  specialize (H1 eq_refl).
  destruct (rngl_eqb_dec b 0) as [Hbz| Hbz]; [ right | left ].
  now apply (rngl_eqb_eq Heo) in Hbz.
  apply (rngl_eqb_neq Heo) in Hbz.
  specialize (H1 a b Hbz) as H4.
  rewrite Hab in H4.
  rewrite <- H4.
  now apply rngl_div_0_l.
}
Qed.

Theorem rngl_abs_div :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ x y, y ≠ 0%L → rngl_abs (x / y)%L = (rngl_abs x / rngl_abs y)%L.
Proof.
intros * Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hyz.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
progress unfold rngl_abs.
remember (x ≤? _)%L as xz eqn:Hx; symmetry in Hx.
remember (y ≤? _)%L as yz eqn:Hy; symmetry in Hy.
remember (x / y ≤? _)%L as xyz eqn:Hxy; symmetry in Hxy.
destruct xz. {
  apply rngl_leb_le in Hx.
  destruct yz. {
    apply rngl_leb_le in Hy.
    destruct xyz. {
      apply rngl_leb_le in Hxy.
      progress unfold rngl_div in Hxy.
      rewrite Hiv in Hxy.
      specialize (rngl_mul_le_compat_nonpos Hor) as H1.
      specialize (H1 0 0 x y⁻¹)%L.
      assert (H : (x ≤ 0 ≤ 0)%L). {
        split; [ easy | apply (rngl_le_refl Hor) ].
      }
      specialize (H1 H); clear H.
      assert (H : (y⁻¹ ≤ 0 ≤ 0)%L). {
        split; [ | apply (rngl_le_refl Hor) ].
        apply (rngl_opp_le_compat Hop Hto).
        rewrite (rngl_opp_0 Hop).
        rewrite (rngl_opp_inv Hop Hiv _ Hyz).
        apply (rngl_opp_le_compat Hop Hto) in Hy.
        rewrite (rngl_opp_0 Hop) in Hy.
        apply (rngl_lt_le_incl Hto).
        apply (rngl_inv_pos Hop Hiv Hto).
        apply (rngl_le_neq Hto).
        split; [ easy | ].
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        rewrite (rngl_opp_involutive Hop) in H.
        now symmetry in H.
      }
      specialize (H1 H); clear H.
      rewrite (rngl_mul_0_l Hos) in H1.
      specialize (rngl_le_antisymm Hor _ _ Hxy H1) as H2.
      apply (rngl_integral Hos) in H2. 2: {
        rewrite Hi1, Heo; cbn.
        now destruct rngl_is_integral_domain.
      }
      destruct H2 as [H2| H2]. {
        subst x.
        rewrite (rngl_div_0_l Hos Hi1 _ Hyz).
        rewrite (rngl_opp_0 Hop).
        symmetry.
        apply (rngl_div_0_l Hos Hi1).
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      } {
        exfalso; revert H2.
        now apply (rngl_inv_neq_0 Hos Hiv).
      }
    } {
      unfold rngl_div.
      rewrite Hiv.
      rewrite (rngl_mul_opp_l Hop).
      rewrite <- (rngl_mul_opp_r Hop).
      f_equal.
      rewrite (rngl_opp_inv Hop Hiv). 2: {
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      }
      now rewrite (rngl_opp_involutive Hop).
    }
  } {
    apply (rngl_leb_gt_iff Hto) in Hy.
    destruct xyz. {
      apply rngl_leb_le in Hxy.
      progress unfold rngl_div.
      rewrite Hiv.
      now rewrite (rngl_mul_opp_l Hop).
    } {
      apply rngl_leb_nle in Hxy.
      exfalso; apply Hxy; clear Hxy.
      progress unfold rngl_div.
      rewrite Hiv.
      apply (rngl_mul_nonpos_nonneg Hop Hto _ _ Hx).
      apply (rngl_lt_le_incl Hto).
      now apply (rngl_inv_pos Hop Hiv Hto).
    }
  }
}
apply (rngl_leb_gt_iff Hto) in Hx.
destruct yz. {
  apply rngl_leb_le in Hy.
  destruct xyz. {
    apply rngl_leb_le in Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite <- (rngl_mul_opp_r Hop).
    f_equal.
    now apply (rngl_opp_inv Hop Hiv).
  } {
    apply rngl_leb_nle in Hxy.
    exfalso; apply Hxy; clear Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_lt_le_incl Hto) in Hx.
    apply (rngl_mul_nonneg_nonpos Hop Hto _ _ Hx).
    apply (rngl_lt_le_incl Hto).
    apply (rngl_inv_neg Hop Hiv Hto).
    apply (rngl_le_neq Hto).
    split; [ easy | congruence ].
  }
}
apply rngl_leb_nle in Hy.
apply (rngl_not_le Hto) in Hy.
destruct Hy as (_, Hy).
destruct xyz; [ | easy ].
apply rngl_leb_le in Hxy.
unfold rngl_div in Hxy.
rewrite Hiv in Hxy.
assert (Hzy : (0 < y)%L). {
  apply (rngl_le_neq Hto).
  split; [ easy | congruence ].
}
specialize (rngl_inv_pos Hop Hiv Hto _ Hzy) as Hy'.
apply (rngl_lt_le_incl Hto) in Hy'.
generalize Hx; intros Hx'.
apply (rngl_lt_le_incl Hto) in Hx'.
specialize (rngl_mul_nonneg_nonneg Hos Hor _ _ Hx' Hy') as H1.
specialize (rngl_le_antisymm Hor _ _ Hxy H1) as H2.
apply (rngl_integral Hos) in H2. 2: {
  rewrite Hi1, Heo.
  now destruct rngl_is_integral_domain.
}
destruct H2 as [H2| H2]. {
  now subst x; apply (rngl_lt_irrefl Hor) in Hx.
} {
  exfalso; revert H2.
  now apply (rngl_inv_neq_0 Hos Hiv).
}
Qed.

Theorem rngl_mul_pos_pos :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a * b)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Haz Hbz.
...
apply (rngl_le_neq Hto) in Haz.
apply (rngl_le_neq Hto) in Hbz.
apply (rngl_le_neq Hto).
destruct Haz as (Haz, Hza).
destruct Hbz as (Hbz, Hzb).
split; [ now apply (rngl_mul_nonneg_nonneg Hos Hor) | ].
apply not_eq_sym in Hza, Hzb.
apply not_eq_sym.
intros Hab.
now apply (rngl_eq_mul_0_l Hos Hiq) in Hab.
Qed.

Theorem rngl_mul_pos_cancel_r :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b → 0 < a * b ↔ 0 < a)%L.
Proof.
intros Hop Hiq Hor * Ha.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Hb. {
  apply (rngl_le_neq Hto) in Ha.
  apply (rngl_le_neq Hto) in Hb.
  apply (rngl_le_neq Hto).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply rngl_nle_gt in Habz.
      apply (rngl_nlt_ge_iff Hto).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hto).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
}
Qed.

Theorem rngl_mul_pos_cancel_l :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a → 0 < a * b ↔ 0 < b)%L.
Proof.
intros Hop Hiq Hor * Ha.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Hb. {
  apply (rngl_le_neq Hto) in Ha.
  apply (rngl_le_neq Hto) in Hb.
  apply (rngl_le_neq Hto).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply rngl_nle_gt in Habz.
      apply (rngl_nlt_ge_iff Hto).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hto).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
}
Qed.

(*************)

Theorem rngl_mul_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (0 < a)%L → (b ≤ c)%L ↔ (a * b ≤ a * c)%L.
Proof.
intros Hop Hiq Hor * Hc.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Hbc. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
} {
  apply (rngl_le_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hbc.
  apply rngl_nlt_ge in Hbc.
  apply (rngl_nlt_ge_iff Hto).
  intros H1; apply Hbc; clear Hbc.
  rewrite <- (rngl_mul_0_r Hos a).
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_opp_sub_distr Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_l :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (a * b < a * c)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hbc.
  apply rngl_nle_gt in Hbc.
  apply (rngl_nle_gt_iff Hto).
  intros H1; apply Hbc; clear Hbc.
  rewrite <- (rngl_mul_0_r Hos a).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_sub_0_l Hop).
  rewrite (rngl_opp_sub_distr Hop).
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    now apply (rngl_lt_le_incl Hto).
  }
  now apply (rngl_le_0_sub Hop Hor).
}
Qed.

(*************)

Theorem rngl_mul_lt_mono_pos_r :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b * a < c * a)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hop Hiq Hor); [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hbc.
  apply (rngl_mul_pos_cancel_r Hop Hiq Hor) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_le_mono_pos_r :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (a * c ≤ b * c)%L.
Proof.
intros Hop Hiq Hor * Hc.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hto).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hab.
  apply rngl_nlt_ge in Hab.
  apply (rngl_nlt_ge_iff Hto).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (0 * c)%L by apply (rngl_mul_0_l Hos).
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor); [ easy | ].
  apply (rngl_nle_gt_iff Hto).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply rngl_nlt_ge in H2.
}
Qed.

Theorem rngl_div_lt_mono_pos_r :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b / a < c / a)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hza.
  rewrite (H1 a) in Hza.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
intros * Hza.
split; intros Hbc. {
  progress unfold rngl_div at 1 2.
  rewrite Hiv.
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor); [ | easy ].
  now apply (rngl_inv_pos Hop Hiv Hor).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor a) in Hbc; [ | easy ].
  rewrite (rngl_div_mul Hiv) in Hbc. 2: {
    intros H; subst a.
    now apply (rngl_lt_irrefl Hor) in Hza.
  }
  rewrite (rngl_div_mul Hiv) in Hbc. 2: {
    intros H; subst a.
    now apply (rngl_lt_irrefl Hor) in Hza.
  }
  easy.
}
Qed.

Theorem rngl_div_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < a)%L → (b⁻¹ ≤ c⁻¹ ↔ a / b ≤ a / c)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Haz.
progress unfold rngl_div.
rewrite Hiv.
now apply (rngl_mul_le_mono_pos_l Hop Hiq Hor).
Qed.

Theorem rngl_div_le_mono_pos_r :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c)%L → (a ≤ b ↔ a / c ≤ b / c)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hcz.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_le_mono_pos_r Hop Hiq Hor).
now apply (rngl_inv_pos Hop Hiv Hor).
Qed.

Theorem rngl_lt_neq :
  rngl_is_ordered T = true →
  ∀ a b, (a < b)%L → a ≠ b.
Proof.
intros Hor.
intros * Hab.
intros H; subst b.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_le_inv_inv :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (a⁻¹ ≤ b⁻¹)%L ↔ (b ≤ a)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Haz Hbz.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor a) in Hab. 2: {
    now apply (rngl_lt_le_incl Hto).
  }
  apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ b) in Hab. 2: {
    now apply (rngl_lt_le_incl Hto).
  }
  rewrite (rngl_mul_inv_diag_r Hiv) in Hab. 2: {
    now apply (rngl_lt_neq Hor) in Haz.
  }
  rewrite <- rngl_mul_assoc in Hab.
  rewrite (rngl_mul_inv_diag_l Hiv) in Hab. 2: {
    now apply (rngl_lt_neq Hor) in Hbz.
  }
  rewrite rngl_mul_1_l in Hab.
  rewrite rngl_mul_1_r in Hab.
  easy.
} {
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hor a); [ easy | ].
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hor _ _ b); [ easy | ].
  rewrite (rngl_mul_inv_diag_r Hiv). 2: {
    now apply (rngl_lt_neq Hor) in Haz.
  }
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_inv_diag_l Hiv). 2: {
    now apply (rngl_lt_neq Hor) in Hbz.
  }
  rewrite rngl_mul_1_l.
  rewrite rngl_mul_1_r.
  easy.
}
Qed.

Theorem rngl_div_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 < b → 0 ≤ a / b)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_mul_le_mono_pos_l Hop Hiq Hor b); [ easy | ].
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_psub_iff; left ].
rewrite (rngl_mul_inv_diag_r Hiv). {
  apply (rngl_0_le_1 Hos Hor).
}
apply (rngl_le_neq Hto) in Hb.
now apply not_eq_sym.
Qed.

Theorem rngl_div_pos :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a / b)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
now apply (rngl_inv_pos Hop Hiv Hor).
Qed.

Theorem rngl_le_div_l :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a ≤ b * c ↔ a / c ≤ b)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hor) with (c := c); [ easy | ].
  now rewrite (rngl_div_mul Hiv).
} {
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hor _ _ c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_l :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a < b * c ↔ a / c < b)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor c); [ easy | ].
  now rewrite (rngl_div_mul Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hiv) in Habq.
}
Qed.

Theorem rngl_le_div_r :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c ≤ b ↔ a ≤ b / c)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hor _ _ c); [ easy | ].
  now rewrite (rngl_div_mul Hiv).
} {
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hor _ _ c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_r :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c < b ↔ a < b / c)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor c); [ easy | ].
  now rewrite (rngl_div_mul Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hiv) in Habq.
}
Qed.

Theorem rngl_middle_sub_l :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (((a + b) / 2 - a) = (b - a) / 2)%L.
Proof.
intros Hop Hiv Hor *.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
progress unfold rngl_sub.
rewrite Hop.
rewrite <- rngl_add_assoc; f_equal.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_1_r a) at 2.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
f_equal.
rewrite <- (rngl_opp_involutive Hop (_ - _))%L.
f_equal.
rewrite (rngl_opp_sub_distr Hop).
apply (rngl_one_sub_half Hop Hiv Hor).
Qed.

Theorem rngl_middle_sub_r :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b - (a + b) / 2 = (b - a) / 2)%L.
Proof.
intros Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_sub_add_distr Hos).
f_equal.
rewrite (rngl_sub_mul_r_diag_l Hop).
f_equal.
apply (rngl_one_sub_half Hop Hiv Hor).
Qed.

Theorem rngl_abs_le_ε :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a,
  (∀ ε, (0 < ε)%L → (rngl_abs a ≤ ε)%L)
  → a = 0%L.
Proof.
intros Hop Hiv Hor * H1.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  apply (rngl_characteristic_1 Hos Hc1).
}
destruct (rngl_ltb_dec a 0%L) as [H12| H12]. {
  apply rngl_ltb_lt in H12.
  specialize (H1 (- a / 2))%L.
  assert (H : (0 < - a / 2)%L). {
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_pos_pos Hop Hiq Hor). {
      rewrite <- (rngl_opp_0 Hop).
      now apply -> (rngl_opp_lt_compat Hop Hor).
    }
    apply (rngl_inv_pos Hop Hiv Hor).
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  specialize (H1 H); clear H.
  exfalso.
  apply rngl_nlt_ge in H1; apply H1; clear H1.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    now apply (rngl_lt_le_incl Hto).
  }
  apply (rngl_lt_div_l Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  remember (_ * _)%L as x.
  rewrite <- (rngl_mul_1_r (- a))%L.
  subst x.
  apply (rngl_mul_lt_mono_pos_l Hop Hiq Hor). 2: {
    apply (rngl_lt_add_r Hos Hor).
    apply (rngl_0_lt_1 Hos Hc1 Hor).
  }
  rewrite <- (rngl_opp_0 Hop).
  now apply -> (rngl_opp_lt_compat Hop Hor).
}
destruct (rngl_ltb_dec 0 a) as [H21| H21]. {
  apply rngl_ltb_lt in H21.
  specialize (H1 (a / 2))%L.
  assert (H : (0 < a / 2)%L). {
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
    apply (rngl_inv_pos Hop Hiv Hor).
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  specialize (H1 H); clear H.
  exfalso.
  apply rngl_nlt_ge in H1; apply H1.
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_lt_le_incl Hto).
  }
  apply (rngl_lt_div_l Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hor).
  }
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  now apply (rngl_lt_add_r Hos Hor).
}
apply (rngl_ltb_ge_iff Hor) in H12, H21.
now apply (rngl_le_antisymm Hor).
Qed.

Theorem rngl_mul_pos_neg :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < a → b < 0 → a * b < 0)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hza Hbz.
apply (rngl_le_neq Hto).
split. {
  apply (rngl_mul_nonneg_nonpos Hop Hor).
  now apply (rngl_lt_le_incl Hto).
  now apply (rngl_lt_le_incl Hto).
}
intros H.
apply (rngl_eq_mul_0_l Hos Hiq) in H. {
  subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
} {
  intros H1; subst b.
  now apply (rngl_lt_irrefl Hor) in Hbz.
}
Qed.

Theorem eq_rngl_add_square_0 :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (a * a + b * b = 0)%L → a = 0%L ∧ b = 0%L.
Proof.
intros Hop Hiq Hor.
assert (Hio :
  (rngl_is_integral_domain T ||
    rngl_has_inv_or_pdiv T &&
      rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  apply Bool.andb_true_iff.
  split; [ easy | ].
  apply (rngl_has_eq_dec_or_is_ordered_r Hor).
}
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hab.
apply (rngl_eq_add_0 Hos Hor) in Hab; cycle 1. {
  apply (rngl_mul_diag_nonneg Hos Hor).
} {
  apply (rngl_mul_diag_nonneg Hos Hor).
}
destruct Hab as (Ha, Hb).
split. {
  now apply (rngl_integral Hos Hio) in Ha; destruct Ha.
} {
  now apply (rngl_integral Hos Hio) in Hb; destruct Hb.
}
Qed.

Theorem rngl_abs_mul :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a * b) = rngl_abs a * rngl_abs b)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a * b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    rewrite (rngl_mul_opp_l Hop).
    apply rngl_leb_le in Haz.
    destruct bz; [ | easy ].
    rewrite (rngl_mul_opp_r Hop).
    apply rngl_leb_le in Hbz.
    specialize (rngl_mul_nonpos_nonpos Hos Hor _ _ Haz Hbz) as H1.
    apply (rngl_le_antisymm Hor _ _ Habz) in H1.
    rewrite H1.
    now do 2 rewrite (rngl_opp_0 Hop).
  }
  apply (rngl_leb_gt_iff Hto) in Haz.
  destruct bz; [ now rewrite (rngl_mul_opp_r Hop) | ].
  apply (rngl_leb_gt_iff Hto) in Hbz.
  apply rngl_nlt_ge in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_le_neq Hto).
  split. {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    now apply (rngl_lt_le_incl Hto).
    now apply (rngl_lt_le_incl Hto).
  }
  apply not_eq_sym.
  intros H1.
  apply (rngl_eq_mul_0_l Hos Hiq) in H1. {
    now subst a; apply (rngl_lt_irrefl Hor) in Haz.
  } {
    intros H; subst b.
    now apply (rngl_lt_irrefl Hor) in Hbz.
  }
}
apply (rngl_leb_gt_iff Hto) in Habz.
destruct az. {
  rewrite (rngl_mul_opp_l Hop).
  apply rngl_leb_le in Haz.
  destruct bz. {
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
  apply (rngl_leb_gt_iff Hto) in Hbz.
  apply (rngl_le_neq Hto) in Hbz.
  destruct Hbz as (Hbz, Hzb).
  specialize (rngl_mul_nonpos_nonneg Hop Hor _ _ Haz Hbz) as H1.
  now apply rngl_nlt_ge in H1.
}
apply (rngl_leb_gt_iff Hto) in Haz.
destruct bz; [ | easy ].
apply rngl_leb_le in Hbz.
apply (rngl_le_neq Hto) in Haz.
destruct Haz as (Haz, Hza).
specialize (rngl_mul_nonneg_nonpos Hop Hor _ _ Haz Hbz) as H1.
now apply rngl_nlt_ge in H1.
Qed.

Theorem eq_rngl_squ_rngl_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_or_pdiv T)%bool = true →
  ∀ a b,
  (a * b = b * a)%L
  → (a² = b²)%L
  → rngl_abs a = rngl_abs b.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Habc Hab.
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop), Habc in Hab.
rewrite (rngl_add_sub Hos) in Hab.
assert (Hio :
  (rngl_is_integral_domain T ||
   rngl_has_inv_or_pdiv T && rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff in Hii.
  apply Bool.orb_true_iff.
  destruct Hii as [Hii| Hii]; [ now left | right ].
  rewrite Hii.
  now apply (rngl_has_eq_dec_or_is_ordered_r).
}
apply (rngl_integral Hos Hio) in Hab.
destruct Hab as [Hab| Hab]. {
  apply (rngl_add_move_0_r Hop) in Hab.
  subst a.
  apply (rngl_abs_opp Hop Hor).
} {
  apply -> (rngl_sub_move_0_r Hop) in Hab.
  now subst a.
}
Qed.

Theorem rngl_mul_neg_neg :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (a < 0)%L → (b < 0)%L → (0 < a * b)%L.
Proof.
intros Hop Hiq Hor.
intros * Haz Hbz.
rewrite <- (rngl_mul_opp_opp Hop).
apply (rngl_mul_pos_pos Hop Hiq Hor).
now apply (rngl_opp_pos_neg Hop Hor).
now apply (rngl_opp_pos_neg Hop Hor).
Qed.

Theorem rngl_mul_lt_mono_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (0 ≤ a < b → 0 ≤ c < d → a * c < b * d)%L.
Proof.
intros Hop Hiq Hor * (Haz, Hab) (Hcz, Hcd).
apply (rngl_le_lt_trans Hto _ (b * c)%L). {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hto).
}
apply (rngl_mul_lt_mono_pos_l Hop Hiq Hor); [ | easy ].
now apply (rngl_le_lt_trans Hto _ a).
Qed.

Theorem rngl_mul_min_distr_l :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 ≤ a)%L → rngl_min (a * b)%L (a * c)%L = (a * rngl_min b c)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hza.
destruct (rngl_eqb_dec a 0%L) as [Haz| Haz]. {
  apply (rngl_eqb_eq Heo) in Haz.
  subst a.
  do 3 rewrite (rngl_mul_0_l Hos).
  apply (rngl_min_id Hor).
}
apply (rngl_eqb_neq Heo) in Haz.
assert (H : (0 < a)%L). {
  apply (rngl_le_neq Hto).
  split; [ easy | ].
  now apply not_eq_sym.
}
clear Hza Haz; rename H into Hza.
progress unfold rngl_min.
remember (_ * _ ≤? _ * _)%L as abc eqn:Habc.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Habc, Hbc.
destruct abc. {
  f_equal.
  destruct bc; [ easy | ].
  apply rngl_leb_le in Habc.
  apply (rngl_leb_gt_iff Hto) in Hbc.
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hor) in Habc; [ | easy ].
  now apply rngl_nle_gt in Hbc.
}
destruct bc; [ | easy ].
f_equal.
apply rngl_leb_le in Hbc.
apply (rngl_leb_gt_iff Hto) in Habc.
apply (rngl_mul_lt_mono_pos_l Hop Hiq Hor) in Habc; [ | easy ].
now apply rngl_nle_gt in Habc.
Qed.

Theorem rngl_square_le_simpl_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b → a * a ≤ b * b → a ≤ b)%L.
Proof.
intros Hop Hiq Hor * Hzb Hab.
destruct (rngl_leb_dec a 0%L) as [Haz| Haz]. {
  apply rngl_leb_le in Haz.
  now apply (rngl_le_trans Hor a 0%L b).
}
apply (rngl_leb_gt_iff Hto) in Haz.
apply (rngl_nle_gt_iff Hto) in Haz.
apply rngl_nlt_ge in Hab.
apply (rngl_nlt_ge_iff Hto).
intros Hba; apply Hab; clear Hab.
now apply (rngl_mul_lt_mono_nonneg Hop Hiq Hor).
Qed.

Theorem rngl_pow_pos_pos :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a n, (0 < a → 0 < a ^ n)%L.
Proof.
intros Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hza.
  rewrite H1 in Hza.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
intros * Hza.
induction n; cbn; [ apply (rngl_0_lt_1 Hos Hc1 Hor) | ].
now apply (rngl_mul_pos_pos Hop Hiq Hor).
Qed.

Theorem rngl_le_0_mul :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)%L.
Proof.
intros Hop Hiq Hor * Hab.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (rngl_leb_dec 0 a)%L as [Hza| Hza]. {
  apply rngl_leb_le in Hza.
  destruct (rngl_ltb_dec 0 a) as [Hlza| Hlza]. {
    apply rngl_ltb_lt in Hlza.
    rewrite <- (rngl_mul_0_r Hos a) in Hab.
    now left; apply (rngl_mul_le_mono_pos_l Hop Hiq Hor) in Hab.
  }
  apply (rngl_ltb_ge_iff Hor) in Hlza.
  apply (rngl_le_antisymm Hor) in Hza; [ | easy ].
  subst a.
  destruct (rngl_leb_dec 0 b)%L as [Hzb| Hzb]. {
    apply rngl_leb_le in Hzb.
    now left.
  }
  apply (rngl_leb_gt_iff Hto), (rngl_lt_le_incl Hto) in Hzb.
  now right.
} {
  apply (rngl_leb_gt_iff Hto) in Hza.
  right.
  rewrite <- (rngl_mul_0_l Hos b) in Hab.
  split; [ now apply (rngl_lt_le_incl Hto) | ].
  apply rngl_nle_gt in Hza.
  apply (rngl_nlt_ge_iff Hto).
  intros Hzb; apply Hza.
  now apply (rngl_mul_le_mono_pos_r Hop Hiq Hor) in Hab.
}
Qed.

Theorem rngl_abs_lt_squ_lt :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (a * b = b * a)%L → (rngl_abs a < rngl_abs b)%L → (a² < b²)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_int_dom_or_inv_or_pdiv_r Hiq) as Hii.
intros * Habc Hab.
apply (rngl_le_neq Hto).
split. {
  apply (rngl_abs_le_squ_le Hop Hor).
  now apply (rngl_lt_le_incl Hto).
}
intros H.
apply (eq_rngl_squ_rngl_abs Hop Hor Hii _ _ Habc) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_squ_le_abs_le :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a² ≤ b² → rngl_abs a ≤ rngl_abs b)%L.
Proof.
intros Hop Hiq Hor.
intros * Hab.
progress unfold rngl_squ in Hab.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hiq Hor) in Hab; [ easy | ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_le_compat Hop Hor).
  } {
    apply (rngl_leb_gt_iff Hto) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hiq Hor) in Hab; [ easy | ].
    now apply (rngl_lt_le_incl Hto).
  }
} {
  apply (rngl_leb_gt_iff Hto) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    now apply (rngl_square_le_simpl_nonneg Hop Hiq Hor) in Hab.
  } {
    apply (rngl_leb_gt_iff Hto) in Hbz.
    apply (rngl_lt_le_incl Hto) in Haz, Hbz.
    now apply (rngl_square_le_simpl_nonneg Hop Hiq Hor) in Hab.
  }
}
Qed.

Theorem rngl_squ_lt_abs_lt :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (a² < b²)%L → (rngl_abs a < rngl_abs b)%L.
Proof.
intros Hop Hiq Hor * Hab.
apply (rngl_le_neq Hto).
split. {
  apply (rngl_squ_le_abs_le Hop Hiq Hor).
  now apply (rngl_lt_le_incl Hto).
}
intros H.
apply (f_equal rngl_squ) in H.
do 2 rewrite (rngl_squ_abs Hop) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_squ_le_1_iff :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a, (a² ≤ 1)%L ↔ (-1 ≤ a ≤ 1)%L.
Proof.
intros Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Ha. {
  rewrite <- (rngl_squ_1) in Ha.
  apply (rngl_squ_le_abs_le Hop Hiq Hor) in Ha.
  rewrite (rngl_abs_1 Hos Hor) in Ha.
  now apply (rngl_abs_le Hop Hor).
} {
  rewrite <- (rngl_squ_1).
  apply (rngl_abs_le_squ_le Hop Hor).
  rewrite (rngl_abs_1 Hos Hor).
  now apply -> (rngl_abs_le Hop Hor).
}
Qed.

Theorem eq_rngl_squ_0 :
  rngl_has_opp_or_psub T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_or_pdiv T &&
     rngl_has_eq_dec_or_order T)%bool = true →
  ∀ a, (a² = 0 → a = 0)%L.
Proof.
intros Hos Hio * Ha.
apply (rngl_integral Hos Hio) in Ha.
now destruct Ha.
Qed.

Theorem rngl_le_squ_le :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a² ≤ b² → a ≤ b)%L.
Proof.
intros Hop Hiq Hor.
intros * Hza Hzb Hab.
rewrite <- (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
now apply (rngl_squ_le_abs_le Hop Hiq Hor).
Qed.

Theorem rngl_le_le_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → a ≤ b → a² ≤ b²)%L.
Proof.
intros Hop Hor.
intros * Hza Hab.
apply (rngl_abs_le_squ_le Hop Hor).
rewrite (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor b); [ easy | ].
now apply (rngl_le_trans Hor _ a).
Qed.

Theorem rngl_lt_squ_lt :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a² < b² → a < b)%L.
Proof.
intros Hop Hiq Hor.
intros * Hza Hzb Hab.
rewrite <- (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
now apply (rngl_squ_lt_abs_lt Hop Hiq Hor).
Qed.

Theorem rngl_lt_lt_squ :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a * b = b * a → 0 ≤ a → a < b → a² < b²)%L.
Proof.
intros Hop Hiq Hor.
intros * Habba Hza Hab.
apply (rngl_abs_lt_squ_lt Hop Hiq Hor _ _ Habba).
rewrite (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor b); [ easy | ].
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_lt_le_incl Hto) in Hab.
Qed.

Theorem rngl_squ_eq_cases :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec_or_order T = true →
  ∀ a b, (a * b = b * a → a² = b² → a = b ∨ a = -b)%L.
Proof.
intros Hop Hiv Heo * Habc Hab.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_or_pdiv T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  now rewrite Hi1.
}
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop), Habc in Hab.
rewrite (rngl_add_sub Hos) in Hab.
apply (rngl_integral Hos Hio) in Hab.
destruct Hab as [Hab| Hab]; [ right | left ]. {
  now apply (rngl_add_move_0_r Hop) in Hab.
} {
  now apply -> (rngl_sub_move_0_r Hop) in Hab.
}
Qed.

Theorem rngl_pow_div_pow :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ (a : T) m n,
  (a ≠ 0)%L
  → n ≤ m
  → (a ^ m / a ^ n = a ^ (m - n))%L.
Proof.
intros Hos Hiv.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
intros * Haz Hnm.
revert m Hnm.
induction n; intros. {
  rewrite (rngl_div_1_r Hiq); [ | now left ].
  now rewrite Nat.sub_0_r.
}
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hnm.
do 2 rewrite (rngl_pow_succ_l).
rewrite <- (rngl_div_div Hos Hiv); [ | easy | ]. 2: {
  now apply (rngl_pow_neq_0 Hos Hiq).
}
rewrite (rngl_mul_div Hi1); [ | easy ].
now apply IHn.
Qed.

Theorem rngl_squ_inv' :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec_or_order T = true →
  ∀ a, a ≠ 0%L ∨ (0⁻¹)² = 0⁻¹ → (a⁻¹)² = (a²)⁻¹.
Proof.
intros Hos Hiv Heo * Hzi.
destruct (rngl_eqb_dec a 0) as [Haz| Haz]. {
  apply (rngl_eqb_eq Heo) in Haz.
  destruct Hzi as [| Hzi]; [ easy | ].
  now subst a; rewrite (rngl_squ_0 Hos).
}
apply (rngl_eqb_neq Heo) in Haz.
progress unfold rngl_squ.
now rewrite (rngl_inv_mul_distr Hos Hiv).
Qed.

Theorem rngl_squ_div' :
  rngl_mul_is_comm T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec_or_order T = true →
  ∀ a b, b ≠ 0%L ∨ (0⁻¹)² = 0⁻¹ → (a / b)²%L = (a² / b²)%L.
Proof.
intros Hic Hos Hiv Hed * Hbz.
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_squ_mul Hic).
progress f_equal.
now apply (rngl_squ_inv' Hos Hiv Hed).
Qed.

End a.

Arguments rngl_div_le_mono_pos_l {T ro rp} Hop Hiv Hor (a b c)%_L.
Arguments rngl_div_le_mono_pos_r {T ro rp} Hop Hiv Hor (a b c)%_L.
Arguments rngl_middle_sub_r {T ro rp} Hop Hiv Hor (a b)%_L.
Arguments rngl_mul_le_mono_pos_l {T ro rp} Hop Hiq Hor (a b c)%_L.
Arguments rngl_mul_le_mono_pos_r {T ro rp} Hop Hiq Hor (a b c)%_L.
Arguments rngl_pow_div_pow {T ro rp} Hos Hiv a%_L (m n)%_nat.
