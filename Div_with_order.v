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
From Stdlib Require Import Utf8 Arith.

Require Import Structures.
Require Import Order.
Require Import Add.
Require Import Mul.
Require Import Div.
Require Import Add_with_order.
Require Import Mul_with_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_inv_pos :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a → 0 < a⁻¹)%L.
Proof.
intros * Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hza.
assert (Haz : a ≠ 0%L). {
  intros H; subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
specialize (rngl_inv_neq_0 Hon Hos Hiv) as H1.
destruct (rngl_le_dec Hor 0 a⁻¹)%L as [H2| H2]. {
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  intros H; symmetry in H; revert H.
  now apply H1.
}
apply (rngl_not_le Hor) in H2.
destruct H2 as (H2, H3).
specialize (rngl_mul_nonneg_nonpos Hop Hor) as H4.
assert (H : (0 ≤ a)%L) by now apply (rngl_lt_iff Hor) in Hza.
specialize (H4 _ _ H H3); clear H.
rewrite (rngl_mul_inv_diag_r Hon Hiv a Haz) in H4.
specialize (rngl_0_le_1 Hon Hos Hor) as H5.
specialize (rngl_le_antisymm Hor _ _ H4 H5) as H6.
clear H4 H5.
apply (rngl_1_eq_0_iff Hon Hos) in H6.
specialize (rngl_characteristic_1 Hon Hos H6) as H4.
exfalso; apply Haz, H4.
Qed.

Theorem rngl_inv_neg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, (a < 0 → a⁻¹ < 0)%L.
Proof.
intros * Hon Hop Hiv Hor.
intros * Hza.
specialize (rngl_inv_pos Hon Hop Hiv Hor) as H2.
specialize (H2 (- a))%L.
apply (rngl_opp_lt_compat Hop Hor).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_opp_inv Hon Hop Hiv); [ | now apply rngl_lt_iff ].
apply H2.
apply (rngl_opp_lt_compat Hop Hor) in Hza.
now rewrite (rngl_opp_0 Hop) in Hza.
Qed.

Theorem rngl_div_le_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b ≠ 0 → 0 ≤ a ≤ b → a / b ≤ 1)%L.
Proof.
intros * Hon Hop Hiv Hor * Hbz (Hza, Hab).
unfold rngl_div.
rewrite Hiv.
specialize (rngl_mul_le_compat_nonneg Hor) as H1.
specialize (H1 a b⁻¹ b b⁻¹)%L.
assert (H : (0 ≤ a ≤ b)%L) by easy.
specialize (H1 H); clear H.
assert (H : (0 ≤ b⁻¹ ≤ b⁻¹)%L). {
  split; [ | apply (rngl_le_refl Hor) ].
  apply (rngl_lt_le_incl Hor).
  apply (rngl_inv_pos Hon Hop Hiv Hor).
  apply (rngl_lt_iff Hor).
  split; [ | congruence ].
  now apply (rngl_le_trans Hor _ a).
}
specialize (H1 H); clear H.
now rewrite (rngl_mul_inv_diag_r Hon Hiv) in H1.
Qed.

Theorem rngl_one_sub_half :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (1 - 2⁻¹ = 2⁻¹)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 (_ - _))%L, H1.
}
assert (Hc2 : (2 ≠ 0)%L). {
  specialize (rngl_0_lt_2 Hon Hos Hc1 Hor) as H2.
  intros H; rewrite H in H2.
  now apply (rngl_lt_irrefl Hor) in H2.
}
apply (rngl_mul_cancel_r Hi1) with (c := 2%L); [ easy | ].
rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
rewrite (rngl_mul_1_l Hon).
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_integral :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec_or_order T)%bool = true →
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
  assert (Hon : rngl_has_1 T = true). {
    remember (rngl_has_inv_and_1_or_quot T) as iq eqn:Hiq.
    symmetry in Hiq.
    destruct iq; [ cbn in Hdo | easy ].
    apply rngl_has_inv_and_1_or_quot_iff in Hiq.
    destruct Hiq as [| Hiq]; [ easy | ].
    apply rngl_has_quot_has_no_inv in Hiq.
    congruence.
  }
  apply Bool.andb_true_iff in Hdo.
  destruct Hdo as (Hiq, Heo).
  cbn.
  assert (H : (a⁻¹ * a * b = a⁻¹ * 0)%L). {
    now rewrite <- rngl_mul_assoc, Hab.
  }
  destruct (rngl_eq_dec Heo a 0) as [Haz| Haz]; [ now left | right ].
  rewrite rngl_mul_inv_diag_l in H; [ | easy | easy | easy ].
  rewrite (rngl_mul_1_l Hon) in H; rewrite H.
  apply (rngl_mul_0_r Hmo).
} {
  apply andb_prop in Hdo.
  destruct Hdo as (Hdi, Heo).
  specialize rngl_mul_div as H1.
  rewrite Hdi in H1.
  specialize (H1 eq_refl).
  destruct (rngl_eq_dec Heo b 0) as [Hbz| Hbz]; [ now right | left ].
  specialize (H1 a b Hbz) as H4.
  rewrite Hab in H4.
  rewrite <- H4.
  now apply rngl_div_0_l.
}
Qed.

Theorem rngl_abs_div :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec T = true →
  rngl_is_ordered T = true →
  ∀ x y, y ≠ 0%L → rngl_abs (x / y)%L = (rngl_abs x / rngl_abs y)%L.
Proof.
intros * Hon Hop Hiv Heb Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hyz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
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
        apply (rngl_opp_le_compat Hop Hor).
        rewrite (rngl_opp_0 Hop).
        rewrite (rngl_opp_inv Hon Hop Hiv _ Hyz).
        apply (rngl_opp_le_compat Hop Hor) in Hy.
        rewrite (rngl_opp_0 Hop) in Hy.
        apply (rngl_lt_le_incl Hor).
        apply (rngl_inv_pos Hon Hop Hiv Hor).
        apply (rngl_lt_iff Hor).
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
        now apply (rngl_inv_neq_0 Hon Hos Hiv).
      }
    } {
      unfold rngl_div.
      rewrite Hiv.
      rewrite (rngl_mul_opp_l Hop).
      rewrite <- (rngl_mul_opp_r Hop).
      f_equal.
      rewrite (rngl_opp_inv Hon Hop Hiv). 2: {
        intros H.
        apply (f_equal rngl_opp) in H.
        rewrite (rngl_opp_0 Hop) in H.
        now rewrite (rngl_opp_involutive Hop) in H.
      }
      now rewrite (rngl_opp_involutive Hop).
    }
  } {
    apply (rngl_leb_gt Hor) in Hy.
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
      apply (rngl_mul_nonpos_nonneg Hop Hor _ _ Hx).
      apply (rngl_lt_le_incl Hor).
      now apply (rngl_inv_pos Hon Hop Hiv Hor).
    }
  }
}
apply (rngl_leb_gt Hor) in Hx.
destruct yz. {
  apply rngl_leb_le in Hy.
  destruct xyz. {
    apply rngl_leb_le in Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite <- (rngl_mul_opp_r Hop).
    f_equal.
    now apply (rngl_opp_inv Hon Hop Hiv).
  } {
    apply rngl_leb_nle in Hxy.
    exfalso; apply Hxy; clear Hxy.
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_lt_le_incl Hor) in Hx.
    apply (rngl_mul_nonneg_nonpos Hop Hor _ _ Hx).
    apply (rngl_lt_le_incl Hor).
    apply (rngl_inv_neg Hon Hop Hiv Hor).
    apply (rngl_lt_iff Hor).
    split; [ easy | congruence ].
  }
}
apply rngl_leb_nle in Hy.
apply (rngl_not_le Hor) in Hy.
destruct Hy as (_, Hy).
destruct xyz; [ | easy ].
apply rngl_leb_le in Hxy.
unfold rngl_div in Hxy.
rewrite Hiv in Hxy.
assert (Hzy : (0 < y)%L). {
  apply (rngl_lt_iff Hor).
  split; [ easy | congruence ].
}
specialize (rngl_inv_pos Hon Hop Hiv Hor _ Hzy) as Hy'.
apply (rngl_lt_le_incl Hor) in Hy'.
generalize Hx; intros Hx'.
apply (rngl_lt_le_incl Hor) in Hx'.
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
  now apply (rngl_inv_neq_0 Hon Hos Hiv).
}
Qed.

Theorem rngl_mul_pos_pos :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a * b)%L.
Proof.
intros Hos Hor Hii * Haz Hbz.
apply (rngl_lt_iff Hor) in Haz.
apply (rngl_lt_iff Hor) in Hbz.
apply (rngl_lt_iff Hor).
destruct Haz as (Haz, Hza).
destruct Hbz as (Hbz, Hzb).
split. {
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
}
apply not_eq_sym in Hza, Hzb.
apply not_eq_sym.
intros Hab.
now apply (rngl_eq_mul_0_l Hos Hii) in Hab.
Qed.

Theorem rngl_mul_pos_cancel_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < b → 0 < a * b ↔ 0 < a)%L.
Proof.
intros Hop Hor Hii * Ha.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply rngl_nle_gt in Habz.
      apply (rngl_nlt_ge_iff Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonpos_nonneg Hop Hor); [ | easy ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst a.
  now rewrite (rngl_mul_0_l Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hos Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b * a < c * a)%L.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  apply (rngl_mul_pos_pos Hos Hor Hii); [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hbc.
  apply (rngl_mul_pos_cancel_r Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_div_lt_mono_pos_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (b / a < c / a)%L.
Proof.
intros Hon Hop Hiv Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hza.
  rewrite (H1 a) in Hza.
  now apply (rngl_lt_irrefl Hor) in Hza.
}
intros * Hza.
split; intros Hbc. {
  progress unfold rngl_div at 1 2.
  rewrite Hiv.
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii); [ | easy ].
  now apply (rngl_inv_pos Hon Hop Hiv Hor).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii a) in Hbc; [ | easy ].
  rewrite (rngl_div_mul Hon Hiv) in Hbc. 2: {
    intros H; subst a.
    now apply (rngl_lt_irrefl Hor) in Hza.
  }
  rewrite (rngl_div_mul Hon Hiv) in Hbc. 2: {
    intros H; subst a.
    now apply (rngl_lt_irrefl Hor) in Hza.
  }
  easy.
}
Qed.

Theorem rngl_mul_pos_cancel_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (0 < a → 0 < a * b ↔ 0 < b)%L.
Proof.
intros Hop Hor Hii * Ha.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  apply (rngl_lt_iff Hor) in Ha.
  apply (rngl_lt_iff Hor) in Hb.
  apply (rngl_lt_iff Hor).
  destruct Ha as (Haz, Hza).
  destruct Hb as (Habz, Hzab).
  apply not_eq_sym in Hza, Hzab.
  split. {
    apply (rngl_lt_eq_cases Hor) in Habz.
    destruct Habz as [Habz| Habz]. {
      apply rngl_nle_gt in Habz.
      apply (rngl_nlt_ge_iff Hor).
      intros Hb; apply Habz; clear Habz.
      apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
      now apply (rngl_lt_le_incl Hor).
    }
    now rewrite Habz in Hzab.
  }
  intros H; subst b.
  now rewrite (rngl_mul_0_r Hos) in Hzab.
} {
  now apply (rngl_mul_pos_pos Hos Hor).
}
Qed.

Theorem rngl_mul_lt_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < a)%L → (b < c)%L ↔ (a * b < a * c)%L.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha.
split; intros Hbc. {
  apply (rngl_lt_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
  now apply (rngl_lt_0_sub Hop Hor).
} {
  apply (rngl_lt_0_sub Hop Hor) in Hbc.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hbc.
  apply (rngl_mul_pos_cancel_l Hop Hor Hii) in Hbc; [ | easy ].
  now apply (rngl_lt_0_sub Hop Hor).
}
Qed.

Theorem rngl_mul_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (c * a ≤ c * b)%L.
Proof.
intros Hop Hor Hii * Hc.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_lt_eq_cases Hor) in Hab.
  destruct Hab as [Hab| Hab]; [ | subst b; apply (rngl_le_refl Hor) ].
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_le_0_sub Hop Hor).
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_l Hop) in Hab.
  apply rngl_nlt_ge in Hab.
  apply (rngl_nlt_ge_iff Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (c * 0)%L by apply (rngl_mul_0_r Hos).
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt_iff Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply rngl_nlt_ge in H2.
}
Qed.

Theorem rngl_mul_le_mono_pos_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c : T, (0 < c)%L → (a ≤ b)%L ↔ (a * c ≤ b * c)%L.
Proof.
intros Hop Hor Hii * Hc.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_le_0_sub Hop Hor) in Hab.
  rewrite <- (rngl_mul_sub_distr_r Hop) in Hab.
  apply rngl_nlt_ge in Hab.
  apply (rngl_nlt_ge_iff Hor).
  intros H1; apply Hab; clear Hab.
  replace 0%L with (0 * c)%L by apply (rngl_mul_0_l Hos).
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii); [ easy | ].
  apply (rngl_nle_gt_iff Hor).
  intros H2.
  apply -> (rngl_le_0_sub Hop Hor) in H2.
  now apply rngl_nlt_ge in H2.
}
Qed.

Theorem rngl_div_le_mono_pos_l :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 < a)%L → (b⁻¹ ≤ c⁻¹ ↔ a / b ≤ a / c)%L.
Proof.
intros Hop Hiv Hor Hii.
intros * Haz.
progress unfold rngl_div.
rewrite Hiv.
now apply (rngl_mul_le_mono_pos_l Hop Hor Hii).
Qed.

Theorem rngl_div_le_mono_pos_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 < c)%L → (a ≤ b ↔ a / c ≤ b / c)%L.
Proof.
intros Hon Hop Hiv Hor Hii.
intros * Hcz.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_le_mono_pos_r Hop Hor Hii).
now apply (rngl_inv_pos Hon Hop Hiv Hor).
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
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (a⁻¹ ≤ b⁻¹)%L ↔ (b ≤ a)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
intros * Haz Hbz.
split; intros Hab. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor a) in Hab. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ b) in Hab. 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_mul_inv_diag_r Hon Hiv) in Hab. 2: {
    now apply (rngl_lt_neq Hor) in Haz.
  }
  rewrite <- rngl_mul_assoc in Hab.
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hab. 2: {
    now apply (rngl_lt_neq Hor) in Hbz.
  }
  rewrite (rngl_mul_1_l Hon) in Hab.
  rewrite (rngl_mul_1_r Hon) in Hab.
  easy.
} {
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii _ _ a); [ easy | ].
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ b); [ easy | ].
  rewrite (rngl_mul_inv_diag_r Hon Hiv). 2: {
    now apply (rngl_lt_neq Hor) in Haz.
  }
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_inv_diag_l Hon Hiv). 2: {
    now apply (rngl_lt_neq Hor) in Hbz.
  }
  rewrite (rngl_mul_1_l Hon).
  rewrite (rngl_mul_1_r Hon).
  easy.
}
Qed.

Theorem rngl_div_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 < b → 0 ≤ a / b)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha Hb.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_mul_le_mono_pos_l Hop Hor) with (c := b); [ | easy | ]. {
  apply Bool.orb_true_iff; right.
  now apply rngl_has_inv_and_1_or_quot_iff; left.
}
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_subt_iff; left ].
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ apply (rngl_0_le_1 Hon Hos Hor) | ].
apply (rngl_lt_iff Hor) in Hb.
now apply not_eq_sym.
Qed.

Theorem rngl_div_pos :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (0 < b)%L → (0 < a / b)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Ha Hb.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
now apply (rngl_inv_pos Hon Hop Hiv Hor).
Qed.

Theorem rngl_le_div_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a ≤ b * c ↔ a / c ≤ b)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := c); [ easy | ].
  rewrite (rngl_div_mul Hon Hiv); [ easy | ].
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
} {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ c) in Habq; [ | easy ].
  rewrite (rngl_div_mul Hon Hiv) in Habq; [ easy | ].
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
Qed.

Theorem rngl_le_div_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c ≤ b ↔ a ≤ b / c)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
split; intros Habq. {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii) with (c := c); [ easy | ].
  now rewrite (rngl_div_mul Hon Hiv).
} {
  apply (rngl_mul_le_mono_pos_r Hop Hor Hii _ _ c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hon Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a < b * c ↔ a / c < b)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := c); [ easy | ].
  now rewrite (rngl_div_mul Hon Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hon Hiv) in Habq.
}
Qed.

Theorem rngl_lt_div_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (0 < c → a * c < b ↔ a < b / c)%L.
Proof.
intros Hon Hop Hiv Hor * Hzc.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
assert (Hcz : c ≠ 0%L). {
  intros H; rewrite H in Hzc.
  now apply (rngl_lt_irrefl Hor) in Hzc.
}
split; intros Habq. {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := c); [ easy | ].
  now rewrite (rngl_div_mul Hon Hiv).
} {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii c) in Habq; [ | easy ].
  now rewrite (rngl_div_mul Hon Hiv) in Habq.
}
Qed.

Theorem rngl_middle_sub_l :
   rngl_has_1 T = true →
   rngl_has_opp T = true →
   rngl_has_inv T = true →
   rngl_is_ordered T = true →
   ∀ a b, (((a + b) / 2 - a) = (b - a) / 2)%L.
Proof.
intros Hon Hop Hiv Hor *.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
progress unfold rngl_sub.
rewrite Hop.
rewrite <- rngl_add_assoc; f_equal.
rewrite (rngl_add_opp_r Hop).
rewrite <- (rngl_mul_1_r Hon a) at 2.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
f_equal.
rewrite <- (rngl_opp_involutive Hop (_ - _))%L.
f_equal.
rewrite (rngl_opp_sub_distr Hop).
apply (rngl_one_sub_half Hon Hop Hiv Hor).
Qed.

Theorem rngl_middle_sub_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (b - (a + b) / 2 = (b - a) / 2)%L.
Proof.
intros Hon Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_add_comm.
rewrite (rngl_sub_add_distr Hos).
f_equal.
rewrite (rngl_sub_mul_r_diag_l Hon Hop).
f_equal.
apply (rngl_one_sub_half Hon Hop Hiv Hor).
Qed.

Theorem rngl_abs_le_ε :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a,
  (∀ ε, (0 < ε)%L → (rngl_abs a ≤ ε)%L)
  → a = 0%L.
Proof.
intros Hon Hop Hiv Hor * H1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  apply (rngl_characteristic_1 Hon Hos Hc1).
}
destruct (rngl_lt_dec Hor a 0%L) as [H12| H12]. {
  specialize (H1 (- a / 2))%L.
  assert (H : (0 < - a / 2)%L). {
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_pos_pos Hos Hor Hii). {
      rewrite <- (rngl_opp_0 Hop).
      now apply -> (rngl_opp_lt_compat Hop Hor).
    }
    apply (rngl_inv_pos Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  specialize (H1 H); clear H.
  exfalso.
  apply rngl_nlt_ge in H1; apply H1; clear H1.
  rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  remember (_ * _)%L as x.
  rewrite <- (rngl_mul_1_r Hon (- a))%L.
  subst x.
  apply (rngl_mul_lt_mono_pos_l Hop Hor Hii). 2: {
    apply (rngl_lt_add_r Hos Hor).
    apply (rngl_0_lt_1 Hon Hos Hc1 Hor).
  }
  rewrite <- (rngl_opp_0 Hop).
  now apply -> (rngl_opp_lt_compat Hop Hor).
}
destruct (rngl_lt_dec Hor 0%L a) as [H21| H21]. {
  specialize (H1 (a / 2))%L.
  assert (H : (0 < a / 2)%L). {
    progress unfold rngl_div.
    rewrite Hiv.
    apply (rngl_mul_pos_pos Hos Hor Hii); [ easy | ].
    apply (rngl_inv_pos Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  specialize (H1 H); clear H.
  exfalso.
  apply rngl_nlt_ge in H1; apply H1.
  rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply (rngl_lt_le_incl Hor).
  }
  apply (rngl_lt_div_l Hon Hop Hiv Hor). {
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  rewrite rngl_mul_add_distr_l.
  rewrite (rngl_mul_1_r Hon).
  now apply (rngl_lt_add_r Hos Hor).
}
apply (rngl_nlt_ge_iff Hor) in H12, H21.
now apply (rngl_le_antisymm Hor).
Qed.

Theorem rngl_mul_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true →
  ∀ a b, (0 < a → b < 0 → a * b < 0)%L.
Proof.
intros Hop Hor Hid * Hza Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_mul_nonneg_nonpos Hop Hor). {
    now apply (rngl_lt_le_incl Hor).
  } {
    now apply (rngl_lt_le_incl Hor).
  }
}
intros H.
apply (rngl_integral Hos Hid) in H.
destruct H as [H| H]. {
  subst a.
  now apply (rngl_lt_irrefl Hor) in Hza.
} {
  subst b.
  now apply (rngl_lt_irrefl Hor) in Hbz.
}
Qed.

Theorem eq_rngl_add_square_0 :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a * a + b * b = 0)%L → a = 0%L ∧ b = 0%L.
Proof.
intros * Hos Hor Hii.
assert (Hio :
  (rngl_is_integral_domain T ||
    rngl_has_inv_and_1_or_quot T &&
      rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff in Hii.
  apply Bool.orb_true_iff.
  destruct Hii as [Hii| Hii]; [ now left | right ].
  rewrite Hii.
  now apply (rngl_has_eq_dec_or_is_ordered_r).
}
intros * Hab.
apply (rngl_eq_add_0 Hor) in Hab; cycle 1. {
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
  rngl_has_inv_and_1_or_quot T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a * b) = rngl_abs a * rngl_abs b)%L.
Proof.
intros Hop Hi1 Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
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
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz; [ now rewrite (rngl_mul_opp_r Hop) | ].
  apply (rngl_leb_gt Hor) in Hbz.
  apply rngl_nlt_ge in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_iff Hor).
  split. {
    now apply (rngl_mul_nonneg_nonneg Hos Hor); apply (rngl_lt_le_incl Hor).
  }
  apply not_eq_sym.
  intros H1.
  apply (rngl_eq_mul_0_l Hos) in H1. {
    now subst a; apply (rngl_lt_irrefl Hor) in Haz.
  } {
    rewrite Hi1.
    now destruct (rngl_is_integral_domain T).
  } {
    intros H; subst b.
    now apply (rngl_lt_irrefl Hor) in Hbz.
  }
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  rewrite (rngl_mul_opp_l Hop).
  apply rngl_leb_le in Haz.
  destruct bz. {
    rewrite (rngl_mul_opp_r Hop).
    symmetry.
    apply (rngl_opp_involutive Hop).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply (rngl_lt_iff Hor) in Hbz.
  destruct Hbz as (Hbz, Hzb).
  specialize (rngl_mul_nonpos_nonneg Hop Hor _ _ Haz Hbz) as H1.
  now apply rngl_nlt_ge in H1.
}
apply (rngl_leb_gt Hor) in Haz.
destruct bz; [ | easy ].
apply rngl_leb_le in Hbz.
apply (rngl_lt_iff Hor) in Haz.
destruct Haz as (Haz, Hza).
specialize (rngl_mul_nonneg_nonpos Hop Hor _ _ Haz Hbz) as H1.
now apply rngl_nlt_ge in H1.
Qed.

Theorem eq_rngl_squ_rngl_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b,
  (a * b = b * a)%L
  → (a² = b²)%L
  → rngl_abs a = rngl_abs b.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Habc Hab.
apply (rngl_sub_move_0_r Hop) in Hab.
rewrite (rngl_squ_sub_squ Hop), Habc in Hab.
rewrite (rngl_add_sub Hos) in Hab.
assert (Hio :
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec_or_order T)%bool = true). {
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
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a < 0)%L → (b < 0)%L → (0 < a * b)%L.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Haz Hbz.
rewrite <- (rngl_mul_opp_opp Hop).
apply (rngl_mul_pos_pos Hos Hor Hii).
now apply (rngl_opp_pos_neg Hop Hor).
now apply (rngl_opp_pos_neg Hop Hor).
Qed.

Theorem rngl_mul_lt_mono_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c d, (0 ≤ a < b → 0 ≤ c < d → a * c < b * d)%L.
Proof.
intros Hop Hor Hii * (Haz, Hab) (Hcz, Hcd).
apply (rngl_le_lt_trans Hor _ (b * c)%L). {
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii); [ | easy ].
now apply (rngl_le_lt_trans Hor _ a).
Qed.

Theorem rngl_mul_min_distr_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b c, (0 ≤ a)%L → rngl_min (a * b)%L (a * c)%L = (a * rngl_min b c)%L.
Proof.
intros Hop Hor Hii.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hza.
destruct (rngl_eq_dec Heo a 0%L) as [Haz| Haz]. {
  subst a.
  do 3 rewrite (rngl_mul_0_l Hos).
  apply (rngl_min_id Hor).
}
assert (H : (0 < a)%L). {
  apply (rngl_lt_iff Hor).
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
  apply (rngl_leb_gt Hor) in Hbc.
  apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Habc; [ | easy ].
  now apply rngl_nle_gt in Hbc.
}
destruct bc; [ | easy ].
f_equal.
apply rngl_leb_le in Hbc.
apply (rngl_leb_gt Hor) in Habc.
apply (rngl_mul_lt_mono_pos_l Hop Hor Hii) in Habc; [ | easy ].
now apply rngl_nle_gt in Habc.
Qed.

Theorem rngl_square_le_simpl_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ b → a * a ≤ b * b → a ≤ b)%L.
Proof.
intros Hop Hor Hii * Hzb Hab.
destruct (rngl_le_dec Hor a 0%L) as [Haz| Haz]. {
  now apply (rngl_le_trans Hor a 0%L b).
}
apply (rngl_nle_gt_iff Hor) in Haz.
apply rngl_nlt_ge in Hab.
apply (rngl_nlt_ge_iff Hor).
intros Hba; apply Hab; clear Hab.
now apply (rngl_mul_lt_mono_nonneg Hop Hor Hii).
Qed.

Theorem rngl_pow_pos_pos :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ a n, (0 < a → 0 < a ^ n)%L.
Proof.
intros Hon Hos Hiv Hc1 Hor.
intros * Hza.
induction n; cbn; [ apply (rngl_0_lt_1 Hon Hos Hc1 Hor) | ].
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
now apply (rngl_mul_pos_pos Hos Hor Hii).
Qed.

Theorem rngl_le_0_mul :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)%L.
Proof.
intros Hon Hop Hiv Hor * Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (rngl_le_dec Hor 0 a)%L as [Hza| Hza]. {
  destruct (rngl_lt_dec Hor 0 a)%L as [Hlza| Hlza]. 2: {
    apply (rngl_nlt_ge_iff Hor) in Hlza.
    apply (rngl_le_antisymm Hor) in Hza; [ | easy ].
    subst a.
    destruct (rngl_le_dec Hor 0 b)%L as [Hzb| Hzb]; [ now left | ].
    apply (rngl_nle_gt_iff Hor), (rngl_lt_le_incl Hor) in Hzb.
    now right.
  }
  rewrite <- (rngl_mul_0_r Hos a) in Hab.
  now left; apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in Hab.
} {
  apply (rngl_nle_gt_iff Hor) in Hza.
  right.
  rewrite <- (rngl_mul_0_l Hos b) in Hab.
  split; [ now apply (rngl_lt_le_incl Hor) | ].
  apply rngl_nle_gt in Hza.
  apply (rngl_nlt_ge_iff Hor).
  intros Hzb; apply Hza.
  now apply (rngl_mul_le_mono_pos_r Hop Hor Hii) in Hab.
}
Qed.

Theorem rngl_abs_lt_squ_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a * b = b * a)%L → (rngl_abs a < rngl_abs b)%L → (a² < b²)%L.
Proof.
intros Hop Hor Hii.
intros * Habc Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_abs_le_squ_le Hop Hor).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (eq_rngl_squ_rngl_abs Hop Hor Hii _ _ Habc) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem rngl_squ_le_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a² ≤ b² → rngl_abs a ≤ rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
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
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_le_compat Hop Hor).
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Haz.
    rewrite (rngl_opp_0 Hop) in Haz.
    rewrite <- (rngl_mul_opp_opp Hop) in Hab.
    apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab; [ easy | ].
    now apply (rngl_lt_le_incl Hor).
  }
} {
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_opp_le_compat Hop Hor) in Hbz.
    rewrite (rngl_opp_0 Hop) in Hbz.
    rewrite <- (rngl_mul_opp_opp Hop b) in Hab.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  } {
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor) in Haz, Hbz.
    now apply (rngl_square_le_simpl_nonneg Hop Hor Hii) in Hab.
  }
}
Qed.

Theorem rngl_squ_lt_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b : T, (a² < b²)%L → (rngl_abs a < rngl_abs b)%L.
Proof.
intros Hop Hor Hii * Hab.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_squ_le_abs_le Hop Hor Hii).
  now apply (rngl_lt_le_incl Hor).
}
intros H.
apply (f_equal rngl_squ) in H.
do 2 rewrite (rngl_squ_abs Hop) in H.
rewrite H in Hab.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

Theorem eq_rngl_squ_0 :
  rngl_has_opp_or_subt T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true →
  ∀ a, (a² = 0 → a = 0)%L.
Proof.
intros Hos Hio * Ha.
apply (rngl_integral Hos Hio) in Ha.
now destruct Ha.
Qed.

Theorem rngl_le_squ_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a² ≤ b² → a ≤ b)%L.
Proof.
intros Hop Hor Hii.
intros * Hza Hzb Hab.
rewrite <- (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
now apply (rngl_squ_le_abs_le Hop Hor Hii).
Qed.

Theorem rngl_le_le_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ a → a ≤ b → a² ≤ b²)%L.
Proof.
intros Hop Hor Hii.
intros * Hza Hab.
apply (rngl_abs_le_squ_le Hop Hor).
rewrite (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor b); [ easy | ].
now apply (rngl_le_trans Hor _ a).
Qed.

Theorem rngl_lt_squ_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a² < b² → a < b)%L.
Proof.
intros Hop Hor Hii.
intros * Hza Hzb Hab.
rewrite <- (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite <- (rngl_abs_nonneg_eq Hop Hor b); [ | easy ].
now apply (rngl_squ_lt_abs_lt Hop Hor Hii).
Qed.

Theorem rngl_lt_lt_squ :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true →
  ∀ a b, (a * b = b * a → 0 ≤ a → a < b → a² < b²)%L.
Proof.
intros Hop Hor Hii.
intros * Habba Hza Hab.
apply (rngl_abs_lt_squ_lt Hop Hor Hii _ _ Habba).
rewrite (rngl_abs_nonneg_eq Hop Hor a); [ | easy ].
rewrite (rngl_abs_nonneg_eq Hop Hor b); [ easy | ].
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_lt_le_incl Hor) in Hab.
Qed.

Theorem rngl_squ_eq_cases :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_has_eq_dec_or_order T = true →
  ∀ a b, (a * b = b * a → a² = b² → a = b ∨ a = -b)%L.
Proof.
intros Hon Hop Hiv Heo * Habc Hab.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
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
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_has_inv T = true →
  ∀ (a : T) m n,
  (a ≠ 0)%L
  → n ≤ m
  → (a ^ m / a ^ n = a ^ (m - n))%L.
Proof.
intros Hic Hon Hos Hiv.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ ^ (_ - _)))%L.
  apply H1.
}
intros * Haz Hnm.
revert m Hnm.
induction n; intros; cbn. {
  rewrite (rngl_div_1_r Hon Hiq Hc1).
  now rewrite Nat.sub_0_r.
}
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hnm.
cbn.
rewrite (rngl_mul_comm Hic a).
rewrite (rngl_mul_comm Hic _ (a ^ n)).
rewrite <- (rngl_div_div Hos Hon Hiv); [ | easy | ]. 2: {
  apply (rngl_pow_nonzero Hon Hc1 Hos); [ | easy ].
  rewrite Hi1.
  apply Bool.orb_true_r.
}
rewrite (rngl_mul_div Hi1); [ | easy ].
now apply IHn.
Qed.

End a.

Arguments rngl_div_le_mono_pos_l {T ro rp} Hop Hiv Hor Hii (a b c)%_L.
Arguments rngl_div_le_mono_pos_r {T ro rp} Hon Hop Hiv Hor Hii (a b c)%_L.
Arguments rngl_middle_sub_r {T ro rp} Hon Hop Hiv Hor (a b)%_L.
Arguments rngl_mul_le_mono_pos_l {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_mul_le_mono_pos_r {T ro rp} Hop Hor Hii (a b c)%_L.
Arguments rngl_pow_div_pow {T ro rp} Hic Hon Hos Hiv a%_L (m n)%_nat.
