(** * DerivMul

Derivability of a product and of an inverse of a function from [A]
to [T] where
- [A] is any type with a distance and relation orders [lt] and [le], and
- [T] is a ring-like, generally ℝ.

The derivative of [f.g] is well-known as being [f.g'+f'.g].

The derivative of [f⁻¹] is well-knwon as being [-f'/f²].
*)

Set Nested Proofs Allowed.

Require Import Stdlib.Arith.Arith.
Require Import Utf8 Core RealLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Context {Hop : rngl_has_opp T = true}.
Context {Hto : rngl_is_totally_ordered T = true}.
Let Hor := rngl_is_totally_ordered_is_ordered Hto.

Theorem rngl_dist_mul_distr_r :
  rngl_has_inv_or_pdiv T = true →
  ∀ a b c,
  (0 ≤ c)%L → (rngl_dist a b * c = rngl_dist (a * c) (b * c))%L.
Proof.
intros Hiq.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hzc.
progress unfold rngl_dist.
(*
...
(* 35,30 *)
  ============================
  (∣ (a - b) ∣ * c)%L = ∣ (a * c - b * c) ∣
...
(* 60,50 *)
  ============================
  ((∣ a - b ∣) * c)%L = ∣ a * c - b * c ∣
...
*)
rewrite <- (rngl_mul_sub_distr_r Hop).
progress unfold rngl_abs.
rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite (rngl_leb_sub_0 Hop Hor).
rewrite <- (rngl_mul_sub_distr_r Hop).
remember (a ≤? b)%L as ab eqn:Hab.
remember (a * c ≤? b * c)%L as acbc eqn:Hacbc.
symmetry in Hab, Hacbc.
destruct ab. {
  destruct acbc; [ apply (rngl_mul_opp_l Hop) | ].
  apply rngl_leb_le in Hab.
  apply (rngl_leb_gt_iff Hto) in Hacbc.
  exfalso.
  apply (rngl_nle_gt Hor) in Hacbc.
  apply Hacbc; clear Hacbc.
  now apply (rngl_mul_le_mono_nonneg_r Hop Hor).
}
apply (rngl_leb_gt_iff Hto) in Hab.
destruct acbc; [ | easy ].
apply rngl_leb_le in Hacbc.
apply (rngl_lt_eq_cases Hor) in Hzc.
destruct Hzc as [Hzc| Hzc]. {
  exfalso.
  apply (rngl_nlt_ge Hor) in Hacbc.
  apply Hacbc; clear Hacbc.
  now apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto).
}
subst c.
rewrite (rngl_mul_0_r Hos).
symmetry.
apply (rngl_opp_0 Hop).
Qed.

Definition is_limit_when_tending_to_neighbourhood_le (is_left : bool) {A B}
  (lt : A → A → Prop) (da : A → A → T) (db : B → B → T)
  (f : A → B) (x₀ : A) (L : B) :=
  (∀ ε : T, 0 < ε →
   ∃ η : T, (0 < η)%L ∧ ∀ x : A,
   (if is_left then lt x x₀ else lt x₀ x)
   → da x x₀ < η
   → db (f x) L ≤ ε)%L.

Theorem is_limit_lt_is_limit_le_iff :
  rngl_has_inv T = true →
  ∀ is_left {A B} lt da db (f : A → B) x₀ L,
  is_limit_when_tending_to_neighbourhood is_left lt da db f x₀ L
  ↔ is_limit_when_tending_to_neighbourhood_le is_left lt da db f x₀ L.
Proof.
intros Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  split; intros H ε; rewrite (H1 ε); intro Hε;
  now apply rngl_lt_irrefl in Hε.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
split; intros H1 ε Hε. {
  specialize (H1 ε Hε).
  destruct H1 as (η & Hη & H1).
  exists η.
  split; [ easy | ].
  intros x Hlt Hd.
  apply rngl_lt_le_incl.
  now apply H1.
} {
  specialize (H1 (ε / 2))%L.
  assert (Hε2 : (0 < ε / 2)%L). {
    apply (rngl_div_pos Hop Hiv Hto _ _ Hε Hz2).
  }
  specialize (H1 Hε2).
  destruct H1 as (η & Hη & H1).
  exists η.
  split; [ easy | ].
  intros x Hlt Hd.
  apply (rngl_le_lt_trans Hor _ (ε / 2)). 2: {
    apply (rngl_lt_div_l Hop Hiv Hto _ _ _ Hz2).
    rewrite (rngl_mul_2_r).
    apply (rngl_lt_add_l Hos Hor _ _ Hε).
  }
  now apply H1.
}
Qed.

Theorem left_or_right_derivable_continuous_when_derivative_eq_0 :
  rngl_has_inv T = true →
  ∀ is_left A lt,
  (∀ x, ¬ (lt x x))
  → ∀ {da} (dist : is_dist da) (f : A → T) x,
  left_or_right_derivative_at is_left lt da rngl_dist f x 0%L
  → left_or_right_continuous_at is_left lt da rngl_dist f x.
Proof.
intros Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hlti * dist * Hd.
rename x into x₀.
intros ε Hε.
specialize (Hd √ε).
assert (Hsε : (0 < √ε)%L) by now apply (rl_sqrt_pos Hos Hto).
specialize (Hd Hsε).
destruct Hd as (η & Hη & Hd).
exists (rngl_min √ε η).
split; [ now apply rngl_min_glb_lt | ].
intros x Hlt Hdxx.
specialize (Hd x Hlt).
apply (rngl_min_glb_lt_iff Hto) in Hdxx.
destruct Hdxx as (Hdε, Hdη).
specialize (Hd Hdη).
assert (Hdz : da x x₀ ≠ 0%L). {
  intros H.
  apply (dist_separation dist) in H.
  subst x.
  now destruct is_left; apply Hlti in Hlt.
}
apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto (da x x₀)) in Hd. 2: {
  clear H.
  apply rngl_le_neq.
  split; [ apply (dist_nonneg Hop Hiv Hto dist) | easy ].
}
cbn in Hd |-*.
rewrite (rngl_dist_mul_distr_r Hiq) in Hd. 2: {
  apply (dist_nonneg Hop Hiv Hto dist).
}
rewrite (rngl_div_mul Hiv) in Hd; [ | easy ].
rewrite (rngl_mul_0_l Hos) in Hd.
progress unfold rngl_dist in Hd.
progress unfold rngl_dist.
rewrite (rngl_sub_0_r Hos) in Hd.
destruct is_left. {
  rewrite rngl_mul_1_l in Hd.
  eapply (rngl_lt_le_trans Hor). {
    rewrite <- (rngl_abs_opp Hop Hto).
    rewrite (rngl_opp_sub_distr Hop).
    apply Hd.
  }
  eapply (rngl_le_trans Hor). {
    apply (rngl_mul_le_mono_pos_l Hop Hiq Hto); [ easy | ].
    apply rngl_lt_le_incl, Hdε.
  }
  rewrite fold_rngl_squ.
  rewrite (rngl_squ_sqrt); [ apply (rngl_le_refl Hor) | ].
  now apply rngl_lt_le_incl.
} {
  rewrite (rngl_mul_opp_l Hop) in Hd.
  rewrite rngl_mul_1_l in Hd.
  rewrite (rngl_opp_sub_distr Hop) in Hd.
  eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
  eapply (rngl_le_trans Hor). {
    apply (rngl_mul_le_mono_pos_l Hop Hiq Hto); [ easy | ].
    apply rngl_lt_le_incl, Hdε.
  }
  rewrite fold_rngl_squ.
  rewrite (rngl_squ_sqrt); [ apply (rngl_le_refl Hor) | ].
  now apply rngl_lt_le_incl.
}
Qed.

(* ... to be simplified *)

Theorem left_or_right_derivable_continuous :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ is_left A lt, (∀ x, ¬ (lt x x)) →
  ∀ {da} (dist : is_dist da) (f : A → T) x a,
  left_or_right_derivative_at is_left lt da rngl_dist f x a
  → left_or_right_continuous_at is_left lt da rngl_dist f x.
Proof.
intros Hic Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hlti * dist * Hd ε Hε.
  rewrite (H1 ε) in Hε.
  now apply rngl_lt_irrefl in Hε.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
intros * Hlti * dist * Hd.
rename x into x₀.
destruct (rngl_eqb_dec a 0) as [Hfz| Hfz]. {
  apply (rngl_eqb_eq Heo) in Hfz.
  subst a.
  specialize left_or_right_derivable_continuous_when_derivative_eq_0 as H1.
  now apply (H1 Hiv _ _ lt Hlti _ dist f).
}
apply (rngl_eqb_neq Heo) in Hfz.
progress unfold left_or_right_derivative_at in Hd.
progress unfold is_limit_when_tending_to_neighbourhood in Hd.
specialize (Hd (rngl_abs a))%L.
assert (Haz : (0 < rngl_abs a)%L) by now apply (rngl_abs_pos Hop Hto).
specialize (Hd Haz).
destruct Hd as (η & Hη & Hd).
intros ε Hε.
exists (rngl_min η (ε / (2 * rngl_abs a)))%L.
split. {
  apply rngl_min_glb_lt; [ easy | ].
  apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
  apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
  now apply (rngl_abs_pos Hop Hto).
}
intros x Hlt Hdxx.
specialize (Hd x Hlt).
apply (rngl_min_glb_lt_iff Hto) in Hdxx.
destruct Hdxx as (H1, H2).
specialize (Hd H1).
assert (Hdz : da x x₀ ≠ 0%L). {
  intros H.
  apply (dist_separation dist) in H.
  subst x.
  now destruct is_left; apply Hlti in Hlt.
}
cbn in Hd |-*.
apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto (da x x₀)) in Hd. 2: {
  clear H.
  apply rngl_le_neq.
  split; [ apply (dist_nonneg Hop Hiv Hto dist) | easy ].
}
rewrite (rngl_dist_mul_distr_r Hiq) in Hd. 2: {
  apply (dist_nonneg Hop Hiv Hto dist).
}
rewrite (rngl_div_mul Hiv) in Hd; [ | easy ].
progress unfold rngl_dist in Hd.
progress unfold rngl_dist.
progress unfold rngl_abs in Hd at 1.
rewrite (rngl_leb_sub_0 Hop Hor) in Hd.
set (σ := (if is_left then 1 else -1)%L) in Hd.
remember (σ * (f x₀ - f x) ≤? a * da x x₀)%L as b eqn:Hb.
symmetry in Hb.
destruct b. {
  apply rngl_leb_le in Hb.
  progress unfold rngl_abs.
  rewrite (rngl_leb_sub_0 Hop Hor).
  remember (f x ≤? f x₀)%L as c eqn:Hc.
  symmetry in Hc.
  destruct c. {
    apply rngl_leb_le in Hc.
    rewrite (rngl_opp_sub_distr Hop).
    destruct (rngl_leb_dec a 0) as [Hflz| Hflz]. {
      apply rngl_leb_le in Hflz.
      destruct is_left. {
        apply (rngl_nle_gt_iff Hto).
        intros Hea.
        apply (rngl_nlt_ge Hor) in Hb.
        apply Hb; clear Hb.
        eapply (rngl_le_lt_trans Hor). {
          apply (rngl_mul_le_mono_pos_r Hop Hiq Hto). {
            apply rngl_le_neq.
            split; [ apply (dist_nonneg Hop Hiv Hto dist) | easy ].
          }
          apply Hflz.
        }
        rewrite (rngl_mul_0_l Hos).
        progress unfold σ.
        rewrite rngl_mul_1_l.
        apply (rngl_lt_0_sub Hop Hor).
        apply rngl_le_neq.
        split; [ easy | ].
        intros H; rewrite H, (rngl_sub_diag Hos) in Hea.
        now apply (rngl_nlt_ge Hor) in Hea.
      } {
        subst σ.
        rewrite (rngl_mul_opp_l Hop) in Hd.
        rewrite rngl_mul_1_l in Hd.
        rewrite (rngl_opp_sub_distr Hop) in Hd.
        rewrite (rngl_sub_opp_r Hop) in Hd.
        apply (rngl_lt_add_lt_sub_l Hop Hor) in Hd.
        rewrite <- (rngl_mul_sub_distr_r Hop) in Hd.
        rewrite (rngl_abs_nonpos_eq Hop Hto) in Hd; [ | easy ].
        rewrite (rngl_abs_nonpos_eq Hop Hto) in H2; [ | easy ].
        eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
        eapply (rngl_le_trans Hor). {
          apply (rngl_mul_le_mono_pos_l Hop Hiq Hto). {
            rewrite <- (rngl_opp_add_distr Hop).
            apply (rngl_opp_pos_neg Hop Hor).
            rewrite <- (rngl_mul_2_l).
            apply (rngl_mul_pos_neg Hop Hiq Hor); [ easy | ].
            now apply rngl_le_neq.
          }
          apply rngl_lt_le_incl, H2.
        }
        rewrite (rngl_mul_2_l).
        rewrite (rngl_add_opp_r Hop).
        rewrite (rngl_mul_comm Hic).
        rewrite (rngl_div_mul Hiv). 2: {
          intros H.
          rewrite <- (rngl_add_opp_r Hop) in H.
          apply (rngl_eq_add_0 Hos Hor) in H. {
            destruct H as (H, _).
            rewrite <- (rngl_opp_0 Hop) in H.
            now apply (rngl_opp_inj Hop) in H.
          } {
            now apply (rngl_opp_nonneg_nonpos Hop Hor).
          } {
            now apply (rngl_opp_nonneg_nonpos Hop Hor).
          }
        }
        apply (rngl_le_refl Hor).
      }
    } {
      apply (rngl_leb_gt_iff Hto) in Hflz.
      destruct is_left. {
        progress unfold σ in Hb.
        rewrite rngl_mul_1_l in Hb.
        eapply (rngl_le_lt_trans Hor); [ apply Hb | ].
        rewrite (rngl_abs_nonneg_eq Hop Hor) in H2. 2: {
          now apply rngl_lt_le_incl.
        }
        eapply (rngl_lt_le_trans Hor). {
          apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto); [ easy | ].
          apply H2.
        }
        rewrite (rngl_mul_comm Hic 2).
        rewrite <- (rngl_div_div Hos Hiv); [ | easy | easy ].
        rewrite (rngl_mul_comm Hic).
        rewrite (rngl_div_mul Hiv); [ | easy ].
        apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
        rewrite (rngl_mul_2_r).
        apply (rngl_le_add_l Hos Hor).
        now apply rngl_lt_le_incl.
      } {
        rewrite (rngl_abs_nonneg_eq Hop Hor) in Hd. 2: {
          now apply rngl_le_neq.
        }
        subst σ.
        rewrite (rngl_mul_opp_l Hop) in Hd.
        rewrite rngl_mul_1_l in Hd.
        rewrite (rngl_opp_sub_distr Hop) in Hd.
        rewrite (rngl_sub_opp_r Hop) in Hd.
        apply (rngl_lt_add_lt_sub_l Hop Hor) in Hd.
        rewrite <- (rngl_mul_sub_distr_r Hop) in Hd.
        rewrite (rngl_sub_diag Hos) in Hd.
        rewrite (rngl_mul_0_l Hos) in Hd.
        apply -> (rngl_lt_sub_0 Hop Hor) in Hd.
        now apply (rngl_nlt_ge Hor) in Hd.
      }
    }
  } {
    apply (rngl_leb_gt_iff Hto) in Hc.
    destruct (rngl_leb_dec a 0) as [Hflz| Hflz]. {
      apply rngl_leb_le in Hflz.
      destruct is_left. {
        rewrite (rngl_abs_nonpos_eq Hop Hto) in Hd; [ | easy ].
        rewrite (rngl_abs_nonpos_eq Hop Hto) in H2; [ | easy ].
        subst σ.
        rewrite rngl_mul_1_l in Hd.
        rewrite (rngl_opp_sub_distr Hop) in Hd.
        rewrite (rngl_sub_sub_distr Hop) in Hd.
        rewrite <- (rngl_add_sub_swap Hop) in Hd.
        rewrite <- (rngl_add_sub_assoc Hop) in Hd.
        apply (rngl_lt_add_lt_sub_l Hop Hor) in Hd.
        rewrite <- (rngl_mul_sub_distr_r Hop) in Hd.
        eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
        eapply (rngl_le_trans Hor). {
          apply (rngl_mul_le_mono_pos_l Hop Hiq Hto). {
            rewrite <- (rngl_opp_add_distr Hop).
            apply (rngl_opp_pos_neg Hop Hor).
            rewrite <- (rngl_mul_2_l).
            apply (rngl_mul_pos_neg Hop Hiq Hor); [ easy | ].
            now apply rngl_le_neq.
          }
          apply rngl_lt_le_incl, H2.
        }
        rewrite (rngl_mul_2_l).
        rewrite (rngl_add_opp_r Hop).
        rewrite (rngl_mul_comm Hic).
        rewrite (rngl_div_mul Hiv). 2: {
          intros H.
          rewrite <- (rngl_add_opp_r Hop) in H.
          apply (rngl_eq_add_0 Hos Hor) in H. {
            destruct H as (H, _).
            rewrite <- (rngl_opp_0 Hop) in H.
            now apply (rngl_opp_inj Hop) in H.
          } {
            now apply (rngl_opp_nonneg_nonpos Hop Hor).
          } {
            now apply (rngl_opp_nonneg_nonpos Hop Hor).
          }
        }
        apply (rngl_le_refl Hor).
      } {
        subst σ.
        rewrite (rngl_mul_opp_l Hop) in Hb.
        rewrite rngl_mul_1_l in Hb.
        rewrite (rngl_opp_sub_distr Hop) in Hb.
        eapply (rngl_le_lt_trans Hor); [ apply Hb | ].
        apply (rngl_le_lt_trans Hor _ 0); [ | easy ].
        apply (rngl_mul_nonpos_nonneg Hop Hor); [ easy | ].
        apply (dist_nonneg Hop Hiv Hto dist).
      }
    } {
      apply (rngl_leb_gt_iff Hto) in Hflz.
      destruct is_left. {
        apply rngl_lt_le_incl in Hflz.
        rewrite (rngl_abs_nonneg_eq Hop Hor) in Hd; [ | easy ].
        subst σ.
        rewrite rngl_mul_1_l in Hd.
        rewrite (rngl_opp_sub_distr Hop) in Hd.
        rewrite (rngl_sub_sub_distr Hop) in Hd.
        rewrite <- (rngl_add_sub_swap Hop) in Hd.
        rewrite <- (rngl_add_sub_assoc Hop) in Hd.
        apply (rngl_lt_add_lt_sub_l Hop Hor) in Hd.
        rewrite <- (rngl_mul_sub_distr_r Hop) in Hd.
        rewrite (rngl_sub_diag Hos) in Hd.
        rewrite (rngl_mul_0_l Hos) in Hd.
        apply -> (rngl_lt_sub_0 Hop Hor) in Hd.
        apply rngl_lt_le_incl in Hd.
        now apply (rngl_nlt_ge Hor) in Hd.
      } {
        subst σ.
        rewrite (rngl_mul_opp_l Hop) in Hb.
        rewrite rngl_mul_1_l in Hb.
        rewrite (rngl_opp_sub_distr Hop) in Hb.
        eapply (rngl_le_lt_trans Hor); [ apply Hb | ].
        rewrite (rngl_abs_nonneg_eq Hop Hor) in H2. 2: {
          now apply rngl_lt_le_incl.
        }
        eapply (rngl_lt_le_trans Hor). {
          apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto); [ easy | ].
          apply H2.
        }
        rewrite (rngl_mul_comm Hic 2).
        rewrite <- (rngl_div_div Hos Hiv); [ | easy | easy ].
        rewrite (rngl_mul_comm Hic).
        rewrite (rngl_div_mul Hiv); [ | easy ].
        apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
        rewrite (rngl_mul_2_r).
        apply (rngl_le_add_l Hos Hor).
        now apply rngl_lt_le_incl.
      }
    }
  }
}
apply (rngl_leb_gt_iff Hto) in Hb.
progress unfold rngl_abs.
rewrite (rngl_leb_sub_0 Hop Hor).
remember (f x ≤? f x₀)%L as c eqn:Hc.
symmetry in Hc.
destruct c. {
  apply rngl_leb_le in Hc.
  rewrite (rngl_opp_sub_distr Hop).
  destruct (rngl_leb_dec a 0) as [Hflz| Hflz]. {
    apply rngl_leb_le in Hflz.
    destruct is_left. {
      subst σ.
      rewrite (rngl_abs_nonpos_eq Hop Hto) in Hd; [ | easy ].
      apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
      rewrite (rngl_mul_opp_l Hop) in Hd.
      rewrite (rngl_add_opp_l Hop) in Hd.
      rewrite (rngl_sub_diag Hos) in Hd.
      rewrite rngl_mul_1_l in Hd.
      apply -> (rngl_lt_sub_0 Hop Hor) in Hd.
      now apply (rngl_nle_gt Hor) in Hd.
    } {
      rewrite <- (rngl_opp_sub_distr Hop) in Hb.
      subst σ.
      rewrite (rngl_mul_opp_l Hop) in Hb.
      rewrite rngl_mul_1_l in Hb.
      rewrite (rngl_opp_sub_distr Hop) in Hb.
      apply (rngl_lt_opp_r Hop Hor) in Hb.
      rewrite rngl_add_comm in Hb.
      apply (rngl_lt_opp_r Hop Hor) in Hb.
      eapply (rngl_lt_le_trans Hor); [ apply Hb | ].
      rewrite <- (rngl_mul_opp_l Hop).
      rewrite <- (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
      rewrite (rngl_mul_comm Hic).
      apply (rngl_le_div_r Hop Hiv Hto); [ easy | ].
      eapply (rngl_le_trans Hor). {
        apply rngl_lt_le_incl, H2.
      }
      rewrite <- (rngl_div_div Hos Hiv); [ | | easy ]. 2: {
        intros H.
        now apply (eq_rngl_abs_0 Hop) in H.
      }
      apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
      rewrite (rngl_mul_2_r).
      apply (rngl_le_add_l Hos Hor).
      apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
      now apply rngl_lt_le_incl.
    }
  } {
    apply (rngl_leb_gt_iff Hto) in Hflz.
    destruct is_left. {
      rewrite (rngl_abs_nonneg_eq Hop Hor) in Hd, H2; cycle 1. {
        now apply rngl_lt_le_incl.
      } {
        now apply rngl_lt_le_incl.
      }
      apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
      rewrite <- (rngl_mul_2_l) in Hd.
      subst σ.
      rewrite rngl_mul_1_l in Hd.
      eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
      rewrite rngl_mul_assoc.
      rewrite (rngl_mul_comm Hic).
      apply (rngl_le_div_r Hop Hiv Hto). {
        now apply (rngl_mul_pos_pos Hop Hiq Hor).
      }
      now apply rngl_lt_le_incl.
    } {
      exfalso.
      apply (rngl_nle_gt Hor) in Hb.
      apply Hb; clear Hb.
      apply (rngl_le_trans Hor _ 0). {
        subst σ.
        rewrite (rngl_mul_opp_l Hop).
        rewrite rngl_mul_1_l.
        rewrite (rngl_opp_sub_distr Hop).
        now apply (rngl_le_sub_0 Hop Hor).
      }
      apply (rngl_mul_nonneg_nonneg Hos Hor).
      now apply rngl_lt_le_incl.
      apply (dist_nonneg Hop Hiv Hto dist).
    }
  }
} {
  destruct is_left. {
    subst σ.
    apply (rngl_leb_gt_iff Hto) in Hc.
    destruct (rngl_leb_dec a 0) as [Hflz| Hflz]. {
      apply rngl_leb_le in Hflz.
      rewrite <- (rngl_opp_sub_distr Hop) in Hb.
      rewrite rngl_mul_1_l in Hb.
      apply (rngl_lt_opp_r Hop Hor) in Hb.
      rewrite rngl_add_comm in Hb.
      apply (rngl_lt_opp_r Hop Hor) in Hb.
      eapply (rngl_lt_le_trans Hor); [ apply Hb | ].
      rewrite <- (rngl_mul_opp_l Hop).
      rewrite <- (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
      rewrite (rngl_mul_comm Hic).
      apply (rngl_le_div_r Hop Hiv Hto); [ easy | ].
      eapply (rngl_le_trans Hor). {
        apply rngl_lt_le_incl, H2.
      }
      rewrite <- (rngl_div_div Hos Hiv); [ | | easy ]. 2: {
        intros H.
        now apply (eq_rngl_abs_0 Hop) in H.
      }
      apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
      rewrite (rngl_mul_2_r).
      apply (rngl_le_add_l Hos Hor).
      apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
      now apply rngl_lt_le_incl.
    } {
      apply (rngl_leb_gt_iff Hto) in Hflz.
      exfalso.
      apply (rngl_nle_gt Hor) in Hb.
      apply Hb; clear Hb.
      apply (rngl_le_trans Hor _ 0). {
        rewrite rngl_mul_1_l.
        apply (rngl_le_sub_0 Hop Hor).
        now apply rngl_lt_le_incl.
      }
      apply (rngl_mul_nonneg_nonneg Hos Hor).
      now apply rngl_lt_le_incl.
      apply (dist_nonneg Hop Hiv Hto dist).
    }
  } {
    apply (rngl_leb_gt_iff Hto) in Hc.
    destruct (rngl_leb_dec a 0) as [Hflz| Hflz]. {
      apply rngl_leb_le in Hflz.
      rewrite (rngl_abs_nonpos_eq Hop Hto) in Hd; [ | easy ].
      apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
      rewrite (rngl_mul_opp_l Hop) in Hd.
      rewrite (rngl_add_opp_l Hop) in Hd.
      rewrite (rngl_sub_diag Hos) in Hd.
      subst σ.
      rewrite (rngl_mul_opp_l Hop) in Hd.
      rewrite rngl_mul_1_l in Hd.
      rewrite (rngl_opp_sub_distr Hop) in Hd.
      apply -> (rngl_lt_sub_0 Hop Hor) in Hd.
      apply rngl_lt_le_incl in Hd.
      now apply (rngl_nle_gt Hor) in Hd.
    } {
      apply (rngl_leb_gt_iff Hto) in Hflz.
      rewrite (rngl_abs_nonneg_eq Hop Hor) in Hd, H2; cycle 1. {
        now apply rngl_lt_le_incl.
      } {
        now apply rngl_lt_le_incl.
      }
      apply (rngl_lt_sub_lt_add_r Hop Hor) in Hd.
      rewrite <- (rngl_mul_2_l) in Hd.
      subst σ.
      rewrite (rngl_mul_opp_l Hop) in Hd.
      rewrite rngl_mul_1_l in Hd.
      rewrite (rngl_opp_sub_distr Hop) in Hd.
      eapply (rngl_lt_le_trans Hor); [ apply Hd | ].
      rewrite rngl_mul_assoc.
      rewrite (rngl_mul_comm Hic).
      apply (rngl_le_div_r Hop Hiv Hto). {
        now apply (rngl_mul_pos_pos Hop Hiq Hor).
      }
      now apply rngl_lt_le_incl.
    }
  }
}
Qed.

Theorem dist_comm : ∀ A (d : distance A) x y, d_dist x y = d_dist y x.
Proof.
intros.
apply dist_symmetry.
now destruct d.
Qed.

(* ... to be simplified
   by grouping cases is_left and not is_left together *)

Theorem left_or_right_derivative_mul_at :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ is_left A lt, (∀ x, ¬ (lt x x)) →
  ∀ {da} (dist : is_dist da) (f g : A → T) u v x₀,
  left_or_right_derivative_at is_left lt da rngl_dist f x₀ u
  → left_or_right_derivative_at is_left lt da rngl_dist g x₀ v
  -> left_or_right_derivative_at is_left lt da rngl_dist
       (λ x : A, (f x * g x)%L) x₀ (f x₀ * v + u * g x₀)%L.
Proof.
intros Hic Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv_and_comm Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hlti * dist * Hf Hg * ε Hε.
  rewrite (H1 ε) in Hε.
  now apply rngl_lt_irrefl in Hε.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_0_le_2 Hos Hto) as Hz2'.
assert (Hz3 : (0 < 3)%L). {
  apply (rngl_lt_le_trans Hor _ 2); [ easy | ].
  apply (rngl_add_le_mono_r Hos Hor).
  apply (rngl_1_le_2 Hos Hto).
}
assert (Hz3' : (0 ≤ 3)%L). {
  apply (rngl_le_trans Hor _ 2); [ easy | ].
  apply (rngl_add_le_mono_r Hos Hor).
  apply (rngl_1_le_2 Hos Hto).
}
intros * Hlti * dist * Hf Hg *.
destruct is_left. {
  apply (is_limit_lt_is_limit_le_iff Hiv).
  intros ε Hε.
  specialize (Hf (ε / (3 * rngl_abs (g x₀) + 1)))%L as H1.
  assert (H : (0 < ε / (3 * rngl_abs (g x₀) + 1))%L). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  specialize (H1 H); clear H.
  specialize (Hg (ε / (3 * rngl_abs (f x₀) + 1)))%L as H2.
  assert (H : (0 < ε / (3 * rngl_abs (f x₀) + 1))%L). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  specialize (H2 H); clear H.
  move Hε before ε.
  destruct H1 as (ηf & Hηf & H1).
  destruct H2 as (ηg & Hηg & H2).
  move ηf before ε.
  move ηg before ηf.
  move Hηg before Hηf.
  specialize (Hg 1%L (rngl_0_lt_1 Hos Hc1 Hto)) as H10.
  destruct H10 as (δ₁ & Hδ₁ & H10).
  cbn in H10.
  progress unfold rngl_dist in H10.
  set (K := (rngl_abs v + 1)%L).
  generalize Hf; intros H11.
  apply (left_or_right_derivable_continuous Hic Hiv) in H11; cycle 1. {
    apply Hlti.
  } {
    easy.
  }
  specialize (H11 (ε / (3 * K))%L).
  assert (H : (0 < ε / (3 * K))%L). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
    progress unfold K.
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  specialize (H11 H); clear H.
  destruct H11 as (δ₂ & Hδ₂ & H11).
  cbn in H11.
  progress unfold rngl_dist in H11.
  exists (rngl_min3 ηf ηg (rngl_min δ₁ δ₂)).
  split. {
    apply rngl_min_glb_lt.
    now apply rngl_min_glb_lt.
    now apply rngl_min_glb_lt.
  }
  intros x Hlt Hd.
  move x before x₀.
  apply (rngl_min_glb_lt_iff Hto) in Hd.
  destruct Hd as (H3, H5).
  apply (rngl_min_glb_lt_iff Hto) in H3, H5.
  destruct H3 as (H3, H4).
  destruct H5 as (H5, H6).
  specialize (H1 x Hlt H3).
  specialize (H2 x Hlt H4).
  cbn.
  rewrite rngl_mul_1_l in H1, H2 |-*.
  assert (Hzd : (0 < da x x₀)%L). {
    apply rngl_le_neq.
    split; [ apply (dist_nonneg Hop Hiv Hto dist) | ].
    cbn; intros H; symmetry in H.
    apply (dist_separation dist) in H.
    subst x.
    now apply Hlti in Hlt.
  }
  assert (Hzed : (0 ≤ da x x₀)%L). {
    apply (dist_nonneg Hop Hiv Hto dist).
  }
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto _ _ _ Hzd) in H1.
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto _ _ _ Hzd) in H2.
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hto _ _ _ Hzd).
  cbn in H1, H2.
  rewrite (rngl_dist_mul_distr_r Hiq _ _ _ Hzed) in H1.
  rewrite (rngl_dist_mul_distr_r Hiq _ _ _ Hzed) in H2.
  rewrite (rngl_dist_mul_distr_r Hiq _ _ _ Hzed).
  rewrite (rngl_div_mul Hiv) in H1. 2: {
    intros H; rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  rewrite (rngl_div_mul Hiv) in H2. 2: {
    intros H; rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  rewrite (rngl_div_mul Hiv). 2: {
    intros H; rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  rewrite rngl_mul_add_distr_r.
  rewrite <- (rngl_add_sub Hos (_ - _) (f x * g x₀)).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  remember (f x₀ - f x)%L as a.
  remember (g x₀ - g x)%L as b.
  rewrite (rngl_add_comm (_ * _ * _)).
  rewrite (rngl_mul_mul_swap Hic u).
  rewrite <- (rngl_mul_assoc (f x₀)).
  rewrite (rngl_mul_comm Hic (f x₀)).
  remember (u * da x x₀)%L as c.
  remember (v * da x x₀)%L as d.
  move x before x₀.
  move a before x; move b before a; move c before b; move d before c.
  move Heqb before Heqa.
  move H1 at bottom.
  move H2 at bottom.
  rewrite (rngl_mul_comm Hic _ b).
  progress unfold rngl_dist.
  progress unfold rngl_dist in H1.
  progress unfold rngl_dist in H2.
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite <- (rngl_add_sub Hos (_ - _) (b  * f x₀)).
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop _ (b * f x₀)).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_sub_sub_distr Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite <- Heqa.
  rewrite (rngl_mul_comm Hic b).
  (* lemma *)
  rewrite <- (rngl_add_opp_r Hop).
  eapply (rngl_le_trans Hor); [ apply (rngl_abs_triangle Hop Hto) | ].
  rewrite (rngl_abs_opp Hop Hto).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_abs_triangle Hop Hto).
  }
  do 2 rewrite (rngl_abs_mul Hop Hiq Hto).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply rngl_lt_le_incl.
    apply H1.
  }
  rewrite (rngl_mul_mul_swap Hic).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_le_trans Hor _ (ε * da x x₀ / 3)). 2: {
      apply (rngl_le_refl Hor).
    }
    rewrite <- (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ _ Hzed).
    apply -> (rngl_le_div_r Hop Hiv Hto); [ | easy ].
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- rngl_mul_assoc.
    rewrite (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_le_div_l Hop Hiv Hto). {
      apply (rngl_add_nonneg_pos Hos Hor).
      apply (rngl_mul_nonneg_nonneg Hos Hor _ _ Hz3').
      apply (rngl_abs_nonneg Hop Hto).
      apply (rngl_0_lt_1 Hos Hc1 Hto).
    }
    apply (rngl_mul_le_mono_nonneg_l Hop Hor).
    now apply rngl_lt_le_incl.
    apply (rngl_le_add_r Hos Hor).
    apply (rngl_0_le_1 Hos Hto).
  }
  rewrite (rngl_add_comm (_ / _)).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply rngl_lt_le_incl.
    apply H2.
  }
  rewrite (rngl_mul_mul_swap Hic).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_le_trans Hor _ (ε * da x x₀ / 3)). 2: {
      apply (rngl_le_refl Hor).
    }
    rewrite <- (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ _ Hzed).
    apply -> (rngl_le_div_r Hop Hiv Hto); [ | easy ].
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- rngl_mul_assoc.
    rewrite (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_le_div_l Hop Hiv Hto). {
      apply (rngl_add_nonneg_pos Hos Hor).
      apply (rngl_mul_nonneg_nonneg Hos Hor _ _ Hz3').
      apply (rngl_abs_nonneg Hop Hto).
      apply (rngl_0_lt_1 Hos Hc1 Hto).
    }
    apply (rngl_mul_le_mono_nonneg_l Hop Hor).
    now apply rngl_lt_le_incl.
    apply (rngl_le_add_r Hos Hor).
    apply (rngl_0_le_1 Hos Hto).
  }
  (* voilà. Mais il reste ce fichu terme rngl_abs (a * b) *)
  rewrite (rngl_abs_mul Hop Hiq Hto).
  set (dx := da x x₀).
  fold dx in H1, H2, H3, H4, H5, H6, Heqc, Heqd, Hzd, Hzed |-*.
  specialize (H10 x Hlt H5).
  specialize (H11 x Hlt H6).
  rewrite rngl_mul_1_l in H10.
  move H10 at bottom.
  move H11 at bottom.
  rewrite <- Heqb in H10.
  rewrite <- (rngl_abs_sub_comm Hop Hto) in H11.
  rewrite <- Heqa in H11.
  progress fold dx in H10.
  assert (Hbk : (rngl_abs b < K * dx)%L). {
    progress unfold K.
    apply (rngl_lt_div_l Hop Hiv Hto); [ easy | ].
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    eapply (rngl_le_lt_trans Hor); [ | apply H10 ].
    apply (rngl_le_sub_le_add_r Hop Hor).
    eapply (rngl_le_trans Hor); [ | apply (rngl_abs_triangle Hop Hto) ].
    rewrite (rngl_sub_add Hop).
    apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
    rewrite <- (rngl_abs_nonneg_eq Hop Hor dx) at 2; [ | easy ].
    rewrite <- (rngl_abs_mul Hop Hiq Hto).
    rewrite (rngl_div_mul Hiv); [ apply (rngl_le_refl Hor) | ].
    intros H.
    rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  assert (H : (rngl_abs a * rngl_abs b < ε * dx / 3)%L). {
    rewrite <- (rngl_div_mul Hiv ε (3 * K))%L. 2: {
      progress unfold K.
      intros H.
      apply (rngl_eq_mul_0_r Hos Hi1) in H. 2: {
        intros H'.
        rewrite H' in Hz3.
        now apply rngl_lt_irrefl in Hz3.
      }
      rewrite <- (rngl_sub_opp_r Hop) in H.
      apply -> (rngl_sub_move_0_r Hop) in H.
      specialize (rngl_abs_nonneg Hop Hto v) as H'.
      rewrite H in H'.
      apply (rngl_nlt_ge Hor) in H'.
      apply H'; clear H'.
      apply (rngl_opp_1_lt_0 Hop Hto Hc1).
    }
    rewrite <- (rngl_mul_div_assoc Hiv).
    rewrite <- rngl_mul_assoc.
    apply (rngl_mul_lt_mono_nonneg Hop Hiq Hto). {
      split; [ | easy ].
      apply (rngl_abs_nonneg Hop Hto).
    }
    rewrite (rngl_mul_comm Hic).
    rewrite rngl_mul_assoc.
    rewrite (rngl_div_mul Hiv). 2: {
      intros H.
      rewrite H in Hz3.
      now apply rngl_lt_irrefl in Hz3.
    }
    rewrite (rngl_mul_comm Hic).
    split; [ | easy ].
    apply (rngl_abs_nonneg Hop Hto).
  }
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_l Hos Hor).
    apply rngl_lt_le_incl, H.
  }
  do 2 rewrite <- (rngl_div_add_distr_r Hiv).
  do 2 rewrite <- rngl_mul_add_distr_r.
  rewrite <- (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  apply (rngl_add_le_mono_r Hos Hor).
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  apply (rngl_le_refl Hor).
} {
  apply (is_limit_lt_is_limit_le_iff Hiv).
  intros ε Hε.
  specialize (Hf (ε / (3 * rngl_abs (g x₀) + 1)))%L as H1.
  assert (H : (0 < ε / (3 * rngl_abs (g x₀) + 1))%L). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  specialize (H1 H); clear H.
  specialize (Hg (ε / (3 * rngl_abs (f x₀) + 1)))%L as H2.
  assert (H : (0 < ε / (3 * rngl_abs (f x₀) + 1))%L). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  specialize (H2 H); clear H.
  move Hε before ε.
  destruct H1 as (ηf & Hηf & H1).
  destruct H2 as (ηg & Hηg & H2).
  move ηf before ε.
  move ηg before ηf.
  move Hηg before Hηf.
  specialize (Hg 1%L (rngl_0_lt_1 Hos Hc1 Hto)) as H10.
  destruct H10 as (δ₁ & Hδ₁ & H10).
  cbn in H10.
  progress unfold rngl_dist in H10.
  set (K := (rngl_abs v + 1)%L).
  generalize Hf; intros H11.
  apply (left_or_right_derivable_continuous Hic Hiv) in H11; cycle 1. {
    apply Hlti.
  } {
    apply dist.
  }
  specialize (H11 (ε / (3 * K))%L).
  assert (H : (0 < ε / (3 * K))%L). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
    progress unfold K.
    apply (rngl_add_nonneg_pos Hos Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  specialize (H11 H); clear H.
  destruct H11 as (δ₂ & Hδ₂ & H11).
  cbn in H11.
  progress unfold rngl_dist in H11.
  exists (rngl_min3 ηf ηg (rngl_min δ₁ δ₂)).
  split. {
    apply rngl_min_glb_lt.
    now apply rngl_min_glb_lt.
    now apply rngl_min_glb_lt.
  }
  intros x Hlt Hd.
  move x before x₀.
  apply (rngl_min_glb_lt_iff Hto) in Hd.
  destruct Hd as (H3, H5).
  apply (rngl_min_glb_lt_iff Hto) in H3, H5.
  destruct H3 as (H3, H4).
  destruct H5 as (H5, H6).
  specialize (H1 x Hlt H3).
  specialize (H2 x Hlt H4).
  rewrite (rngl_mul_opp_l Hop) in H1, H2 |-*.
  rewrite rngl_mul_1_l in H1, H2 |-*.
  rewrite (rngl_opp_sub_distr Hop) in H1, H2 |-*.
  cbn.
  assert (Hzd : (0 < da x x₀)%L). {
    apply rngl_le_neq.
    split; [ now apply (dist_nonneg Hop Hiv Hto) | ].
    cbn; intros H; symmetry in H.
    apply (dist_separation dist) in H.
    subst x.
    now apply Hlti in Hlt.
  }
  assert (Hzed : (0 ≤ da x x₀)%L). {
    now apply (dist_nonneg Hop Hiv Hto).
  }
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto _ _ _ Hzd) in H1.
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto _ _ _ Hzd) in H2.
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hto _ _ _ Hzd).
  cbn in H1, H2.
  rewrite (rngl_dist_mul_distr_r Hiq _ _ _ Hzed) in H1.
  rewrite (rngl_dist_mul_distr_r Hiq _ _ _ Hzed) in H2.
  rewrite (rngl_dist_mul_distr_r Hiq _ _ _ Hzed).
  rewrite (rngl_div_mul Hiv) in H1. 2: {
    intros H; rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  rewrite (rngl_div_mul Hiv) in H2. 2: {
    intros H; rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  rewrite (rngl_div_mul Hiv). 2: {
    intros H; rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  rewrite rngl_mul_add_distr_r.
  rewrite <- (rngl_add_sub Hos (_ - _) (f x * g x₀)).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  remember (f x - f x₀)%L as a.
  remember (g x - g x₀)%L as b.
  rewrite (rngl_add_comm (_ * _ * _)).
  rewrite (rngl_mul_mul_swap Hic u).
  rewrite <- (rngl_mul_assoc (f x₀)).
  rewrite (rngl_mul_comm Hic (f x₀)).
  remember (u * da x x₀)%L as c.
  remember (v * da x x₀)%L as d.
  move x before x₀.
  move a before x; move b before a; move c before b; move d before c.
  move Heqb before Heqa.
  move H1 at bottom.
  move H2 at bottom.
  rewrite (rngl_mul_comm Hic _ b).
  progress unfold rngl_dist.
  progress unfold rngl_dist in H1.
  progress unfold rngl_dist in H2.
  rewrite (rngl_sub_add_distr Hos).
  rewrite (rngl_sub_sub_swap Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite <- (rngl_add_sub Hos (_ - _) (b  * f x₀)).
  rewrite <- (rngl_add_sub_swap Hop (b * f x)).
  rewrite <- (rngl_add_sub_assoc Hop _ (b * f x₀)).
  rewrite <- (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite <- Heqa.
  rewrite (rngl_mul_comm Hic b).
  rewrite rngl_add_comm.
  rewrite (rngl_add_comm (a * b)).
  rewrite rngl_add_assoc.
  (* lemma *)
  eapply (rngl_le_trans Hor); [ apply (rngl_abs_triangle Hop Hto) | ].
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_abs_triangle Hop Hto).
  }
  do 2 rewrite (rngl_abs_mul Hop Hiq Hto).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply rngl_lt_le_incl.
    apply H1.
  }
  rewrite (rngl_mul_mul_swap Hic).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_le_trans Hor _ (ε * da x x₀ / 3)). 2: {
      apply (rngl_le_refl Hor).
    }
    rewrite <- (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ _ Hzed).
    apply -> (rngl_le_div_r Hop Hiv Hto); [ | easy ].
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- rngl_mul_assoc.
    rewrite (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_le_div_l Hop Hiv Hto). {
      apply (rngl_add_nonneg_pos Hos Hor).
      apply (rngl_mul_nonneg_nonneg Hos Hor _ _ Hz3').
      apply (rngl_abs_nonneg Hop Hto).
      apply (rngl_0_lt_1 Hos Hc1 Hto).
    }
    apply (rngl_mul_le_mono_nonneg_l Hop Hor).
    now apply rngl_lt_le_incl.
    apply (rngl_le_add_r Hos Hor).
    apply (rngl_0_le_1 Hos Hto).
  }
  rewrite (rngl_add_comm (_ / _)).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply rngl_lt_le_incl.
    apply H2.
  }
  rewrite (rngl_mul_mul_swap Hic).
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_le_trans Hor _ (ε * da x x₀ / 3)). 2: {
      apply (rngl_le_refl Hor).
    }
    rewrite <- (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ _ Hzed).
    apply -> (rngl_le_div_r Hop Hiv Hto); [ | easy ].
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- rngl_mul_assoc.
    rewrite (rngl_div_mul_mul_div Hic Hiv).
    apply (rngl_le_div_l Hop Hiv Hto). {
      apply (rngl_add_nonneg_pos Hos Hor).
      apply (rngl_mul_nonneg_nonneg Hos Hor _ _ Hz3').
      apply (rngl_abs_nonneg Hop Hto).
      apply (rngl_0_lt_1 Hos Hc1 Hto).
    }
    apply (rngl_mul_le_mono_nonneg_l Hop Hor).
    now apply rngl_lt_le_incl.
    apply (rngl_le_add_r Hos Hor).
    apply (rngl_0_le_1 Hos Hto).
  }
  (* voilà. Mais il reste ce fichu terme rngl_abs (a * b) *)
  rewrite (rngl_abs_mul Hop Hiq Hto).
  set (dx := da x x₀).
  fold dx in H1, H2, H3, H4, H5, H6, Heqc, Heqd, Hzd, Hzed |-*.
  specialize (H10 x Hlt H5).
  specialize (H11 x Hlt H6).
  rewrite (rngl_mul_opp_l Hop) in H10.
  rewrite rngl_mul_1_l in H10.
  rewrite (rngl_opp_sub_distr Hop) in H10.
  move H10 at bottom.
  move H11 at bottom.
  rewrite <- Heqb in H10.
  rewrite <- Heqa in H11.
  progress fold dx in H10.
  assert (Hbk : (rngl_abs b < K * dx)%L). {
    progress unfold K.
    apply (rngl_lt_div_l Hop Hiv Hto); [ easy | ].
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    eapply (rngl_le_lt_trans Hor); [ | apply H10 ].
    apply (rngl_le_sub_le_add_r Hop Hor).
    eapply (rngl_le_trans Hor); [ | apply (rngl_abs_triangle Hop Hto) ].
    rewrite (rngl_sub_add Hop).
    apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
    rewrite <- (rngl_abs_nonneg_eq Hop Hor dx) at 2; [ | easy ].
    rewrite <- (rngl_abs_mul Hop Hiq Hto).
    rewrite (rngl_div_mul Hiv); [ apply (rngl_le_refl Hor) | ].
    intros H.
    rewrite H in Hzd.
    now apply rngl_lt_irrefl in Hzd.
  }
  assert (H : (rngl_abs a * rngl_abs b < ε * dx / 3)%L). {
    rewrite <- (rngl_div_mul Hiv ε (3 * K))%L. 2: {
      progress unfold K.
      intros H.
      apply (rngl_eq_mul_0_r Hos Hi1) in H. 2: {
        intros H'.
        rewrite H' in Hz3.
        now apply rngl_lt_irrefl in Hz3.
      }
      rewrite <- (rngl_sub_opp_r Hop) in H.
      apply -> (rngl_sub_move_0_r Hop) in H.
      specialize (rngl_abs_nonneg Hop Hto v) as H'.
      rewrite H in H'.
      apply (rngl_nlt_ge Hor) in H'.
      apply H'; clear H'.
      apply (rngl_opp_1_lt_0 Hop Hto Hc1).
    }
    rewrite <- (rngl_mul_div_assoc Hiv).
    rewrite <- rngl_mul_assoc.
    apply (rngl_mul_lt_mono_nonneg Hop Hiq Hto). {
      split; [ | easy ].
      apply (rngl_abs_nonneg Hop Hto).
    }
    rewrite (rngl_mul_comm Hic).
    rewrite rngl_mul_assoc.
    rewrite (rngl_div_mul Hiv). 2: {
      intros H.
      rewrite H in Hz3.
      now apply rngl_lt_irrefl in Hz3.
    }
    rewrite (rngl_mul_comm Hic).
    split; [ | easy ].
    apply (rngl_abs_nonneg Hop Hto).
  }
  eapply (rngl_le_trans Hor). {
    apply (rngl_add_le_mono_l Hos Hor).
    apply rngl_lt_le_incl, H.
  }
  do 2 rewrite <- (rngl_div_add_distr_r Hiv).
  do 2 rewrite <- rngl_mul_add_distr_r.
  rewrite <- (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_mul_le_mono_nonneg_r Hop Hor); [ easy | ].
  apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  apply (rngl_add_le_mono_r Hos Hor).
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  apply (rngl_le_refl Hor).
}
Qed.

Theorem left_or_right_continuous_lower_bounded :
  rngl_has_inv T = true →
  ∀ is_left {A} (da : A → A → T) le f x₀,
  left_or_right_continuous_at is_left le da rngl_dist f x₀
  → f x₀ ≠ 0%L
  → ∃ δ,
    (0 < δ)%L ∧ ∀ x,
    (if is_left then le x x₀ else le x₀ x)
    → (da x x₀ < δ)%L
    → (rngl_abs (f x₀) / 2 < rngl_abs (f x))%L.
Proof.
intros Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hlfc Hfzz.
  now rewrite (H1 (f x₀)) in Hfzz.
}
intros * Hlfc Hfzz.
specialize (Hlfc (rngl_abs (f x₀) / 2)%L).
assert (Ha2 : (0 < rngl_abs (f x₀) / 2)%L). {
  apply (rngl_div_pos Hop Hiv Hto). {
    apply (rngl_abs_pos Hop Hto).
    apply Hfzz.
  }
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
specialize (Hlfc Ha2).
destruct Hlfc as (δ & Hδ & H1).
exists δ.
split; [ easy | ].
intros x Hxx Hdxx.
(* bizarre que ce soit si compliqué *)
cbn in H1.
progress unfold rngl_dist in H1.
specialize (H1 x Hxx Hdxx).
specialize (rngl_middle_sub_r Hop Hiv Hto) as H2.
specialize (H2 0 (rngl_abs (f x₀)))%L.
rewrite rngl_add_0_l in H2.
rewrite (rngl_sub_0_r Hos) in H2.
rewrite <- H2.
apply (rngl_lt_sub_lt_add_l Hop Hor).
rewrite rngl_add_comm.
apply (rngl_lt_sub_lt_add_l Hop Hor).
eapply (rngl_le_lt_trans Hor); [ | apply H1 ].
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_abs_sub_comm Hop Hto).
eapply (rngl_le_trans Hor); [ | apply (rngl_abs_triangle Hop Hto) ].
rewrite (rngl_add_sub_assoc Hop).
rewrite rngl_add_comm.
rewrite (rngl_add_sub Hos).
apply (rngl_le_refl Hor).
Qed.

Theorem left_or_right_continuous_upper_bounded :
  rngl_characteristic T ≠ 1 →
  ∀ is_left {A} (da : A → A → T) le f x₀ u,
(*
  left_or_right_continuous_at is_left le da rngl_distance f x₀
*)
  is_limit_when_tending_to_neighbourhood is_left le da rngl_dist f x₀ u
  → ∃ δ M,
    (0 < δ)%L ∧ (0 < M)%L ∧ ∀ x,
    (if is_left then le x x₀ else le x₀ x)
    → (da x x₀ < δ)%L
    → (rngl_abs (f x) < M)%L.
Proof.
intros Hc1.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hlfc.
specialize (Hlfc 1%L).
specialize (rngl_0_lt_1 Hos Hc1 Hto) as H.
specialize (Hlfc H); clear H.
destruct Hlfc as (δ & Hδ & H1).
exists δ, (1 + rngl_abs u)%L.
split; [ easy | ].
split. {
  apply (rngl_lt_0_add Hos Hor).
  apply (rngl_0_lt_1 Hos Hc1 Hto).
  apply (rngl_abs_nonneg Hop Hto).
}
intros x Hxx Hdxx.
specialize (H1 x Hxx Hdxx).
cbn in H1.
progress unfold rngl_dist in H1.
apply (rngl_lt_sub_lt_add_r Hop Hor).
eapply (rngl_le_lt_trans Hor); [ | apply H1 ].
apply (rngl_le_sub_le_add_r Hop Hor).
eapply (rngl_le_trans Hor); [ | apply (rngl_abs_triangle Hop Hto) ].
rewrite (rngl_sub_add Hop).
apply (rngl_le_refl Hor).
Qed.

Theorem left_or_right_continuous_mul_at :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ is_left A le da (f g : A → T) x₀ u v,
  is_limit_when_tending_to_neighbourhood is_left le da rngl_dist f x₀ u
  → is_limit_when_tending_to_neighbourhood is_left le da rngl_dist g x₀ v
  → is_limit_when_tending_to_neighbourhood is_left le da rngl_dist
       (λ x : A, (f x * g x)%L) x₀ (u * v)%L.
Proof.
intros Hic Hiv * Hlfc Hlgc.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros ε Hε.
  rewrite (H1 ε) in Hε.
  now apply rngl_lt_irrefl in Hε.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_0_le_2 Hos Hto) as Hz2'.
intros ε Hε.
specialize (left_or_right_continuous_upper_bounded Hc1) as H50.
specialize (H50 is_left A da le g x₀ _ Hlgc).
destruct H50 as (δ & M & Hδ & HM & H50).
specialize (Hlfc (ε / (2 * M)))%L as H1.
assert (H : (0 < ε / (2 * M))%L). {
  apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
}
specialize (H1 H); clear H.
specialize (Hlgc (ε / (2 * rngl_abs u + 1)))%L as H2.
assert (H : (0 < ε / (2 * rngl_abs u + 1))%L). {
  apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
  apply (rngl_add_nonneg_pos Hos Hor). 2: {
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply (rngl_abs_nonneg Hop Hto).
}
specialize (H2 H); clear H.
cbn in H1, H2 |-*.
progress unfold rngl_dist in H1.
progress unfold rngl_dist in H2.
progress unfold rngl_dist.
destruct H1 as (η₁ & Hη₁ & H1).
destruct H2 as (η₂ & Hη₂ & H2).
exists (rngl_min3 η₁ η₂ δ).
split. {
  apply rngl_min_glb_lt; [ | easy ].
  now apply rngl_min_glb_lt.
}
intros x Hxx Hd.
move x before x₀.
apply (rngl_min_glb_lt_iff Hto) in Hd.
destruct Hd as (H3, H5).
apply (rngl_min_glb_lt_iff Hto) in H3.
destruct H3 as (H3, H4).
rewrite <- (rngl_add_sub Hos (_ - _) (u * g x)).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
rewrite <- (rngl_mul_sub_distr_l Hop).
specialize (H1 x Hxx H3).
specialize (H2 x Hxx H4).
remember (f x - u)%L as a.
remember (g x - v)%L as b.
move b before a.
specialize (H50 x Hxx H5).
eapply (rngl_le_lt_trans Hor). {
  apply (rngl_abs_triangle Hop Hto).
}
do 2 rewrite (rngl_abs_mul Hop Hiq Hto).
eapply (rngl_lt_le_trans Hor). {
  apply (rngl_add_lt_mono_r Hos Hor).
  apply (rngl_mul_lt_mono_nonneg Hop Hiq Hto). {
    split; [ | apply H1 ].
    apply (rngl_abs_nonneg Hop Hto).
  } {
    split; [ | apply H50 ].
    apply (rngl_abs_nonneg Hop Hto).
  }
}
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_l Hos Hor).
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply (rngl_abs_nonneg Hop Hto).
  }
  apply rngl_lt_le_incl, H2.
}
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_r Hos Hor).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite <- (rngl_mul_div_assoc Hiv).
  apply (rngl_le_trans Hor _ (ε * (1 / 2))); [ | apply (rngl_le_refl Hor) ].
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    now apply rngl_lt_le_incl.
  }
  apply (rngl_le_div_l Hop Hiv Hto). {
    now apply (rngl_mul_pos_pos Hop Hiq Hor).
  }
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite rngl_mul_1_l.
  rewrite (rngl_mul_comm Hic 2).
  rewrite (rngl_mul_div Hi1). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  apply (rngl_le_refl Hor).
}
eapply (rngl_le_trans Hor). {
  apply (rngl_add_le_mono_l Hos Hor).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite <- (rngl_mul_div_assoc Hiv).
  apply (rngl_le_trans Hor _ (ε * (1 / 2))); [ | apply (rngl_le_refl Hor) ].
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    now apply rngl_lt_le_incl.
  }
  apply (rngl_le_div_l Hop Hiv Hto). {
    apply (rngl_add_nonneg_pos Hos Hor). 2: {
      apply (rngl_0_lt_1 Hos Hc1 Hto).
    }
    apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
    apply (rngl_abs_nonneg Hop Hto).
  }
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite rngl_mul_1_l.
  rewrite (rngl_div_add_distr_r Hiv).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hi1). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
  apply (rngl_0_le_1 Hos Hto).
}
rewrite <- (rngl_mul_2_l).
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
rewrite (rngl_div_mul Hiv). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite rngl_mul_1_r.
apply (rngl_le_refl Hor).
Qed.

Theorem left_or_right_continuous_inv :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ is_left A le (da : A → A → T) f x₀,
  f x₀ ≠ 0%L
  → left_or_right_continuous_at is_left le da rngl_dist f x₀
  → left_or_right_continuous_at is_left le da rngl_dist
      (λ x, (f x)⁻¹) x₀.
Proof.
intros Hic Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hfzz Hflc.
  intros ε Hε; rewrite H1 in Hε.
  now apply rngl_lt_irrefl in Hε.
}
intros * Hfzz Hlfc.
intros ε Hε.
specialize (left_or_right_continuous_lower_bounded Hiv) as H50.
specialize (H50 is_left A da le f x₀ Hlfc Hfzz).
destruct H50 as (δ & Hδ & H50).
set (M := (rngl_abs (f x₀) / 2)%L) in H50.
assert (HM : (0 < M)%L). {
  apply (rngl_div_pos Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  now apply (rngl_abs_pos Hop Hto).
}
specialize (Hlfc (ε * M²)%L) as H1.
assert (H : (0 < ε * M²)%L). {
  apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
  (* lemma *)
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
}
specialize (H1 H); clear H.
destruct H1 as (η & Hη & H1).
cbn in H1 |-*.
progress unfold rngl_dist in H1.
progress unfold rngl_dist.
exists (rngl_min δ η).
split; [ now apply rngl_min_glb_lt | ].
intros x Hxx Hdxx.
apply (rngl_min_glb_lt_iff Hto) in Hdxx.
destruct Hdxx as (Hdδ, Hdη).
assert (Hfz : f x ≠ 0%L). {
  specialize (H50 x Hxx Hdδ).
  intros H; rewrite H in H50.
  rewrite (rngl_abs_0 Hop) in H50.
  apply rngl_lt_le_incl in H50.
  now apply (rngl_nlt_ge Hor) in H50.
}
move x before x₀.
move Hfz before Hfzz.
move δ before ε.
move η before ε.
move HM before Hδ.
move Hη before Hδ.
rewrite <- (rngl_mul_div Hi1 (f x)⁻¹ (f x₀)); [ | easy ].
rewrite <- (rngl_mul_div Hi1 (f x₀)⁻¹ (f x)); [ | easy ].
do 2 rewrite (rngl_mul_comm Hic _⁻¹).
do 2 rewrite (rngl_mul_inv_r Hiv).
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic).
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_abs_div Hop Hiv Hto). 2: {
  intros H.
  apply (rngl_integral Hos Hio) in H.
  now destruct H.
}
apply (rngl_lt_div_l Hop Hiv Hto). {
  apply (rngl_abs_pos Hop Hto).
  intros H.
  apply (rngl_integral Hos Hio) in H.
  now destruct H.
}
rewrite (rngl_abs_sub_comm Hop Hto).
eapply (rngl_lt_le_trans Hor); [ now apply H1 | ].
apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
  now apply rngl_lt_le_incl.
}
progress unfold rngl_squ.
rewrite (rngl_abs_mul Hop Hiq Hto).
apply (rngl_mul_le_compat_nonneg Hor). {
  split; [ now apply rngl_lt_le_incl | ].
  apply rngl_lt_le_incl.
  now apply H50.
} {
  split; [ now apply rngl_lt_le_incl | ].
  progress unfold M.
  apply (rngl_le_div_l Hop Hiv Hto).
  apply (rngl_0_lt_2 Hos Hc1 Hto).
  rewrite (rngl_mul_2_r).
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_abs_nonneg Hop Hto).
}
Qed.

Theorem rngl_abs_inv :
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (rngl_abs a⁻¹ = (rngl_abs a)⁻¹)%L.
Proof.
intros Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Haz.
do 2 rewrite <- (rngl_div_1_l Hiv).
rewrite (rngl_abs_div Hop Hiv Hto); [ | easy ].
now rewrite (rngl_abs_1 Hos  Hto).
Qed.

Theorem left_or_right_derivative_inv :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ {A} lt is_left (da : A → A → T) f f' x₀,
  f x₀ ≠ 0%L
  → left_or_right_continuous_at is_left lt da rngl_dist f x₀
  → left_or_right_derivative_at is_left lt da rngl_dist f x₀ (f' x₀)
  → left_or_right_derivative_at is_left lt da rngl_dist (λ x : A, (f x)⁻¹)
      x₀ (- f' x₀ / (f x₀)²)%L.
Proof.
intros Hic Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_or_pdiv T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hfzz Hlfc Hlfr ε Hε.
  rewrite H1 in Hε.
  now apply rngl_lt_irrefl in Hε.
}
intros * Hfzz Hlfc Hlfr.
intros ε Hε.
specialize (left_or_right_continuous_lower_bounded Hiv) as H1.
specialize (H1 is_left A da lt f x₀ Hlfc Hfzz).
destruct H1 as (δ & Hδ & H1).
set (M := (rngl_abs (f x₀) / 2)%L) in H1.
assert (HM : (0 < M)%L). {
  apply (rngl_div_pos Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  now apply (rngl_abs_pos Hop Hto).
}
assert (Hem : (0 < ε * M² / 2)%L). {
  apply (rngl_div_pos Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_mul_pos_pos Hop Hiq Hor); [ easy | ].
  (* lemma *)
  now apply (rngl_mul_pos_pos Hop Hiq Hor).
}
specialize (Hlfr _ Hem).
destruct Hlfr as (η & Hη & H3).
cbn in H3.
progress unfold rngl_dist in H3.
set (ε' := (ε * M / (2 * (rngl_abs (f' x₀) * ((f x₀)⁻¹)² + 1)))%L).
specialize (Hlfc ε') as H4.
assert (H : (0 < ε')%L). {
  progress unfold ε'.
  apply (rngl_div_pos Hop Hiv Hto). {
    now apply (rngl_mul_pos_pos Hop Hiq Hor).
  }
  apply (rngl_mul_pos_pos Hop Hiq Hor). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_add_nonneg_pos Hos Hor). 2: {
    apply (rngl_0_lt_1 Hos Hc1 Hto).
  }
  apply (rngl_mul_nonneg_nonneg Hos Hor). {
    apply (rngl_abs_nonneg Hop Hto).
  }
  apply (rngl_squ_nonneg Hos Hto).
}
specialize (H4 H); clear H.
destruct H4 as (δ' & Hδ' & H4).
cbn in H4 |-*.
progress unfold rngl_dist in H4.
progress unfold rngl_dist.
exists (rngl_min3 η δ δ').
split. {
  apply rngl_min_glb_lt; [ | easy ].
  now apply rngl_min_glb_lt.
}
intros x Hxx Hdxx.
apply (rngl_min_glb_lt_iff Hto) in Hdxx.
destruct Hdxx as (Hdη, Hdδ').
apply (rngl_min_glb_lt_iff Hto) in Hdη.
destruct Hdη as (Hdη, Hdδ).
move x before x₀.
move δ before ε.
move η before ε.
move HM before Hδ.
move Hη before Hδ.
assert (Hfz : f x ≠ 0%L). {
  specialize (H1 x Hxx Hdδ).
  intros H; rewrite H in H1.
  rewrite (rngl_abs_0 Hop) in H1.
  apply rngl_lt_le_incl in H1.
  now apply (rngl_nlt_ge Hor) in H1.
}
specialize (H3 x Hxx Hdη).
rewrite (rngl_abs_sub_comm Hop Hto).
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_opp_sub_swap Hop).
(* lemma? *)
rewrite <- (rngl_mul_div Hi1 (f x)⁻¹ (f x₀)); [ | easy ].
rewrite <- (rngl_mul_div Hi1 (f x₀)⁻¹ (f x)); [ | easy ].
do 2 rewrite (rngl_mul_comm Hic _⁻¹).
do 2 rewrite (rngl_mul_inv_r Hiv).
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic (f x)).
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite <- (rngl_div_opp_l Hop Hiv).
rewrite <- (rngl_mul_opp_r Hop).
rewrite <- (rngl_div_opp_l Hop Hiv).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_div_div_swap Hic Hiv).
rewrite <- (rngl_sub_add Hop (_ / _ / _) (f' x₀ / (f x₀ * f x))).
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite <- (rngl_add_sub_assoc Hop).
eapply (rngl_le_lt_trans Hor). {
  apply (rngl_abs_triangle Hop Hto).
}
rewrite (rngl_abs_div Hop Hiv Hto). 2: {
  intros H.
  apply (rngl_integral Hos Hio) in H.
  now destruct H.
}
eapply (rngl_le_lt_trans Hor). {
  apply (rngl_add_le_mono_r Hos Hor).
  apply -> (rngl_le_div_l Hop Hiv Hto). 2: {
    apply (rngl_abs_pos Hop Hto).
    intros H.
    apply (rngl_integral Hos Hio) in H.
    now destruct H.
  }
  eapply (rngl_le_trans Hor). {
    apply rngl_lt_le_incl, H3.
  }
  rewrite <- (rngl_div_mul_mul_div Hic Hiv).
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hto). {
    apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_abs_mul Hop Hiq Hto).
  progress unfold rngl_squ.
  apply (rngl_mul_le_compat_nonneg Hor). {
    split; [ now apply rngl_lt_le_incl | ].
    progress unfold M.
    apply (rngl_le_div_l Hop Hiv Hto).
    apply (rngl_0_lt_2 Hos Hc1 Hto).
    rewrite (rngl_mul_2_r).
    apply (rngl_le_add_l Hos Hor).
    apply (rngl_abs_nonneg Hop Hto).
  } {
    split; [ now apply rngl_lt_le_incl | ].
    now apply rngl_lt_le_incl, H1.
  }
}
apply (rngl_lt_add_lt_sub_l Hop Hor).
specialize (rngl_middle_sub_r Hop Hiv Hto 0 ε) as H.
rewrite rngl_add_0_l in H.
rewrite (rngl_sub_0_r Hos) in H.
rewrite H; clear H.
do 2 rewrite <- (rngl_mul_inv_r Hiv (f' x₀)).
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite (rngl_inv_mul_distr Hos Hiv); [ | easy | easy ].
rewrite <- (rngl_squ_inv Hos Hiv); [ | easy ].
progress unfold rngl_squ.
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_mul_swap Hic).
rewrite <- (rngl_div_1_l Hiv) at 2.
rewrite <- (rngl_div_1_l Hiv (f x)).
rewrite <- (rngl_div_mul Hiv (1 / f x₀) (f x)); [ | easy ].
rewrite <- (rngl_div_mul Hiv (1 / f x) (f x₀)); [ | easy ].
rewrite (rngl_mul_comm Hic _ (f x₀)).
rewrite (rngl_mul_comm Hic _ (f x)).
rewrite (rngl_div_div_swap Hic Hiv).
rewrite <- (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic).
rewrite (rngl_div_1_l Hiv).
rewrite <- (rngl_mul_inv_r Hiv _ (f x)).
rewrite rngl_mul_assoc.
rewrite (rngl_mul_comm Hic _ (f x)⁻¹).
rewrite <- (rngl_mul_assoc (f' x₀)).
rewrite fold_rngl_squ.
rewrite rngl_mul_assoc.
rewrite (rngl_abs_mul Hop Hiq Hto).
rewrite (rngl_abs_sub_comm Hop Hto).
destruct (rngl_eqb_dec (f' x₀) 0) as [Hf'z| Hf'z]. {
  apply (rngl_eqb_eq Heo) in Hf'z.
  rewrite Hf'z.
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_abs_0 Hop).
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_div_pos Hop Hiv Hto); [ easy | ].
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (rngl_eqb_neq Heo) in Hf'z.
eapply (rngl_le_lt_trans Hor). {
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hto). 2: {
    now apply rngl_lt_le_incl, H4.
  }
  apply (rngl_abs_pos Hop Hto).
  intros H.
  apply (rngl_integral Hos Hio) in H.
  destruct H as [H| H]. {
    apply (rngl_integral Hos Hio) in H.
    destruct H as [H| H]; [ | easy ].
    now apply (rngl_inv_neq_0 Hos Hiv) in H.
  }
  apply (eq_rngl_squ_0 Hos Hio) in H.
  now apply (rngl_inv_neq_0 Hos Hiv) in H.
}
progress unfold ε'.
rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_mul_comm Hic).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite <- (rngl_mul_inv_r Hiv _ 2).
apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto); [ easy | ].
rewrite <- (rngl_div_1_l Hiv 2).
rewrite <- (rngl_div_div Hos Hiv); cycle 1. {
  intros H.
  apply (rngl_eq_add_0 Hos Hor) in H; cycle 1. {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_squ_nonneg Hos Hto).
  } {
    apply (rngl_0_le_1 Hos Hto).
  }
  destruct H as (_, H).
  now apply (rngl_1_eq_0_iff Hos) in H.
} {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
apply (rngl_div_lt_mono_pos_r Hop Hiv Hto). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (rngl_lt_div_l Hop Hiv Hto). {
  apply (rngl_add_nonneg_pos Hos Hor). {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply (rngl_abs_nonneg Hop Hto).
    apply (rngl_squ_nonneg Hos Hto).
  }
  apply (rngl_0_lt_1 Hos Hc1 Hto).
}
rewrite rngl_mul_1_l.
do 2 rewrite (rngl_abs_mul Hop Hiq Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor _²). 2: {
  apply (rngl_squ_nonneg Hos Hto).
}
rewrite (rngl_mul_comm Hic).
rewrite (rngl_mul_comm Hic (rngl_abs (f x)⁻¹)).
do 2 rewrite <- rngl_mul_assoc.
assert (H : (rngl_abs (f x)⁻¹ * M < 1)%L). {
  rewrite (rngl_abs_inv Hiv); [ | apply Hfz ].
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_lt_div_l Hop Hiv Hto). {
    apply (rngl_abs_pos Hop Hto), Hfz.
  }
  rewrite rngl_mul_1_l.
  now apply H1.
}
eapply (rngl_lt_le_trans Hor). {
  rewrite rngl_mul_assoc.
  apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto); [ | apply H ].
  apply (rngl_mul_pos_pos Hop Hiq Hor). {
    now apply (rngl_abs_pos Hop Hto).
  }
  apply rngl_le_neq.
  split; [ apply (rngl_squ_nonneg Hos Hto) | ].
  symmetry.
  intros H'.
  apply (eq_rngl_squ_0 Hos Hio) in H'.
  now apply (rngl_inv_neq_0 Hos Hiv) in H'.
}
rewrite rngl_mul_1_r.
apply (rngl_le_sub_le_add_l Hop Hor).
rewrite (rngl_sub_diag Hos).
apply (rngl_0_le_1 Hos Hto).
Qed.

(* *)

Theorem derivative_mul_at :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ A lt, (∀ x, ¬ (lt x x)) →
  ∀ {da} (dist : is_dist da) (f g : A → T) f' g' x₀,
  is_derivative_at lt da rngl_dist f f' x₀
  → is_derivative_at lt da rngl_dist g g' x₀
  → is_derivative_at lt da rngl_dist (λ x : A, (f x * g x)%L)
       (λ x, f x * g' x + f' x * g x)%L x₀.
Proof.
intros Hic Hiv * Hlt * dist * Hf Hg.
destruct Hf as (Hlfc & Hrfc & Hlfr & Hrfr).
destruct Hg as (Hlgc & Hrgc & Hlgr & Hrgr).
split; [ now apply (left_or_right_continuous_mul_at Hic Hiv) | ].
split; [ now apply (left_or_right_continuous_mul_at Hic Hiv) | ].
split. {
  now apply (left_or_right_derivative_mul_at Hic Hiv).
} {
  now apply (left_or_right_derivative_mul_at Hic Hiv).
}
Qed.

Theorem derivative_mul :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ A lt, (∀ x, ¬ (lt x x)) →
  ∀ {da} (dist : is_dist da) (f g : A → T) f' g',
  is_derivative lt da rngl_dist f f'
  → is_derivative lt da rngl_dist g g'
  → is_derivative lt da rngl_dist (λ x : A, (f x * g x)%L)
       (λ x, f x * g' x + f' x * g x)%L.
Proof.
intros Hic Hiv * Hlt * dist * Hf Hg x₀.
now apply (derivative_mul_at Hic Hiv).
Qed.

Theorem derivative_inv_at :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ A lt, (∀ x, ¬ (lt x x)) →
  ∀ da (f : A → T) f' x₀,
  f x₀ ≠ 0%L
  → is_derivative_at lt da rngl_dist f f' x₀
  → is_derivative_at lt da rngl_dist (λ x : A, (f x)⁻¹)
       (λ x, (- f' x / rngl_squ (f x))%L) x₀.
Proof.
intros Hic Hiv.
intros * Hlt * Hfz Hf.
destruct Hf as (Hlfc & Hrfc & Hlfr & Hrfr).
split; [ now apply (left_or_right_continuous_inv Hic Hiv) | ].
split; [ now apply (left_or_right_continuous_inv Hic Hiv) | ].
split. {
  apply (left_or_right_derivative_inv Hic Hiv lt); [ easy | | easy ].
  eapply (is_limit_neighbourhood_eq_compat _ f); [ easy | | apply Hlfc ].
  now intros; left.
} {
  apply (left_or_right_derivative_inv Hic Hiv lt); [ easy | | easy ].
  eapply (is_limit_neighbourhood_eq_compat _ f); [ easy | | apply Hrfc ].
  now intros; left.
}
Qed.

End a.
