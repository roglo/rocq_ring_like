(** * Div

Theorems about division in ring-like structures.

Division can be either:
- multiplication by the inverse ([ab⁻¹]) or
- partial division (with the property [ab/b=a]).

See module [[RingLike.Core]] explaining that.

Some of the theorems below require one or several properties:
- [rngl_has_inv T = true] : that inversion ([x⁻¹]) exists,
- [rngl_mul_is_comm T = true] : that the multiplication is commutative,
- [rngl_has_1 T = true] : that [1] exists,
- [rngl_characteristic T = 0] : that the characteristics is [0],
- [rngl_characteristic T ≠ 1] : that the characteristics [≠ 1],
- [rngl_has_opp_or_psub T = true] : that opposite or partial subtraction
  exists,
- [rngl_has_inv_and_1_or_pdiv T = true] : that inversion or partial
  division exists.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

In general, it is not necessary to import the present module. The normal
usage is to do:
<<
    Require Import RingLike.Core.
>>
which imports the present module and some other ones.
 *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
Require Import Structures.
Require Import Add.
Require Import Mul.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_mul_inv_diag_l :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L.
Proof.
intros Hon Hiv *.
specialize rngl_opt_mul_inv_diag_l as H.
rewrite Hiv, Hon in H.
apply H.
Qed.

Theorem rngl_mul_inv_diag_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a : T, a ≠ 0%L → (a * a⁻¹ = 1)%L.
Proof.
intros Hon Hiv * Haz.
specialize rngl_opt_mul_inv_diag_r as rngl_mul_inv_diag_r.
unfold rngl_div in rngl_mul_inv_diag_r.
rewrite Hiv in rngl_mul_inv_diag_r; cbn in rngl_mul_inv_diag_r.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic. {
  rewrite (rngl_mul_comm Hic).
  now apply (rngl_mul_inv_diag_l Hon Hiv).
}
cbn in rngl_mul_inv_diag_r.
rewrite Hon in rngl_mul_inv_diag_r.
now apply rngl_mul_inv_diag_r.
Qed.

Theorem rngl_mul_inv_r :
  rngl_has_inv T = true →
  ∀ a b, (a * b⁻¹)%L = (a / b)%L.
Proof.
intros Hin *.
now unfold rngl_div; rewrite Hin.
Qed.

Theorem rngl_div_diag :
  rngl_has_1 T = true →
  rngl_has_inv_or_pdiv T = true →
  ∀ a : T, a ≠ 0%L → (a / a = 1)%L.
Proof.
intros Hon Hiq * Haz.
remember (rngl_has_inv T) as ai eqn:Hai; symmetry in Hai.
destruct ai. {
  remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
  destruct ic. {
    unfold rngl_div; rewrite Hai.
    rewrite rngl_mul_comm; [ | easy ].
    now apply rngl_mul_inv_diag_l.
  }
  specialize rngl_opt_mul_inv_diag_r as rngl_mul_inv_diag_r.
  rewrite Hai, Hon, Hic in rngl_mul_inv_diag_r; cbn in rngl_mul_inv_diag_r.
  progress unfold rngl_div; rewrite Hai.
  now apply rngl_mul_inv_diag_r.
}
remember (rngl_has_pdiv T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize rngl_opt_mul_div as H1.
  rewrite Hqu in H1.
  specialize (H1 1%L a Haz).
  now rewrite rngl_mul_1_l in H1.
}
apply rngl_has_inv_or_pdiv_iff in Hiq.
destruct Hiq; congruence.
Qed.

Theorem rngl_mul_div :
  rngl_has_inv_and_1_or_pdiv T = true →
  ∀ a b : T, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros Hii a b Hbz.
progress unfold rngl_has_inv_and_1_or_pdiv in Hii.
apply Bool.orb_true_iff in Hii.
destruct Hii as [Hii| Hqu]. {
  apply Bool.andb_true_iff in Hii.
  destruct Hii as (Hiv, Hon).
  specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_inv_r Hiv).
  rewrite (rngl_div_diag Hon Hiq); [ | easy ].
  apply (rngl_mul_1_r Hon).
} {
  specialize rngl_opt_mul_div as H1.
  rewrite Hqu in H1.
  now apply H1.
}
Qed.

Theorem rngl_mul_cancel_l :
  rngl_has_inv_and_1_or_pdiv_and_comm T = true →
  ∀ a b c, a ≠ 0%L
  → (a * b = a * c)%L
  → b = c.
Proof.
intros Hii * Haz Habc.
progress unfold rngl_has_inv_and_1_or_pdiv_and_comm in Hii.
apply Bool.orb_true_iff in Hii.
destruct Hii as [Hii| Hii]. {
  apply Bool.andb_true_iff in Hii.
  destruct Hii as (Hiv, Hon).
  apply (f_equal (λ x, rngl_mul (a⁻¹)%L x)) in Habc.
  do 2 rewrite rngl_mul_assoc in Habc.
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in Habc; [ | easy ].
  now do 2 rewrite (rngl_mul_1_l Hon) in Habc.
} {
  apply Bool.andb_true_iff in Hii.
  destruct Hii as (Hqu, Hic).
  apply (f_equal (λ x, rngl_div x a)) in Habc.
  do 2 rewrite (rngl_mul_comm Hic a) in Habc.
  specialize rngl_opt_mul_div as H1.
  rewrite Hqu in H1.
  rewrite H1 in Habc; [ | easy ].
  rewrite H1 in Habc; [ | easy ].
  easy.
}
Qed.

Theorem rngl_mul_cancel_r :
  rngl_has_inv_and_1_or_pdiv T = true →
  ∀ a b c, c ≠ 0%L
  → (a * c = b * c)%L
  → a = b.
Proof.
intros Hii * Hcz Hab.
assert (H : (a * c / c = b * c / c)%L) by now rewrite Hab.
rewrite (rngl_mul_div Hii) in H; [ | easy ].
rewrite (rngl_mul_div Hii) in H; [ | easy ].
easy.
Qed.

Theorem rngl_div_mul_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c, (a / b * c = a * c / b)%L.
Proof.
intros Hic Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_mul_swap Hic).
Qed.

Theorem rngl_mul_div_r :
  rngl_mul_is_comm T = true →
  rngl_has_inv_and_1_or_pdiv T = true →
  ∀ a b : T, a ≠ 0%L → (a * b / a)%L = b.
Proof.
intros Hic Hii a b Hbz.
rewrite (rngl_mul_comm Hic).
now apply (rngl_mul_div Hii).
Qed.

Theorem rngl_div_0_l :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv_and_1_or_pdiv T = true →
  ∀ a, a ≠ 0%L → (0 / a)%L = 0%L.
Proof.
intros Hos Hiv * Haz.
remember (0 / a)%L as x eqn:Hx.
replace 0%L with (0 * a)%L in Hx. 2: {
  now apply rngl_mul_0_l.
}
subst x.
apply (rngl_mul_div Hiv _ _ Haz).
Qed.

Theorem rngl_div_mul :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b, b ≠ 0%L → (a / b * b)%L = a.
Proof.
intros Hon Hiv * Hbz.
unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv _ Hbz).
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_div_div_swap :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c,
  (a / b / c = a / c / b)%L.
Proof.
intros Hic Hin *.
progress unfold rngl_div.
now rewrite Hin, rngl_mul_mul_swap.
Qed.

Theorem rngl_div_div_mul_mul :
  rngl_has_1 T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a b c d,
  b ≠ 0%L
  → d ≠ 0%L
  → (a / b = c / d)%L ↔ (a * d = b * c)%L.
Proof.
intros Hon Hic Hiv * Hbz Hdz.
split. {
  intros Habcd.
  apply (f_equal (λ x, rngl_mul x b)) in Habcd.
  rewrite rngl_div_mul in Habcd; [ | easy | easy | easy ].
  apply (f_equal (λ x, rngl_mul x d)) in Habcd.
  rewrite (rngl_mul_comm Hic _ b) in Habcd.
  rewrite <- rngl_mul_assoc in Habcd.
  now rewrite rngl_div_mul in Habcd.
} {
  intros Habcd.
  apply (f_equal (λ x, rngl_div x d)) in Habcd.
  specialize (rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv) as Hi1.
  rewrite rngl_mul_div in Habcd; [ | easy | easy ].
  apply (f_equal (λ x, rngl_div x b)) in Habcd.
  rewrite rngl_div_div_swap in Habcd; [ | easy | easy ].
  rewrite rngl_mul_comm in Habcd; [ | easy ].
  rewrite rngl_mul_div in Habcd; [ easy | easy | easy ].
}
Qed.

Theorem rngl_eq_mul_0_l :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv_or_pdiv T = true →
  ∀ a b, (a * b = 0)%L → b ≠ 0%L → a = 0%L.
Proof.
intros Hon Hos Hiq.
specialize (rngl_has_1_has_inv_or_pdiv_has_inv_and_1_or_pdiv Hon Hiq) as Hii.
intros * Hab Hbz.
remember (rngl_has_inv T) as iv eqn:Hiv; symmetry in Hiv.
destruct iv. {
  apply (f_equal (λ x, (x * b⁻¹)%L)) in Hab.
  rewrite <- rngl_mul_assoc in Hab.
  rewrite (rngl_mul_inv_diag_r Hon Hiv) in Hab; [ | easy ].
  rewrite (rngl_mul_1_r Hon) in Hab; rewrite Hab.
  apply (rngl_mul_0_l Hos).
}
remember (rngl_has_pdiv T) as qu eqn:Hqu; symmetry in Hqu.
destruct qu. {
  specialize (rngl_mul_div Hii a b Hbz) as H1.
  rewrite Hab in H1.
  now rewrite rngl_div_0_l in H1.
}
apply rngl_has_inv_and_1_or_pdiv_iff in Hii.
rewrite Hiv, Hqu in Hii.
now destruct Hii.
Qed.

Theorem rngl_eq_mul_0_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv_or_pdiv_and_comm T = true →
  ∀ a b, (a * b = 0)%L → a ≠ 0%L → b = 0%L.
Proof.
intros Hon Hos Hiq * Hab Haz.
progress unfold rngl_has_inv_or_pdiv_and_comm in Hiq.
apply Bool.orb_true_iff in Hiq.
destruct Hiq as [Hiv | Hiq]. {
  apply (f_equal (λ x, (a⁻¹ * x)%L)) in Hab.
  rewrite rngl_mul_assoc in Hab.
  rewrite (rngl_mul_inv_diag_l Hon Hiv) in Hab; [ | easy ].
  rewrite (rngl_mul_1_l Hon) in Hab; rewrite Hab.
  apply (rngl_mul_0_r Hos).
} {
  apply Bool.andb_true_iff in Hiq.
  destruct Hiq as (Hqu, Hic).
  specialize (rngl_has_pdiv_has_inv_and_1_or_pdiv Hqu) as Hii.
  specialize (rngl_mul_div Hii b a Haz) as H1.
  rewrite (rngl_mul_comm Hic) in H1.
  rewrite Hab in H1.
  now rewrite rngl_div_0_l in H1.
}
Qed.

Theorem rngl_div_add_distr_r:
  rngl_has_inv T = true →
  ∀ a b c, ((a + b) / c)%L = (a / c + b / c)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply rngl_mul_add_distr_r.
Qed.

Theorem rngl_div_sub_distr_r:
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b c, ((a - b) / c)%L = (a / c - b / c)%L.
Proof.
intros Hop Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_sub_distr_r Hop).
Qed.

Theorem rngl_inv_1 :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  rngl_has_opp_or_psub T = true ∨ rngl_characteristic T ≠ 1 →
  (1⁻¹ = 1)%L.
Proof.
intros Hon Hiv Hosc1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  destruct Hosc1 as [Hos| ]; [ | easy ].
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 1%L).
  apply H1.
}
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_div_diag Hon) as H.
unfold rngl_div in H.
rewrite Hiv in H.
transitivity (1 * 1⁻¹)%L. {
  symmetry.
  apply (rngl_mul_1_l Hon).
}
apply H; [ easy | ].
now apply (rngl_1_neq_0_iff Hon).
Qed.

Theorem rngl_div_1_l :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a, (1 / a = a⁻¹)%L.
Proof.
intros Hon Hiv *.
unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_div_1_r :
  rngl_has_1 T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_has_opp_or_psub T = true ∨ rngl_characteristic T ≠ 1 →
  ∀ a, (a / 1 = a)%L.
Proof.
intros Hon Hiq Hosc1 *.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  destruct Hosc1 as [Hos| ]; [ | easy ].
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite (H1 a).
  apply H1.
}
assert (Hi1 : rngl_has_inv_and_1_or_pdiv T = true). {
  apply rngl_has_inv_or_pdiv_iff in Hiq.
  apply rngl_has_inv_and_1_or_pdiv_iff.
  now destruct Hiq; [ left | right ].
}
specialize (rngl_mul_div Hi1 a 1%L) as H1.
rewrite (rngl_mul_1_r Hon) in H1.
now apply H1, rngl_1_neq_0_iff.
Qed.

Theorem rngl_mul_div_assoc :
  rngl_has_inv T = true →
  ∀ a b c, (a * (b / c) = a * b / c)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply rngl_mul_assoc.
Qed.

Theorem rngl_div_compat_l :
  rngl_has_inv T = true →
  ∀ a b c, c ≠ 0%L → (a = b)%L → (a / c = b / c)%L.
Proof.
intros Hin a b c Hcz Hab.
now rewrite Hab.
Qed.

Theorem rngl_inv_if_then_else_distr : ∀ (c : bool) a b,
  ((if c then a else b)⁻¹ = if c then a⁻¹ else b⁻¹)%L.
Proof. now destruct c. Qed.

Theorem rngl_mul_move_1_r :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ a b : T, b ≠ 0%L → (a * b)%L = 1%L ↔ a = (b⁻¹)%L.
Proof.
intros Hon Hiv * Hbz.
split; intros H. {
  apply rngl_div_compat_l with (c := b) in H; [ | easy | easy ].
  unfold rngl_div in H.
  rewrite Hiv in H.
  rewrite <- rngl_mul_assoc in H.
  rewrite (rngl_mul_inv_r Hiv) in H.
  rewrite (rngl_div_diag Hon) in H; [ | | easy ]. 2: {
    now apply rngl_has_inv_or_pdiv_iff; left.
  }
  now rewrite rngl_mul_1_r, rngl_mul_1_l in H.
} {
  rewrite H.
  specialize (rngl_mul_inv_diag_l Hon Hiv) as H1.
  now apply H1.
}
Qed.

Theorem rngl_mul_move_l :
  rngl_mul_is_comm T = true →
  rngl_has_inv_and_1_or_pdiv T = true →
  ∀ a b c, a ≠ 0%L → (a * b)%L = c → b = (c / a)%L.
Proof.
intros Hic Hi1 * Haz Hab.
subst c; symmetry.
rewrite (rngl_mul_comm Hic).
now apply (rngl_mul_div Hi1).
Qed.

Theorem rngl_mul_move_r :
  rngl_has_inv_and_1_or_pdiv T = true →
  ∀ a b c, b ≠ 0%L → (a * b)%L = c → a = (c / b)%L.
Proof.
intros Hi1 * Hcz Ha.
subst c; symmetry.
now apply (rngl_mul_div Hi1).
Qed.

Theorem rngl_inv_neq_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (a⁻¹ ≠ 0)%L.
Proof.
intros Hon Hom Hiv * Haz H1.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  now specialize (rngl_characteristic_1 Hon Hom Hch a).
}
apply Nat.eqb_neq in Hch.
symmetry in H1.
apply (rngl_mul_move_1_r Hon Hiv _ _ Haz) in H1.
rewrite (rngl_mul_0_l Hom) in H1.
symmetry in H1.
now apply rngl_1_neq_0_iff in H1.
Qed.

Theorem rngl_inv_involutive :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ x, x ≠ 0%L → (x⁻¹⁻¹)%L = x.
Proof.
intros Hon Hos Hiv * Hxz.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  exfalso; apply Hxz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat.eqb_neq in Hch.
symmetry.
specialize (rngl_div_diag Hon) as div_diag.
unfold rngl_div in div_diag.
rewrite Hiv in div_diag.
specialize (rngl_mul_move_1_r Hon Hiv) as H1.
apply H1. 2: {
  rewrite rngl_mul_inv_r; [ | easy ].
  unfold rngl_div; rewrite Hiv.
  apply div_diag; [ | easy ].
  now apply rngl_has_inv_or_pdiv_iff; left.
}
now apply rngl_inv_neq_0.
Qed.

Theorem rngl_inv_inj :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →(a⁻¹ = b⁻¹)%L → a = b.
Proof.
intros Hon Hom Hiv * Haz Hbz H.
rewrite <- (rngl_inv_involutive Hon Hom Hiv a); [ | easy ].
rewrite H.
now apply rngl_inv_involutive.
Qed.

Theorem rngl_inv_mul_distr :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a b, a ≠ 0%L → b ≠ 0%L →((a * b)⁻¹ = b⁻¹ * a⁻¹)%L.
Proof.
intros Hon Hos Hiv * Haz Hbz.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_1_inv_has_inv_and_1_or_pdiv_and_comm Hon Hiv) as Hi1.
specialize (rngl_div_diag Hon Hiq) as H1.
specialize (rngl_eq_mul_0_l Hon Hos Hiq) as H2.
unfold rngl_div in H1.
rewrite Hiv in H1.
assert (Habz : (a * b)%L ≠ 0%L). {
  intros H.
  now specialize (H2 a b H Hbz).
}
apply (rngl_mul_cancel_l Hi1 (a * b)%L _ _ Habz).
rewrite (H1 _ Habz).
rewrite rngl_mul_assoc.
rewrite <- (rngl_mul_assoc a).
rewrite (H1 _ Hbz).
rewrite (rngl_mul_1_r Hon).
now symmetry; apply H1.
Qed.

Theorem rngl_div_div :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a b c, (b ≠ 0 → c ≠ 0 → a / b / c = a / (c * b))%L.
Proof.
intros Hon Hos Hiv * Hbz Hzc.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc; f_equal; symmetry.
now apply (rngl_inv_mul_distr Hon Hos Hiv).
Qed.

Theorem rngl_div_div_r :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a b c,
  b ≠ 0%L
  → c ≠ 0%L
  → (a / (b / c) = a * c / b)%L.
Proof.
intros Hon Hos Hiv * Hbz Hcz.
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_inv_mul_distr Hon Hos Hiv); [ | easy | ]. 2: {
  now apply (rngl_inv_neq_0 Hon Hos Hiv).
}
rewrite (rngl_inv_involutive Hon Hos Hiv); [ | easy ].
apply rngl_mul_assoc.
Qed.

Theorem rngl_opp_inv :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a, a ≠ 0%L → (- a⁻¹ = (- a)⁻¹)%L.
Proof.
intros Hon Hop Hiv * Haz.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_1_inv_has_inv_and_1_or_pdiv_and_comm Hon Hiv) as Hi1.
remember (Nat.eqb (rngl_characteristic T) 1) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  exfalso; apply Haz.
  apply (rngl_characteristic_1 Hon Hos Hch).
}
apply Nat.eqb_neq in Hch.
assert (Hoaz : (- a)%L ≠ 0%L). {
  intros H.
  apply (f_equal rngl_opp) in H.
  rewrite rngl_opp_involutive in H; [ | easy ].
  now rewrite rngl_opp_0 in H.
}
apply (rngl_mul_cancel_l Hi1 (- a)%L); [ easy | ].
specialize (rngl_opt_mul_inv_diag_r) as H2.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
rewrite Hon, Hiv in H2; cbn in H2.
rewrite rngl_mul_opp_opp; [ | easy ].
destruct ic. {
  symmetry.
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_inv_diag_l; [ | easy | easy | easy ].
  easy.
} {
  rewrite H2; [ now rewrite H2 | easy ].
}
Qed.

Theorem rngl_div_mul_div :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  ∀ x y z, y ≠ 0%L → ((x / y) * (y / z))%L = (x / z)%L.
Proof.
intros Hon Hiv * Hs.
unfold rngl_div; rewrite Hiv.
rewrite rngl_mul_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_inv_diag_l; [ | easy| easy | easy ].
apply (rngl_mul_1_r Hon).
Qed.

Theorem eq_rngl_div_1 :
  rngl_has_1 T = true →
  rngl_has_inv_or_pdiv T = true →
   ∀ a b, b ≠ 0%L → a = b → (a / b = 1)%L.
Proof.
intros Hon Hiv * Hbz Hab.
subst a.
apply (rngl_div_diag Hon Hiv _ Hbz).
Qed.

Theorem eq_rngl_add_same_0 :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_characteristic T = 0 →
  ∀ a,
  (a + a = 0)%L
  → a = 0%L.
Proof.
intros Hon Hos Hiq Hch * Haa.
rewrite <- (rngl_mul_2_r Hon) in Haa.
apply (rngl_eq_mul_0_l Hon Hos Hiq) in Haa; [ easy | ].
specialize (rngl_characteristic_0 Hon Hch 1) as H1.
cbn in H1.
now rewrite rngl_add_0_r in H1.
Qed.

Theorem rngl_pow_nonzero :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv_or_pdiv T = true →
  ∀ a n, (a ≠ 0 → a ^ n ≠ 0)%L.
Proof.
intros Hon Hos Hiq * Haz.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  now rewrite (H1 a) in Haz.
}
induction n; [ now apply (rngl_1_neq_0_iff Hon) | cbn ].
intros H1; apply IHn.
now apply (rngl_eq_mul_0_l Hon Hos Hiq) in H1.
Qed.

Theorem rngl_squ_inv :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a, (a ≠ 0 → (a⁻¹)² = (a²)⁻¹)%L.
Proof.
intros Hon Hos Hiv * Haz.
progress unfold rngl_squ.
now rewrite (rngl_inv_mul_distr Hon Hos Hiv).
Qed.

Theorem rngl_squ_div :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ a b, b ≠ 0%L → (a / b)²%L = (a² / b²)%L.
Proof.
intros Hic Hon Hos Hiv * Hbz.
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_squ_mul Hic).
progress f_equal.
now apply (rngl_squ_inv Hon Hos Hiv).
Qed.

Theorem rngl_div_opp_l :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b, (- a / b = - (a / b))%L.
Proof.
intros Hop Hiv *.
progress unfold rngl_div.
rewrite Hiv.
apply (rngl_mul_opp_l Hop).
Qed.

Theorem rngl_div_opp_opp :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b, (b ≠ 0 → - a / - b = a / b)%L.
Proof.
intros Hon Hop Hiv.
intros * Hbz.
rewrite <- (rngl_mul_inv_r Hiv).
rewrite <- (rngl_opp_inv Hon Hop Hiv); [ | easy ].
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_mul_inv_r Hiv).
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_inv_pow :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  ∀ x n, x ≠ 0%L → ((x ^ n)⁻¹ = x⁻¹ ^ n)%L.
Proof.
intros Hon Hos Hiv.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hxz.
induction n; [ now apply (rngl_inv_1 Hon Hiv); left | ].
rewrite rngl_pow_succ_r.
rewrite (rngl_pow_succ_l Hon).
rewrite (rngl_inv_mul_distr Hon Hos Hiv); [ | easy | ]. 2: {
  now apply (rngl_pow_nonzero Hon Hos Hiq).
}
now progress f_equal.
Qed.

End a.

Arguments rngl_div_add_distr_r {T ro rp} Hiv (a b c)%_L.
Arguments rngl_div_diag {T ro rp} Hon Hiq a%_L.
Arguments rngl_div_mul {T ro rp} Hon Hiv (a b)%_L.
Arguments rngl_div_opp_opp {T ro rp} Hon Hop Hiv (a b)%_L.
Arguments rngl_div_1_l {T ro rp} Hon Hiv a%_L.
Arguments rngl_mul_cancel_r {T ro rp} Hi1 (a b c)%_L.
Arguments rngl_mul_div {T ro rp} Hiv (a b)%_L.
Arguments rngl_mul_inv_r {T ro} Hiv (a b)%_L.
