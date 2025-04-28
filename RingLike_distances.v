(* distances and limits *)

From Stdlib Require Import Utf8 Arith.

Require Import RingLike_structures.
Require Import RingLike_order.
Require Import RingLike_add.
Require Import RingLike_mul.
Require Import RingLike_div.
Require Import RingLike_add_with_order.
Require Import RingLike_mul_with_order.
Require Import RingLike_div_with_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

(* distances *)

Record is_dist {A} (dist : A → A → T) :=
  { dist_symmetry : ∀ a b, dist a b = dist b a;
    dist_separation : ∀ a b, dist a b = 0%L ↔ a = b;
    dist_triangular : ∀ a b c, (dist a c ≤ dist a b + dist b c)%L }.

Class distance A :=
  { d_dist : A → A → T;
    d_prop : is_dist d_dist }.

Arguments d_dist {A distance} a b.

Definition rngl_dist a b := rngl_abs (a - b)%L.

Theorem rngl_dist_is_dist :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  is_dist rngl_dist.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
progress unfold rngl_dist.
split. {
  intros.
  apply (rngl_abs_sub_comm Hop Hor).
} {
  intros.
  split; intros Hab. {
    apply (eq_rngl_abs_0 Hop) in Hab.
    now apply -> (rngl_sub_move_0_r Hop) in Hab.
  }
  subst b.
  rewrite (rngl_sub_diag Hos).
  apply (rngl_abs_0 Hop).
} {
  intros.
  specialize (rngl_abs_triangle Hop Hor) as H1.
  specialize (H1 (a - b) (b - c))%L.
  rewrite (rngl_add_sub_assoc Hop) in H1.
  now rewrite (rngl_sub_add Hop) in H1.
}
Qed.

Definition rngl_distance Hop Hor :=
  {| d_dist := rngl_dist; d_prop := rngl_dist_is_dist Hop Hor |}.

(* limits *)

Definition is_limit_when_seq_tends_to_inf {A} (dist : distance A) u L :=
  ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n → (d_dist (u n) L < ε)%L.

Definition is_limit_when_tending_to_neighbourhood (is_left : bool) {A B}
  (lt : A → A → Prop)
  (da : distance A) (db : distance B) (f : A → B) (x₀ : A) (L : B) :=
  (∀ ε : T, 0 < ε →
   ∃ η : T, (0 < η)%L ∧ ∀ x : A,
   (if is_left then lt x x₀ else lt x₀ x)
   → d_dist x x₀ < η
   → d_dist (f x) L < ε)%L.

(* Cauchy sequences and completeness *)

Definition is_Cauchy_sequence {A} (dist : distance A) (u : nat → A) :=
  ∀ ε : T, (0 < ε)%L →
  ∃ N : nat, ∀ p q : nat, N ≤ p → N ≤ q → (d_dist (u p) (u q) < ε)%L.

Definition is_complete A (dist : distance A) :=
  ∀ u, is_Cauchy_sequence dist u
  → ∃ c, is_limit_when_seq_tends_to_inf dist u c.

(* continuity *)

Definition left_or_right_continuous_at (is_left : bool) {A B} le
    da db (f : A → B) a :=
  is_limit_when_tending_to_neighbourhood is_left le da db f a (f a).

Definition left_continuous_at {A B} :=
  @left_or_right_continuous_at true A B.
Definition right_continuous_at {A B} :=
  @left_or_right_continuous_at false A B.

Definition is_continuous {A B} lt da db (f : A → B) :=
  ∀ a, left_continuous_at lt da db f a ∧ right_continuous_at lt da db f a.

(* derivability *)

Definition left_or_right_derivative_at (is_left : bool) {A} lt
    (da : distance A) (db : distance T) f a a' :=
  let σ := (if is_left then 1 else -1)%L in
  let g x := (σ * (f a - f x) / d_dist x a)%L in
  is_limit_when_tending_to_neighbourhood is_left lt da db g a a'.

Definition left_derivative_at {A} := @left_or_right_derivative_at true A.
Definition right_derivative_at {A} := @left_or_right_derivative_at false A.

Definition is_derivative_at {A} lt
  (da : distance A) (db : distance T) f f' a :=
  let le x y := lt x y ∨ x = y in
  left_continuous_at le da db f a ∧
  right_continuous_at le da db f a ∧
  left_derivative_at lt da db f a (f' a) ∧
  right_derivative_at lt da db f a (f' a).

Definition is_derivative {A} lt (da : distance A) (db : distance T) f f' :=
  ∀ a, is_derivative_at lt da db f f' a.

(* properties of distances and limits *)

Theorem dist_refl :
  ∀ A (dist : A → A → T) (Hid : is_dist dist) a, dist a a = 0%L.
Proof.
intros * Hid *.
destruct Hid as (Hdsym, Hdsep, Hdtri).
apply (proj2 (Hdsep a a) eq_refl).
Qed.

Theorem dist_diag : ∀ {A} (dist : distance A) a, d_dist a a = 0%L.
Proof.
intros.
destruct dist.
now apply dist_separation.
Qed.

Theorem dist_nonneg :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ {A} (dist : distance A) a b, (0 ≤ d_dist a b)%L.
Proof.
intros Hon Hop Hiv Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
destruct dist as (dist, (Hdsym, Hdsep, Hdtri)).
specialize (proj2 (Hdsep a a) eq_refl) as H1.
specialize (Hdtri a b a) as H2.
rewrite H1, (Hdsym b a) in H2.
rewrite <- (rngl_mul_2_l Hon) in H2.
replace 0%L with (2 * 0)%L in H2 by apply (rngl_mul_0_r Hos).
apply (rngl_mul_le_mono_pos_l Hop Hor Hii) in H2; [ easy | ].
apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
Qed.

Theorem rngl_limit_interv :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ (dist : distance T),
  (∀ x y z, (x ≤ y ≤ z → d_dist x y ≤ d_dist x z)%L)
  → (∀ x y z, (x ≤ y ≤ z → d_dist y z ≤ d_dist x z)%L)
  → ∀ u a b c,
  (∀ i, (a ≤ u i ≤ b)%L)
  → is_limit_when_seq_tends_to_inf dist u c
  → (a ≤ c ≤ b)%L.
Proof.
intros Hon Hop Hiv Hor.
intros * mono_1 mono_2 * Hi Hlim.
progress unfold is_limit_when_seq_tends_to_inf in Hlim.
split. {
  apply (rngl_nlt_ge_iff Hor).
  intros Hca.
  specialize (Hlim (d_dist a c))%L.
  assert (H : (0 < d_dist a c)%L). {
    apply (rngl_lt_iff Hor).
    split; [ apply (dist_nonneg Hon Hop Hiv Hor) | ].
    intros H; symmetry in H.
    apply -> (dist_separation _ d_prop) in H.
    subst c.
    now apply (rngl_lt_irrefl Hor) in Hca.
  }
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  specialize (Hi N) as H.
  apply rngl_nle_gt in HN.
  apply HN; clear HN.
  do 2 rewrite (dist_symmetry _ d_prop _ c).
  apply mono_1.
  split; [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  apply (rngl_nlt_ge_iff Hor).
  intros Hbc.
  specialize (Hlim (d_dist b c))%L.
  assert (H : (0 < d_dist b c)%L). {
    apply (rngl_lt_iff Hor).
    split; [ apply (dist_nonneg Hon Hop Hiv Hor) | ].
    intros H; symmetry in H.
    apply -> (dist_separation _ d_prop) in H.
    subst c.
    now apply (rngl_lt_irrefl Hor) in Hbc.
  }
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  specialize (Hi N).
  apply rngl_nle_gt in HN.
  apply HN; clear HN.
  apply mono_2.
  split; [ easy | ].
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem limit_unique :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ A (dist : distance A) u lim1 lim2,
  is_limit_when_seq_tends_to_inf dist u lim1
  → is_limit_when_seq_tends_to_inf dist u lim2
  → lim1 = lim2.
Proof.
intros Hon Hop Hiv Hor * Hu1 Hu2.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  destruct dist as (d, (Hdsym, Hdsep, Hdtri)).
  assert (H : ∀ a b : A, a = b) by now intros; apply Hdsep, H1.
  apply H.
}
specialize (dist_nonneg Hon Hop Hiv Hor dist) as Hdpos.
assert (Hu : is_limit_when_seq_tends_to_inf dist (λ _, lim1) lim2). {
  intros ε Hε.
  assert (Hε2 : (0 < ε / 2)%L). {
    apply (rngl_mul_lt_mono_pos_r Hop Hor Hii) with (a := 2%L). {
      apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_div_mul Hon Hiv); [ easy | ].
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  specialize (Hu1 (ε / 2) Hε2)%L.
  specialize (Hu2 (ε / 2) Hε2)%L.
  destruct Hu1 as (N1, Hu1).
  destruct Hu2 as (N2, Hu2).
  exists (max N1 N2).
  intros n HN.
  destruct dist as (dist, (Hdsym, Hdsep, Hdtri)).
  eapply (rngl_le_lt_trans Hor); [ apply (Hdtri _ (u n)) | ].
  rewrite Hdsym.
  replace ε with (ε / 2 + ε / 2)%L. 2: {
    apply (rngl_mul_cancel_r Hi1 _ _ 2%L). {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    rewrite rngl_mul_add_distr_r.
    rewrite (rngl_div_mul Hon Hiv). 2: {
      apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
    }
    symmetry.
    apply (rngl_mul_2_r Hon).
  }
  apply (rngl_add_lt_compat Hop Hor). {
    apply Hu1.
    eapply Nat.le_trans; [ | apply HN ].
    apply Nat.le_max_l.
  } {
    apply Hu2.
    eapply Nat.le_trans; [ | apply HN ].
    apply Nat.le_max_r.
  }
}
assert (H : ∀ ε : T, (0 < ε)%L → (d_dist lim1 lim2 < ε)%L). {
  intros ε Hε.
  specialize (Hu ε Hε).
  destruct Hu as (N, HN).
  now apply (HN N).
}
clear Hu; rename H into Hu.
destruct dist as (dist, (Hdsym, Hdsep, Hdtri)).
apply Hdsep.
apply (rngl_abs_le_ε Hon Hop Hiv Hor).
intros ε Hε.
specialize (Hu ε Hε).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | apply Hdpos ].
apply (rngl_lt_le_incl Hor).
eapply (rngl_le_lt_trans Hor); [ | apply Hu ].
apply (rngl_le_refl Hor).
Qed.

Theorem limit_add :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ dist,
  (∀ a b c d, (d_dist (a + b) (c + d) ≤ d_dist a c + d_dist b d)%L)
  → ∀ u v limu limv,
  is_limit_when_seq_tends_to_inf dist u limu
  → is_limit_when_seq_tends_to_inf dist v limv
  → is_limit_when_seq_tends_to_inf dist (λ n, (u n + v n))%L (limu + limv)%L.
Proof.
intros Hon Hop Hiv Hor * Hd * Hu Hv ε Hε.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_int_dom_or_inv_1_quo Hiv Hon) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_mul_lt_mono_pos_r Hop Hor Hii 2⁻¹%L) in Hε. 2: {
    apply (rngl_0_lt_inv_compat Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hon Hos Hc1 Hor).
  }
  rewrite (rngl_mul_0_l Hos) in Hε.
  now rewrite (rngl_mul_inv_r Hiv) in Hε.
}
destruct (Hu (ε / 2) Hε2)%L as (Nu, Hun).
destruct (Hv (ε / 2) Hε2)%L as (Nv, Hvn).
move Nv before Nu.
exists (max Nu Nv).
intros n H.
apply Nat.max_lub_iff in H.
destruct H as (Hnun, Hnvn).
specialize (Hun _ Hnun).
specialize (Hvn _ Hnvn).
apply (rngl_lt_le_trans Hor _ (ε / 2 + ε / 2)%L). 2: {
  rewrite <- (rngl_mul_2_r Hon).
  rewrite (rngl_div_mul Hon Hiv). 2: {
    apply (rngl_2_neq_0 Hon Hos Hc1 Hor).
  }
  apply (rngl_le_refl Hor).
}
eapply (rngl_le_lt_trans Hor). 2: {
  apply (rngl_add_lt_compat Hop Hor); [ apply Hun | apply Hvn ].
}
apply Hd.
Qed.

Theorem rngl_dist_add_add_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d,
  (rngl_dist (a + b) (c + d) ≤ rngl_dist a c + rngl_dist b d)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
progress unfold rngl_dist.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
apply (rngl_abs_triangle Hop Hor).
Qed.

Theorem rngl_dist_left_mono :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c,
  (a ≤ b ≤ c)%L
  → (rngl_dist a b ≤ rngl_dist a c)%L.
Proof.
intros Hop Hor.
intros * Habc.
progress unfold rngl_dist.
rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
  now apply (rngl_le_sub_0 Hop Hor).
}
rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
  apply (rngl_le_sub_0 Hop Hor).
  now apply (rngl_le_trans Hor _ b).
}
do 2 rewrite (rngl_opp_sub_distr Hop).
now apply (rngl_sub_le_mono_r Hop Hor).
Qed.

Theorem rngl_dist_right_mono :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c,
  (a ≤ b ≤ c)%L
  → (rngl_dist b c ≤ rngl_dist a c)%L.
Proof.
intros Hop Hor.
intros * Habc.
progress unfold rngl_dist.
rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
  now apply (rngl_le_sub_0 Hop Hor).
}
rewrite (rngl_abs_nonpos_eq Hop Hor). 2: {
  apply (rngl_le_sub_0 Hop Hor).
  now apply (rngl_le_trans Hor _ b).
}
do 2 rewrite (rngl_opp_sub_distr Hop).
now apply (rngl_sub_le_mono_l Hop Hor).
Qed.

Theorem is_limit_neighbourhood_eq_compat :
  ∀ is_left {A B} (f g : A → B) lt₁ lt₂ da db a u,
  (∀ x, f x = g x)
  → (∀ x y, lt₂ x y → lt₁ x y)
  → is_limit_when_tending_to_neighbourhood is_left lt₁ da db f a u
  → is_limit_when_tending_to_neighbourhood is_left lt₂ da db g a u.
Proof.
intros * Hfg Hlti Hf.
intros x₀ Hx.
specialize (Hf x₀ Hx).
destruct Hf as (η & Hη & Hf).
exists η.
split; [ easy | ].
intros x Hlt Hxa.
rewrite <- Hfg.
apply Hf; [ | easy ].
now destruct is_left; apply Hlti.
Qed.

Theorem is_derivative_at_eq_compat :
  ∀ {A} (f f' g g' : A → T) lt da db a,
  (∀ x, f x = g x)
  → (∀ x, f' x = g' x)
  → is_derivative_at lt da db f f' a
  → is_derivative_at lt da db g g' a.
Proof.
intros * Hfg Hf'g' Hff.
destruct Hff as (H1 & H2 & H3 & H4).
set (lt' := λ x y, lt x y ∨ x = y).
split. {
  apply (is_limit_neighbourhood_eq_compat _ f _ lt'); [ easy | easy | ].
  now rewrite <- Hfg.
}
split. {
  apply (is_limit_neighbourhood_eq_compat _ f _ lt'); [ easy | easy | ].
  now rewrite <- Hfg.
}
split. {
  rewrite <- Hf'g'.
  eapply (is_limit_neighbourhood_eq_compat _ _ _ lt); [ | easy | apply H3 ].
  intros x.
  now do 2 rewrite Hfg.
} {
  rewrite <- Hf'g'.
  eapply (is_limit_neighbourhood_eq_compat _ _ _ lt); [ | easy | apply H4 ].
  intros x.
  now do 2 rewrite Hfg.
}
Qed.

End a.

Arguments rngl_dist {T ro} (a b)%_L.
