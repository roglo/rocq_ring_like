(** * Distances

Definitions and theorems about distances and limits. Also
include the notions of continuity and derivability.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

In general, it is not necessary to import the present module. The
normal usage is to do:
<<
    Require Import RingLike.Core.
>>
which imports the present module and some other ones.
 *)

Require Import Stdlib.Arith.Arith.

Require Import Utf8 Structures Order Add Mul Div.
Require Import Add_with_order Mul_with_order Div_with_order.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

(** ** Properties of distances *)

Record is_dist {A} (da : A → A → T) :=
  { dist_symmetry : ∀ a b, da a b = da b a;
    dist_separation : ∀ a b, da a b = 0%L ↔ a = b;
    dist_triangular : ∀ a b c, (da a c ≤ da a b + da b c)%L }.

Class distance A :=
  { d_dist : A → A → T;
    d_prop : is_dist d_dist }.

End a.

Arguments d_dist {T ro A distance} a b.
Arguments dist_separation {T ro A da} dist a b : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition rngl_dist a b := rngl_abs (a - b)%L.

Theorem rngl_dist_is_dist :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  is_dist rngl_dist.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
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

(** ** Limits *)

Definition is_limit_when_seq_tends_to_inf {A} (da : A → A → T) u L :=
  ∀ ε, (0 < ε)%L → ∃ N, ∀ n, N ≤ n → (da (u n) L < ε)%L.

Definition is_limit_when_tending_to_neighbourhood (is_left : bool) {A B}
  (lt : A → A → Prop)
  (da : A → A → T) (db : B → B → T) (f : A → B) (x₀ : A) (L : B) :=
  (∀ ε : T, 0 < ε →
   ∃ η : T, (0 < η)%L ∧ ∀ x : A,
   (if is_left then lt x x₀ else lt x₀ x)
   → da x x₀ < η
   → db (f x) L < ε)%L.

(** ** Cauchy sequences and completeness *)

Definition is_Cauchy_sequence {A} (da : A → A → T) (u : nat → A) :=
  ∀ ε : T, (0 < ε)%L →
  ∃ N : nat, ∀ p q : nat, N ≤ p → N ≤ q → (da (u p) (u q) < ε)%L.

Definition is_complete A (da : A → A → T) :=
  ∀ u, is_Cauchy_sequence da u
  → ∃ c, is_limit_when_seq_tends_to_inf da u c.

(** ** Continuity *)

Definition left_or_right_continuous_at (is_left : bool) {A B} le
    da db (f : A → B) a :=
  is_limit_when_tending_to_neighbourhood is_left le da db f a (f a).

Definition left_continuous_at {A B} :=
  @left_or_right_continuous_at true A B.
Definition right_continuous_at {A B} :=
  @left_or_right_continuous_at false A B.

Definition is_continuous {A B} lt da db (f : A → B) :=
  ∀ a, left_continuous_at lt da db f a ∧ right_continuous_at lt da db f a.

(** ** Derivability *)

Definition left_or_right_derivative_at (is_left : bool) {A} lt
    (da : A → A → T) (db : T → T → T) f a a' :=
  let σ := (if is_left then 1 else -1)%L in
  let g x := (σ * (f a - f x) / da x a)%L in
  is_limit_when_tending_to_neighbourhood is_left lt da db g a a'.

Definition left_derivative_at {A} := @left_or_right_derivative_at true A.
Definition right_derivative_at {A} := @left_or_right_derivative_at false A.

Definition is_derivative_at {A} lt
  (da : A → A → T) (db : T → T → T) f f' a :=
  let le x y := lt x y ∨ x = y in
  left_continuous_at le da db f a ∧
  right_continuous_at le da db f a ∧
  left_derivative_at lt da db f a (f' a) ∧
  right_derivative_at lt da db f a (f' a).

Definition is_derivative {A} lt (da : A → A → T) (db : T → T → T) f f' :=
  ∀ a, is_derivative_at lt da db f f' a.

(** ** Properties of distances and limits *)

Theorem dist_refl :
  ∀ A (dist : A → A → T) (Hid : is_dist dist) a, dist a a = 0%L.
Proof.
intros * Hid *.
destruct Hid as (Hdsym, Hdsep, Hdtri).
apply (proj2 (Hdsep a a) eq_refl).
Qed.

Theorem dist_diag : ∀ {A} {da : A → A → T} (dist : is_dist da) a,
  da a a = 0%L.
Proof.
intros.
destruct dist.
now apply dist_separation.
Qed.

Theorem dist_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ {A} {da : A → A → T} (dist : is_dist da) a b, (0 ≤ da a b)%L.
Proof.
intros Hop Hiv Hor * dist *.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
destruct dist as (Hdsym, Hdsep, Hdtri).
specialize (proj2 (Hdsep a a) eq_refl) as H1.
specialize (Hdtri a b a) as H2.
rewrite H1, (Hdsym b a) in H2.
rewrite <- (rngl_mul_2_l) in H2.
replace 0%L with (2 * 0)%L in H2 by apply (rngl_mul_0_r Hos).
apply (rngl_mul_le_mono_pos_l Hop Hiq Hor) in H2; [ easy | ].
apply (rngl_0_lt_2 Hos Hc1 Hor).
Qed.

Theorem rngl_limit_interv :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ {dt : T → T → T} (dist : is_dist dt),
  (∀ x y z, (x ≤ y ≤ z → dt x y ≤ dt x z)%L)
  → (∀ x y z, (x ≤ y ≤ z → dt y z ≤ dt x z)%L)
  → ∀ u a b c,
  (∀ i, (a ≤ u i ≤ b)%L)
  → is_limit_when_seq_tends_to_inf dt u c
  → (a ≤ c ≤ b)%L.
Proof.
intros Hop Hiv Hor.
intros * dist mono_1 mono_2 * Hi Hlim.
progress unfold is_limit_when_seq_tends_to_inf in Hlim.
split. {
  apply (rngl_nlt_ge_iff Hto).
  intros Hca.
  specialize (Hlim (dt a c))%L.
  assert (H : (0 < dt a c)%L). {
    apply (rngl_le_neq Hto).
    split; [ apply (dist_nonneg Hop Hiv Hor dist) | ].
    intros H; symmetry in H.
    apply -> (dist_separation dist) in H.
    subst c.
    now apply (rngl_lt_irrefl Hor) in Hca.
  }
  specialize (Hlim H); clear H.
  destruct Hlim as (N, HN).
  specialize (HN N (Nat.le_refl _)).
  specialize (Hi N) as H.
  apply rngl_nle_gt in HN.
  apply HN; clear HN.
  do 2 rewrite (dist_symmetry _ dist _ c).
  apply mono_1.
  split; [ | easy ].
  now apply (rngl_lt_le_incl Hto).
} {
  apply (rngl_nlt_ge_iff Hto).
  intros Hbc.
  specialize (Hlim (dt b c))%L.
  assert (H : (0 < dt b c)%L). {
    apply (rngl_le_neq Hto).
    split; [ apply (dist_nonneg Hop Hiv Hor dist) | ].
    intros H; symmetry in H.
    apply -> (dist_separation dist) in H.
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
  now apply (rngl_lt_le_incl Hto).
}
Qed.

Theorem limit_unique :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ {A} {da : A → A → T} (dist : is_dist da) u lim1 lim2,
  is_limit_when_seq_tends_to_inf da u lim1
  → is_limit_when_seq_tends_to_inf da u lim2
  → lim1 = lim2.
Proof.
intros Hop Hiv Hor * dist * Hu1 Hu2.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  destruct dist as (Hdsym, Hdsep, Hdtri).
  assert (H : ∀ a b : A, a = b) by now intros; apply Hdsep, H1.
  apply H.
}
specialize (dist_nonneg Hop Hiv Hor dist) as Hdpos.
assert (Hu : is_limit_when_seq_tends_to_inf da (λ _, lim1) lim2). {
  intros ε Hε.
  assert (Hε2 : (0 < ε / 2)%L). {
    apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor) with (a := 2%L). {
      apply (rngl_0_lt_2 Hos Hc1 Hor).
    }
    rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_div_mul Hiv); [ easy | ].
    apply (rngl_2_neq_0 Hos Hc1 Hor).
  }
  specialize (Hu1 (ε / 2) Hε2)%L.
  specialize (Hu2 (ε / 2) Hε2)%L.
  destruct Hu1 as (N1, Hu1).
  destruct Hu2 as (N2, Hu2).
  exists (max N1 N2).
  intros n HN.
  destruct dist as (Hdsym, Hdsep, Hdtri).
  eapply (rngl_le_lt_trans Hto); [ apply (Hdtri _ (u n)) | ].
  rewrite Hdsym.
  replace ε with (ε / 2 + ε / 2)%L. 2: {
    apply (rngl_mul_cancel_r Hi1 _ _ 2%L). {
      apply (rngl_2_neq_0 Hos Hc1 Hor).
    }
    rewrite rngl_mul_add_distr_r.
    rewrite (rngl_div_mul Hiv). 2: {
      apply (rngl_2_neq_0 Hos Hc1 Hor).
    }
    symmetry.
    apply (rngl_mul_2_r).
  }
  apply (rngl_add_lt_compat Hos Hor). {
    apply Hu1.
    eapply Nat.le_trans; [ | apply HN ].
    apply Nat.le_max_l.
  } {
    apply Hu2.
    eapply Nat.le_trans; [ | apply HN ].
    apply Nat.le_max_r.
  }
}
assert (H : ∀ ε : T, (0 < ε)%L → (da lim1 lim2 < ε)%L). {
  intros ε Hε.
  specialize (Hu ε Hε).
  destruct Hu as (N, HN).
  now apply (HN N).
}
clear Hu; rename H into Hu.
destruct dist as (Hdsym, Hdsep, Hdtri).
apply Hdsep.
apply (rngl_abs_le_ε Hop Hiv Hor).
intros ε Hε.
specialize (Hu ε Hε).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | apply Hdpos ].
apply (rngl_lt_le_incl Hto).
eapply (rngl_le_lt_trans Hto); [ | apply Hu ].
apply (rngl_le_refl Hor).
Qed.

Theorem limit_add :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ {dt : T → T → T} (dist : is_dist dt),
  (∀ a b c d, (dt (a + b) (c + d) ≤ dt a c + dt b d)%L)
  → ∀ u v limu limv,
  is_limit_when_seq_tends_to_inf dt u limu
  → is_limit_when_seq_tends_to_inf dt v limv
  → is_limit_when_seq_tends_to_inf dt (λ n, (u n + v n))%L (limu + limv)%L.
Proof.
intros Hop Hiv Hor * dist * Hd * Hu Hv ε Hε.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1 in Hε.
  now apply (rngl_lt_irrefl Hor) in Hε.
}
assert (Hε2 : (0 < ε / 2)%L). {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hor 2⁻¹%L) in Hε. 2: {
    apply (rngl_inv_pos Hop Hiv Hor).
    apply (rngl_0_lt_2 Hos Hc1 Hor).
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
  rewrite <- (rngl_mul_2_r).
  rewrite (rngl_div_mul Hiv). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hor).
  }
  apply (rngl_le_refl Hor).
}
eapply (rngl_le_lt_trans Hto). 2: {
  apply (rngl_add_lt_compat Hos Hor); [ apply Hun | apply Hvn ].
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
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
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
