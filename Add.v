(** * Add

Theorems about addition and opposite in ring-like structures.

There is also a notion of subtraction, which can be either:
- addition of the opposite ([a+(-b)]) or
- partial subtraction (with the property [a+b-b=a]).

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
From Stdlib Require Import Morphisms.
Require Import Structures.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_add_0_r : ∀ a, (a + 0)%L = a.
Proof.
intros a; simpl.
rewrite rngl_add_comm.
apply rngl_add_0_l.
Qed.

Theorem rngl_add_opp_l :
  rngl_has_opp T = true →
  ∀ a b, (- a + b)%L = (b - a)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
progress unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem rngl_add_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a + - b)%L = (a - b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
now rewrite Hop.
Qed.

Theorem rngl_add_opp_diag_l :
  rngl_has_opp T = true →
  ∀ x, (- x + x = 0)%L.
Proof.
intros H1 *.
specialize rngl_opt_add_opp_diag_l as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_eq_refl : ∀ a, (a = a)%L.
Proof.
intros.
specialize rngl_opt_equivalence as H.
progress unfold rngl_has_eq in H.
progress unfold rngl_eq in H.
progress unfold rngl_eq.
destruct (rngl_opt_equiv T); [ apply H | easy ].
Qed.

Theorem rngl_sub_diag :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a - a = 0)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  now apply rngl_add_opp_diag_l.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 0%L a).
  rewrite rngl_add_0_l in H1.
  rewrite H1.
  apply rngl_eq_refl.
}
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_subt_diag :
  rngl_has_opp_or_subt T = true →
  ∀ a, (rngl_subt a a = 0)%L.
Proof.
intros Hos *.
specialize (rngl_sub_diag Hos a) as H1.
unfold rngl_sub in H1.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
remember (rngl_has_subt T) as su eqn:Hsu; symmetry in Hsu.
progress unfold rngl_has_opp in Hop.
progress unfold rngl_has_subt in Hsu.
destruct op. {
  unfold rngl_subt.
  destruct rngl_opt_opp_or_subt; [ | easy ].
  destruct s; [ apply rngl_eq_refl | easy ].
}
destruct su; [ easy | ].
progress unfold rngl_has_opp_or_subt in Hos.
destruct (rngl_opt_opp_or_subt T); [ now destruct s | easy ].
Qed.

Global Instance rngl_add_morph  :
  Proper (rngl_eq ==> rngl_eq ==> rngl_eq) rngl_add.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
specialize rngl_opt_add_morph as H.
progress unfold rngl_eq in Hab.
progress unfold rngl_eq in Hcd.
progress unfold rngl_has_eq in H.
progress unfold rngl_eq in H.
progress unfold rngl_eq.
destruct (rngl_opt_equiv T) as [eqv| ]; [ | congruence ].
cbn in H.
now apply H.
Qed.

Global Instance rngl_opp_morph :
  Proper (rngl_eq ==> rngl_eq) rngl_opp.
Proof.
intros a b Hab.
specialize rngl_opt_opp_morph as H.
progress unfold rngl_eq in Hab.
progress unfold rngl_has_eq in H.
progress unfold rngl_eq in H.
progress unfold rngl_eq.
destruct (rngl_opt_equiv T) as [eqv| ]; [ | congruence ].
cbn in H.
now apply H.
Qed.

Global Instance rngl_sub_morph :
  Proper (rngl_eq ==> rngl_eq ==> rngl_eq) rngl_sub.
Proof.
intros a b Hab c d Hcd.
move c before b; move d before c.
specialize rngl_opt_subt_morph as H.
progress unfold rngl_sub.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op; [ now rewrite Hab, Hcd | ].
remember (rngl_has_subt T) as su eqn:Hsu.
symmetry in Hsu.
destruct su; [ | easy ].
progress unfold rngl_eq in Hab.
progress unfold rngl_eq in Hcd.
progress unfold rngl_eq.
progress unfold rngl_has_eq in H.
progress unfold rngl_eq in H.
destruct (rngl_opt_equiv T) as [eqv| ]; [ | congruence ].
now apply H.
Qed.

Theorem rngl_sub_add :
  rngl_has_opp T = true →
  ∀ a b, (a - b + b = a)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite <- rngl_add_assoc.
specialize (rngl_add_opp_diag_l Hop b) as H.
rewrite H.
rewrite rngl_add_0_r.
apply rngl_eq_refl.
Qed.

Theorem rngl_add_sub :
  rngl_has_opp_or_subt T = true →
  ∀ a b, (a + b - b = a)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite <- rngl_add_assoc.
  rewrite (rngl_add_comm b).
  now rewrite rngl_add_opp_diag_l, rngl_add_0_r.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  rewrite H1.
  apply rngl_eq_refl.
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + b = a + c)%L ↔ (b = c)%L.
Proof.
intros Hos *.
split; intros Habc. 2: {
  rewrite Habc.
  apply rngl_eq_refl.
}
rewrite <- (rngl_add_sub Hos b a).
rewrite <- (rngl_add_sub Hos c a).
do 2 rewrite (rngl_add_comm _ a).
now rewrite Habc.
Qed.

Theorem rngl_add_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a + b = c)%L ↔ (b = c - a)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  rewrite <- Hb; symmetry.
  rewrite rngl_add_comm.
  apply (rngl_add_sub Hos).
} {
  rewrite Hb.
  rewrite rngl_add_comm.
  apply (rngl_sub_add Hop).
}
Qed.

Theorem rngl_add_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a + b = c)%L ↔ (a = c - b)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
apply (rngl_add_move_l Hop).
Qed.

Theorem rngl_sub_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a - b = c)%L ↔ (b = a - c)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Hb. {
  rewrite <- Hb.
  apply (rngl_add_move_l Hop).
  apply (rngl_sub_add Hop).
} {
  apply (rngl_add_move_l Hop) in Hb.
  rewrite <- Hb.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_sub_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a - b = c)%L ↔ (a = c + b)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
split; intros Ha. {
  rewrite <- Ha; symmetry.
  apply (rngl_sub_add Hop).
} {
  rewrite Ha.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + b = c)%L → (c - a = b)%L.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp_or_subt T = true →
   ∀ a b c, (a + b = c)%L → (c - b = a)%L.
Proof.
intros Hom * Hab.
apply rngl_add_sub_eq_l; [ easy | ].
now rewrite rngl_add_comm.
Qed.

Theorem rngl_sub_compat_l : ∀ a b c,
  a = b → (a - c = b - c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_cancel_r :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a + c = b + c)%L → (a = b)%L.
Proof.
intros Hos * Habc.
apply (rngl_add_sub_eq_r Hos) in Habc.
now rewrite (rngl_add_sub Hos) in Habc.
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp T = true →
  ∀ a b, (a + b = 0)%L ↔ (a = - b)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros H. {
  rewrite rngl_add_comm in H.
  apply (rngl_add_sub_eq_l Hos) in H.
  rewrite <- H.
  progress unfold rngl_sub.
  rewrite Hop.
  now rewrite rngl_add_0_l.
} {
  rewrite H.
  apply (rngl_add_opp_diag_l Hop).
}
Qed.

Theorem rngl_add_compat_r : ∀ a b c,
  (a = b)%L → (a + c = b + c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_sub_move_0_r :
  rngl_has_opp T = true →
  ∀ a b : T, (a - b = 0)%L ↔ (a = b)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split. {
  intros Hab.
  apply (rngl_add_compat_r _ _ b) in Hab.
  rewrite (rngl_sub_add Hop) in Hab.
  now rewrite rngl_add_0_l in Hab.
} {
  intros Hab.
  rewrite Hab.
  apply (rngl_sub_diag Hos).
}
Qed.

Theorem rngl_opp_0 : rngl_has_opp T = true → (- 0 = 0)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
transitivity (0 + - 0)%L. {
  symmetry.
  rewrite rngl_add_0_l.
  apply rngl_eq_refl.
}
rewrite rngl_add_opp_r; [ | easy ].
apply (rngl_sub_diag Hos).
Qed.

Theorem rngl_subt_0_r :
  rngl_has_subt T = true →
  ∀ a, rngl_subt a 0%L = a.
Proof.
intros Hsu *.
specialize rngl_opt_add_sub as H1.
rewrite Hsu in H1.
unfold rngl_sub in H1.
rewrite Hsu in H1.
unfold rngl_has_subt in Hsu.
unfold rngl_has_opp in H1.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
destruct os as [opp| subt ]; [ easy | ].
specialize (H1 a 0%L).
now rewrite rngl_add_0_r in H1.
Qed.

Theorem rngl_sub_0_l :
  rngl_has_opp T = true →
  ∀ a, (0 - a = - a)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_0_l.
apply rngl_eq_refl.
Qed.

Theorem rngl_sub_0_r :
  rngl_has_opp_or_subt T = true →
  ∀ a, (a - 0 = a)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_opp_0; [ | easy ].
  rewrite rngl_add_0_r.
  apply rngl_eq_refl.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 a 0%L) as H2.
  rewrite rngl_add_0_r in H2.
  rewrite H2.
  apply rngl_eq_refl.
}
apply rngl_has_opp_or_subt_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_opp_add_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a + b) = - b - a)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_subt_iff) as Hop'.
rewrite Hop in Hop'.
apply rngl_add_cancel_l with (a := (a + b)%L); [ now apply Hop'; left | ].
rewrite (rngl_add_opp_r Hop).
rewrite rngl_sub_diag; [ | now apply Hop'; left ].
unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_assoc.
do 2 rewrite (rngl_add_opp_r Hop).
rewrite rngl_add_sub; [ | now apply Hop'; left ].
symmetry.
apply rngl_sub_diag.
now apply Hop'; left.
Qed.

Theorem rngl_opp_sub_swap :
  rngl_has_opp T = true →
  ∀ a b, (- a - b = - b - a)%L.
Proof.
intros Hop *.
rewrite <- (rngl_opp_add_distr Hop).
rewrite rngl_add_comm.
apply (rngl_opp_add_distr Hop).
Qed.

Theorem rngl_add_add_swap : ∀ n m p, (n + m + p)%L = (n + p + m)%L.
Proof.
intros n m p; simpl.
do 2 rewrite <- rngl_add_assoc.
progress f_equal.
apply rngl_add_comm.
Qed.

Theorem rngl_add_add_add_swap :
  ∀ a b c d, ((a + b) + (c + d))%L = ((a + c) + (b + d))%L.
Proof.
intros.
do 2 rewrite <- rngl_add_assoc.
progress f_equal.
rewrite rngl_add_comm, rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem rngl_sub_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a - b - c)%L = (a - c - b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_add_swap.
Qed.

Theorem rngl_add_compat_l : ∀ a b c,
  (a = b)%L → (c + a = c + b)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_add_sub_assoc :
  rngl_has_opp T = true →
  ∀ a b c, (a + (b - c) = a + b - c)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_assoc.
apply rngl_eq_refl.
Qed.

Theorem rngl_add_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a + b - c = a - c + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_add_swap.
apply rngl_eq_refl.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp_or_subt T = true →
  ∀ a b c : T, (a + b - (a + c) = b - c)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap.
  rewrite (rngl_add_add_swap a).
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_sub_diag, rngl_add_0_l; [ easy | easy ].
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  rewrite Hmo in H1.
  rewrite H1.
  rewrite rngl_add_comm.
  rewrite rngl_add_sub; [ easy | easy ].
}
apply rngl_has_opp_or_subt_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp T = true →
  ∀ x, (- - x = x)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
symmetry.
apply (rngl_add_move_0_r Hop).
rewrite (rngl_add_opp_r Hop).
apply (rngl_sub_diag Hos).
Qed.

Theorem rngl_sub_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a - - b = a + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
rewrite (rngl_opp_involutive Hop).
apply rngl_eq_refl.
Qed.

Theorem rngl_opp_inj :
  rngl_has_opp T = true →
  ∀ a b, (- a = - b)%L → (a = b)%L.
Proof.
intros Hro * H.
rewrite <- (rngl_opp_involutive Hro a).
rewrite H.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_sub_cancel_l :
  rngl_has_opp T = true →
  ∀ a b c, (a - b = a - c)%L ↔ (b = c)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros H1; [ | now rewrite H1 ].
do 2 rewrite <- (rngl_add_opp_r Hop) in H1.
apply (rngl_add_cancel_l Hos) in H1.
now apply (rngl_opp_inj Hop) in H1.
Qed.

Theorem rngl_opp_sub_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a - b) = b - a)%L.
Proof.
intros Hro *.
unfold rngl_sub at 1.
rewrite Hro.
rewrite rngl_opp_add_distr; [ | easy ].
now rewrite rngl_opp_involutive.
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp_or_subt T = true →
  ∀ a b c, (a - (b + c) = a - b - c)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  rewrite rngl_add_assoc.
  now rewrite rngl_add_add_swap.
}
remember (rngl_has_subt T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  rewrite Hmo in H1.
  now rewrite H1.
}
apply rngl_has_opp_or_subt_iff in Hos.
now destruct Hos; congruence.
Qed.

Theorem rngl_sub_sub_distr :
  rngl_has_opp T = true →
  ∀ a b c, (a - (b - c) = a - b + c)%L.
Proof.
intros Hop *.
unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_involutive Hop).
unfold rngl_sub; rewrite Hop.
rewrite rngl_add_assoc.
now rewrite rngl_add_add_swap.
Qed.

Theorem rngl_mul_nat_add_r : ∀ a m n,
  rngl_mul_nat a (m + n) = (rngl_mul_nat a m + rngl_mul_nat a n)%L.
Proof.
intros.
unfold rngl_mul_nat, mul_nat.
induction m; cbn; [ now rewrite rngl_add_0_l | ].
rewrite <- rngl_add_assoc; f_equal.
apply IHm.
Qed.

Theorem rngl_of_nat_add : ∀ m n,
  rngl_of_nat (m + n) = (rngl_of_nat m + rngl_of_nat n)%L.
Proof.
intros.
apply rngl_mul_nat_add_r.
Qed.

Theorem rngl_of_nat_sub :
  rngl_has_opp_or_subt T = true →
  ∀ m n, n ≤ m → rngl_of_nat (m - n) = (rngl_of_nat m - rngl_of_nat n)%L.
Proof.
intros Hos * Hnm.
replace m with (n + (m - n)) at 2. 2: {
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm.
  apply Nat.add_sub.
}
rewrite rngl_of_nat_add.
symmetry.
rewrite rngl_add_comm.
...
apply (rngl_add_sub Hos).
Qed.

Theorem rngl_of_nat_1 : rngl_of_nat 1 = 1%L.
Proof. apply rngl_add_0_r. Qed.

Theorem rngl_of_nat_2 : rngl_of_nat 2 = 2%L.
Proof. now cbn; rewrite rngl_add_0_r. Qed.

Theorem rngl_mul_nat_succ :
  ∀ a n, rngl_mul_nat a (S n) = (a + rngl_mul_nat a n)%L.
Proof.
intros.
rewrite <- Nat.add_1_l.
rewrite rngl_mul_nat_add_r.
now cbn; rewrite rngl_add_0_r.
Qed.

Theorem rngl_of_nat_succ :
  ∀ n, rngl_of_nat (S n) = (1 + rngl_of_nat n)%L.
Proof. easy. Qed.

Theorem rngl_abs_0 :
  rngl_has_opp T = true →
  ∣ 0 ∣ = 0%L.
Proof.
intros Hop.
progress unfold rngl_abs.
rewrite (rngl_opp_0 Hop).
now destruct (0 ≤? 0)%L.
Qed.

Theorem eq_rngl_abs_0 :
  rngl_has_opp T = true →
  ∀ a, rngl_abs a = 0%L → a = 0%L.
Proof.
intros Hop * Ha.
progress unfold rngl_abs in Ha.
destruct (a ≤? 0)%L; [ | easy ].
rewrite <- (rngl_opp_0 Hop) in Ha.
now apply (rngl_opp_inj Hop) in Ha.
Qed.

Theorem rngl_add_opp_diag_r :
  rngl_has_opp T = true →
  ∀ x : T, (x + - x)%L = 0%L.
Proof.
intros Hop *.
rewrite (rngl_add_opp_r Hop).
apply rngl_sub_diag.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Arguments rngl_mul_nat {T ro} a%_L n%_nat.

Theorem rngl_of_nat_0 : rngl_of_nat 0 = 0%L.
Proof. easy. Qed.

Theorem fold_rngl_mul_nat :
  ∀ a n, List.fold_right rngl_add 0%L (List.repeat a n)%L = rngl_mul_nat a n.
Proof. easy. Qed.

Theorem rngl_characteristic_0 :
  rngl_has_1 T = true →
  rngl_characteristic T = 0 →
  ∀ i : nat, rngl_of_nat (S i) ≠ 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
now rewrite Hon, Hcz in H1.
Qed.

Theorem rngl_characteristic_non_0 :
  rngl_has_1 T = true →
  rngl_characteristic T ≠ 0 →
  (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
  rngl_of_nat (rngl_characteristic T) = 0%L.
Proof.
intros Hon Hcz.
specialize (rngl_opt_characteristic_prop) as H1.
apply Nat.eqb_neq in Hcz.
now rewrite Hon, Hcz in H1.
Qed.

Theorem rngl_1_neq_0_iff :
  rngl_has_1 T = true → rngl_characteristic T ≠ 1 ↔ (1 ≠ 0)%L.
Proof.
intros Hon.
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
split. {
  intros Hc.
  remember (Nat.eqb (rngl_characteristic T) 0) as cz eqn:Hcz; symmetry in Hcz.
  destruct cz. {
    specialize (H1 0); cbn in H1.
    now rewrite rngl_add_0_r in H1.
  }
  destruct H1 as (Hbef, H1).
  destruct rngl_characteristic as [| n]; [ easy | ].
  destruct n; [ easy | ].
  specialize (Hbef 1).
  cbn in Hbef.
  rewrite rngl_add_0_r in Hbef.
  apply Hbef.
  unfold lt.
  split; [ easy | ].
  do 2 apply le_n_S.
  destruct n; [ easy | apply le_0_n ].
} {
  intros H10 Hc.
  rewrite Hc in H1; cbn in H1.
  now rewrite rngl_add_0_r in H1.
}
Qed.

Theorem eq_rngl_of_nat_0 :
  rngl_has_1 T = true →
  rngl_characteristic T = 0 →
  ∀ i, rngl_of_nat i = 0%L → i = 0.
Proof.
intros Hon Hch * Hi.
destruct i; [ easy | exfalso ].
cbn in Hi.
specialize (rngl_characteristic_0 Hon Hch) as H1.
now specialize (H1 i) as H.
Qed.

Theorem rngl_of_nat_inj :
  rngl_has_1 T = true →
  rngl_has_opp_or_subt T = true →
  rngl_characteristic T = 0 →
  ∀ i j,
  rngl_of_nat i = rngl_of_nat j
  → i = j.
Proof.
intros Hon Hom Hch * Hij.
revert i Hij.
induction j; intros. {
  cbn in Hij.
  now apply eq_rngl_of_nat_0 in Hij.
}
destruct i. {
  exfalso.
  symmetry in Hij.
  now apply eq_rngl_of_nat_0 in Hij.
}
f_equal.
cbn in Hij.
apply rngl_add_cancel_l in Hij; [ | easy ].
now apply IHj.
Qed.

End a.

Arguments rngl_abs {T ro} a%_L.
Arguments rngl_add_sub {T ro rp} Hom (a b)%_L.
Arguments rngl_add_sub_assoc {T ro rp} Hop (a b c)%_L.
Arguments rngl_add_sub_swap {T ro rp} Hop (a b c)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_mul_nat {T ro} a%_L n%_nat.
Arguments rngl_sub_add {T ro rp} Hop (a b)%_L.
Arguments rngl_sub_add_distr {T ro rp} Hos (a b c)%_L.
Arguments rngl_sub_sub_swap {T ro rp} Hop (a b c)%_L.
