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

From Stdlib Require Import Utf8 Arith.
Require Import Structures.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_add_0_r : ∀ a, (a + 0 = a)%L.
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

Theorem rngl_sub_diag :
  rngl_has_opp_or_psub T = true →
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
remember (rngl_has_psub T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 0%L a).
  now rewrite rngl_add_0_l in H1.
}
apply rngl_has_opp_or_psub_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_psub_diag :
  rngl_has_opp_or_psub T = true →
  ∀ a, rngl_psub a a = 0%L.
Proof.
intros Hos *.
specialize (rngl_sub_diag Hos a) as H1.
unfold rngl_sub in H1.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op. {
  unfold rngl_psub.
  unfold rngl_has_opp in Hop.
  destruct rngl_opt_opp_or_psub; [ | easy ].
  now destruct s.
}
remember (rngl_has_psub T) as su eqn:Hsu; symmetry in Hsu.
destruct su; [ easy | ].
apply rngl_has_opp_or_psub_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem rngl_sub_add :
  rngl_has_opp T = true →
  ∀ a b, (a - b + b = a)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite <- rngl_add_assoc.
rewrite (rngl_add_opp_diag_l Hop).
apply rngl_add_0_r.
Qed.

Theorem rngl_add_sub :
  rngl_has_opp_or_psub T = true →
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
remember (rngl_has_psub T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  apply H1.
}
apply rngl_has_opp_or_psub_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_add_cancel_l :
  rngl_has_opp_or_psub T = true →
  ∀ a b c, (a + b = a + c)%L ↔ (b = c)%L.
Proof.
intros Hos *.
split; intros Habc; [ | now subst b ].
specialize (rngl_add_sub Hos c a) as H1.
rewrite rngl_add_comm, <- Habc in H1.
rewrite rngl_add_comm in H1.
now rewrite (rngl_add_sub Hos) in H1.
Qed.

Theorem rngl_add_cancel_r :
  rngl_has_opp_or_psub T = true →
  ∀ a b c, (a + c = b + c)%L ↔ (a = b)%L.
Proof.
intros Hos *.
do 2 rewrite (rngl_add_comm _ c).
apply (rngl_add_cancel_l Hos).
Qed.

Theorem rngl_add_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a + b)%L = c ↔ b = (c - a)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Hb. {
  subst c; symmetry.
  rewrite rngl_add_comm.
  apply (rngl_add_sub Hos).
} {
  subst b.
  rewrite rngl_add_comm.
  apply (rngl_sub_add Hop).
}
Qed.

Theorem rngl_add_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a + b)%L = c ↔ a = (c - b)%L.
Proof.
intros Hop *.
rewrite rngl_add_comm.
apply (rngl_add_move_l Hop).
Qed.

Theorem rngl_sub_move_l :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = c ↔ b = (a - c)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Hb. {
  apply (rngl_add_move_l Hop).
  subst c.
  apply (rngl_sub_add Hop).
} {
  apply (rngl_add_move_l Hop) in Hb.
  subst a.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_sub_move_r :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = c ↔ a = (c + b)%L.
Proof.
intros Hop *.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
split; intros Ha. {
  subst c; symmetry.
  apply (rngl_sub_add Hop).
} {
  subst a.
  apply (rngl_add_sub Hos).
}
Qed.

Theorem rngl_add_sub_eq_l :
  rngl_has_opp_or_psub T = true →
  ∀ a b c, (a + b = c → c - a = b)%L.
Proof.
intros Hom * Hab.
rewrite <- Hab.
rewrite rngl_add_comm.
now apply rngl_add_sub.
Qed.

Theorem rngl_add_sub_eq_r :
  rngl_has_opp_or_psub T = true →
   ∀ a b c, (a + b = c → c - b = a)%L.
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

Theorem rngl_add_move_0_l :
  rngl_has_opp T = true →
  ∀ a b, (a + b = 0)%L ↔ (b = - a)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros H. {
  apply rngl_sub_compat_l with (c := a) in H.
  rewrite rngl_add_comm in H.
  rewrite (rngl_add_sub Hos) in H.
  unfold rngl_sub in H.
  rewrite Hop in H.
  now rewrite rngl_add_0_l in H.
} {
  rewrite H.
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_sub_diag Hos).
}
Qed.

Theorem rngl_add_move_0_r :
  rngl_has_opp T = true →
  ∀ a b, (a + b = 0)%L ↔ (a = - b)%L.
Proof.
intros Hro *.
rewrite rngl_add_comm.
now apply rngl_add_move_0_l.
Qed.

Theorem rngl_add_compat_r : ∀ a b c,
  (a = b)%L → (a + c = b + c)%L.
Proof.
intros a b c Hab.
now rewrite Hab.
Qed.

Theorem rngl_sub_move_0_r :
  rngl_has_opp T = true →
  ∀ a b : T, (a - b)%L = 0%L ↔ a = b.
Proof.
intros Hop *.
split. {
  intros Hab.
  apply (rngl_add_compat_r _ _ b) in Hab.
  unfold rngl_sub in Hab.
  rewrite Hop in Hab.
  rewrite <- rngl_add_assoc in Hab.
  rewrite rngl_add_opp_diag_l in Hab; [ | easy ].
  now rewrite rngl_add_0_r, rngl_add_0_l in Hab.
} {
  intros Hab.
  rewrite Hab.
  apply rngl_sub_diag.
  now apply rngl_has_opp_or_psub_iff; left.
}
Qed.

Theorem rngl_opp_0 : rngl_has_opp T = true → (- 0 = 0)%L.
Proof.
intros Hro.
transitivity (0 + - 0)%L. {
  symmetry.
  apply rngl_add_0_l.
}
rewrite rngl_add_opp_r; [ | easy ].
apply rngl_sub_diag.
now apply rngl_has_opp_or_psub_iff; left.
Qed.

Theorem rngl_psub_0_r :
  rngl_has_psub T = true →
  ∀ a, rngl_psub a 0%L = a.
Proof.
intros Hsu *.
specialize rngl_opt_add_sub as H1.
rewrite Hsu in H1.
unfold rngl_sub in H1.
rewrite Hsu in H1.
unfold rngl_has_psub in Hsu.
unfold rngl_has_opp in H1.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub ]; [ easy | ].
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
apply rngl_add_0_l.
Qed.

Theorem rngl_sub_0_r :
  rngl_has_opp_or_psub T = true →
  ∀ a, (a - 0 = a)%L.
Proof.
intros Hom *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_opp_0; [ | easy ].
  apply rngl_add_0_r.
}
remember (rngl_has_psub T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_add_sub as H1.
  rewrite Hmo in H1.
  specialize (H1 a 0%L) as H2.
  now rewrite rngl_add_0_r in H2.
}
apply rngl_has_opp_or_psub_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_opp_add_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a + b) = - a - b)%L.
Proof.
intros Hop *.
specialize (proj2 rngl_has_opp_or_psub_iff) as Hop'.
rewrite Hop in Hop'.
apply rngl_add_cancel_l with (a := (a + b)%L); [ now apply Hop'; left | ].
rewrite (rngl_add_opp_r Hop).
rewrite rngl_sub_diag; [ | now apply Hop'; left ].
unfold rngl_sub.
rewrite Hop.
rewrite rngl_add_assoc.
do 2 rewrite (rngl_add_opp_r Hop).
rewrite rngl_add_comm.
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

Theorem rngl_add_add_swap : ∀ a b c, (a + b + c = a + c + b)%L.
Proof.
intros.
do 2 rewrite <- rngl_add_assoc.
progress f_equal.
apply rngl_add_comm.
Qed.

Theorem rngl_add_add_add_swap :
  ∀ a b c d, ((a + b) + (c + d) = (a + c) + (b + d))%L.
Proof.
intros.
do 2 rewrite <- rngl_add_assoc.
progress f_equal.
rewrite rngl_add_comm, rngl_add_assoc.
apply rngl_add_add_swap.
Qed.

Theorem rngl_sub_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a - b - c = a - c - b)%L.
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
apply rngl_add_assoc.
Qed.

Theorem rngl_add_sub_swap :
  rngl_has_opp T = true →
  ∀ a b c, (a + b - c = a - c + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
apply rngl_add_add_swap.
Qed.

Theorem rngl_add_sub_simpl_l :
  rngl_has_opp_or_psub T = true →
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
  rewrite (rngl_add_add_swap a).
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_add_opp_r; [ | easy ].
  rewrite rngl_sub_diag, rngl_add_0_l; [ easy | easy ].
}
remember (rngl_has_psub T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  rewrite Hmo in H1.
  rewrite H1.
  rewrite rngl_add_comm.
  rewrite rngl_add_sub; [ easy | easy ].
}
apply rngl_has_opp_or_psub_iff in Hom.
destruct Hom; congruence.
Qed.

Theorem rngl_opp_involutive :
  rngl_has_opp T = true →
  ∀ x, (- - x)%L = x.
Proof.
intros Hro *.
symmetry.
apply (rngl_add_move_0_r Hro).
rewrite (rngl_add_opp_r Hro).
apply rngl_sub_diag.
now apply rngl_has_opp_or_psub_iff; left.
Qed.

Theorem rngl_sub_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a - - b = a + b)%L.
Proof.
intros Hop *.
progress unfold rngl_sub.
rewrite Hop.
f_equal.
apply (rngl_opp_involutive Hop).
Qed.

Theorem rngl_opp_inj :
  rngl_has_opp T = true →
  ∀ a b, (- a = - b)%L → a = b.
Proof.
intros Hro * H.
rewrite <- (rngl_opp_involutive Hro a).
rewrite H.
now apply rngl_opp_involutive.
Qed.

Theorem rngl_sub_cancel_l :
  rngl_has_opp T = true →
  ∀ a b c, (a - b)%L = (a - c)%L ↔ b = c.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros H1; [ | now subst b ].
do 2 rewrite <- (rngl_add_opp_r Hop) in H1.
apply (rngl_add_cancel_l Hos) in H1.
now apply (rngl_opp_inj Hop) in H1.
Qed.

Theorem rngl_opp_sub_distr :
  rngl_has_opp T = true →
  ∀ a b, (- (a - b) = b - a)%L.
Proof.
intros Hop *.
unfold rngl_sub at 1.
rewrite Hop.
rewrite rngl_opp_add_distr; [ | easy ].
rewrite (rngl_sub_opp_r Hop).
apply (rngl_add_opp_l Hop).
Qed.

Theorem rngl_sub_add_distr :
  rngl_has_opp_or_psub T = true →
  ∀ a b c, (a - (b + c) = a - b - c)%L.
Proof.
intros Hos *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  unfold rngl_sub.
  rewrite rngl_opp_add_distr; [ | easy ].
  unfold rngl_sub; rewrite Hop.
  apply rngl_add_assoc.
}
remember (rngl_has_psub T) as mo eqn:Hmo.
symmetry in Hmo.
destruct mo. {
  specialize rngl_opt_sub_add_distr as H1.
  now rewrite Hmo in H1.
}
apply rngl_has_opp_or_psub_iff in Hos.
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
rewrite (rngl_sub_opp_r Hop).
apply rngl_add_assoc.
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
  rngl_has_opp_or_psub T = true →
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
now apply rngl_has_opp_or_psub_iff; left.
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

Theorem rngl_1_neq_0 :
  rngl_has_1 T = true → rngl_characteristic T ≠ 1 → (1 ≠ 0)%L.
Proof.
intros Hon Hc1.
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
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
Qed.

Theorem rngl_1_neq_0_iff :
  rngl_has_1 T = true → rngl_characteristic T ≠ 1 ↔ (1 ≠ 0)%L.
Proof.
intros Hon.
split; [ apply (rngl_1_neq_0 Hon) | ].
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
intros H10 Hc.
rewrite Hc in H1; cbn in H1.
now rewrite rngl_add_0_r in H1.
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
  rngl_has_opp_or_psub T = true →
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
Arguments rngl_add_add_swap {T ro rp} (a b c)%_L.
Arguments rngl_add_sub_swap {T ro rp} Hop (a b c)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_mul_nat {T ro} a%_L n%_nat.
Arguments rngl_opp_sub_swap {T ro rp} Hop (a b)%_L.
Arguments rngl_sub_add {T ro rp} Hop (a b)%_L.
Arguments rngl_sub_add_distr {T ro rp} Hos (a b c)%_L.
Arguments rngl_sub_sub_swap {T ro rp} Hop (a b c)%_L.
