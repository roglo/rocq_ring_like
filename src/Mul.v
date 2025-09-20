(** * Mul

Theorems about multiplication in ring-like structures.

Some of them require one or several properties:
- [rngl_mul_is_comm T = true] : that the multiplication is commutative,
- [rngl_has_opp T = true] : that there is an opposite
- [rngl_has_psub T = true] : that there is a partial subtraction,
- [rngl_has_opp_or_psub T = true] : that there is an opposite or
  a partial subtraction,
- [rngl_has_1 T = true] : that [1] exists,

See the module [[RingLike.Core]] for the general description
of the ring-like library.

In general, it is not necessary to import this module. The normal
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

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ a b, (a * b = b * a)%L.
Proof.
intros H1 *.
specialize rngl_opt_mul_comm as H.
rewrite H1 in H.
apply H.
Qed.

Theorem rngl_mul_add_distr_r : ∀ x y z,
  ((x + y) * z = x * z + y * z)%L.
Proof.
intros x y z; simpl.
specialize rngl_opt_mul_add_distr_r as rngl_mul_add_distr_r.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
symmetry in Hic.
destruct ic. {
  rewrite rngl_mul_comm; [ | easy ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_comm; [ | easy ].
  now rewrite (rngl_mul_comm Hic z).
} {
  apply rngl_mul_add_distr_r.
}
Qed.

Theorem rngl_mul_0_r :
  rngl_has_opp_or_psub T = true →
  ∀ a, (a * 0 = 0)%L.
Proof.
intros Hos *.
apply (rngl_add_cancel_r Hos _ _ (a * a)%L).
rewrite <- rngl_mul_add_distr_l.
now do 2 rewrite rngl_add_0_l.
Qed.

(* if I add the distributivity multiplication/subtraction as an axiom,
   the same theorem above can be proved using it, which gives two
   proofs of the same thing, and I don't like that; it is the reason
   why I hesitate to add this distributivity in my ring-like axioms
   when there is a subtraction but no opposite.  *)

(* a.0 = a.(b-b) = a.b - a.b = 0
   (any b can be chosen: a, 0, 1, ...) *)
Theorem rngl_mul_0_r' :
  rngl_has_psub T = true →
  (∀ a b c, a * (b - c) = a * b - a * c)%L
  → ∀ a, (a * 0 = 0)%L.
Proof.
intros Hsu.
generalize Hsu; intros Hop.
apply rngl_has_psub_has_no_opp in Hop.
intros rngl_mul_sub_distr_l a.
specialize rngl_add_0_l as H1.
specialize rngl_opt_add_sub as H2.
specialize (rngl_mul_sub_distr_l) as H3.
progress unfold rngl_sub in H2.
progress unfold rngl_sub in H3.
rewrite Hsu, Hop in H2, H3.
(*
  H1 : ∀ a : T, (0 + a)%L = a
  H2 : ∀ a b : T, rngl_psub (a + b) b = a
  H3 : ∀ a b c : T, (a * rngl_psub b c)%L = rngl_psub (a * b) (a * c)
*)
(* it seems that the theorem a-a=0 is sufficient, no need to have
   the full a+b-b=a for all a and b *)
set (b := 0%L).
specialize (H3 a b b) as H.
(* a.(b - b) = a.b - a.b *)
rewrite <- (H1 b) in H at 1.
(* a.(0 + b - b) = a.b - a.b *)
rewrite H2 in H.
(* a.0 = a.b - a.b *)
rewrite <- (H1 (a * b))%L in H at 1.
(* a.0 = 0 + a.b - a.b *)
rewrite H2 in H.
(* a.0 = 0 *)
easy.
Qed.

(* a.0 = a.0 + a.b - a.b = a.(0+b) - a.b = a.b - a.b = 0
   (any b can be chosen: a, 0, 1, ...) *)
Theorem rngl_mul_0_r'' :
  rngl_has_psub T = true →
  ∀ a, (a * 0 = 0)%L.
Proof.
intros Hsu.
generalize Hsu; intros Hop.
apply rngl_has_psub_has_no_opp in Hop.
intros.
specialize rngl_add_0_l as H1.
specialize rngl_opt_add_sub as H2.
specialize rngl_mul_add_distr_l as H3.
progress unfold rngl_sub in H2.
rewrite Hsu, Hop in H2.
(*
  H1 : ∀ a : T, (0 + a)%L = a
  H2 : ∀ a b : T, rngl_psub (a + b) b = a
  H3 : ∀ a b c : T, (a * (b + c))%L = (a * b + a * c)%L
*)
set (b := 0%L).
specialize (H2 (a * 0) (a * b))%L as H.
symmetry in H.
(* a.0 = a.0 + a.b - a.b *)
rewrite <- (H3 a) in H at 1.
(* a.0 = a.(0 + b) - a.b *)
rewrite H1 in H.
(* a.0 = a.b - a.b *)
rewrite <- (H1 (a * b))%L in H at 1.
(* a.0 = 0 + a.b - a.b *)
rewrite H2 in H.
(* a.0 = 0 *)
easy.
(* Does a+a=a imply a=0 ? *)
(* Yes, if there is an opposite or a subtraction,
   Otherwise, false. Example: (ℕ, +=lcm, *=* ),
   because ∀ a, lcm a a = a *)
Qed.

Theorem rngl_mul_0_l :
  rngl_has_opp_or_psub T = true →
  ∀ a, (0 * a = 0)%L.
Proof.
intros Hos a.
apply (rngl_add_cancel_r Hos _ _ (1 * a)%L).
rewrite <- rngl_mul_add_distr_r.
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem rngl_mul_1_l :
  rngl_has_1 T = true →
  ∀ a, (1 * a = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
rewrite Hon in H1.
apply H1.
Qed.

Theorem rngl_mul_1_r :
  rngl_has_1 T = true →
  ∀ a, (a * 1 = a)%L.
Proof.
intros Hon *.
specialize rngl_opt_mul_1_l as H1.
specialize rngl_opt_mul_1_r as H2.
rewrite Hon in H1, H2.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
now rewrite rngl_mul_comm, rngl_mul_1_l.
Qed.

Theorem rngl_mul_2_l :
  rngl_has_1 T = true →
  ∀ a, (2 * a = a + a)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_mul_2_r :
  rngl_has_1 T = true →
  ∀ a, (a * 2 = a + a)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_mul_mul_swap :
  rngl_mul_is_comm T = true →
  ∀ a b c, (a * b * c = a * c * b)%L.
Proof.
intros Hic *.
do 2 rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_mul_opp_r :
  rngl_has_opp T = true →
  ∀ a b, (a * - b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_l a b (- b)%L) as H.
rewrite rngl_add_opp_r in H; [ | easy ].
rewrite rngl_sub_diag in H; [ | now apply rngl_has_opp_or_psub_iff; left ].
rewrite rngl_mul_0_r in H; [ | now apply rngl_has_opp_or_psub_iff; left ].
symmetry in H.
rewrite rngl_add_comm in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_l :
  rngl_has_opp T = true →
  ∀ a b c, (a * (b - c) = a * b - a * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_l.
now rewrite rngl_mul_opp_r.
Qed.

Theorem rngl_add_mul_r_diag_l :
  rngl_has_1 T = true →
  ∀ a b, (a + a * b = a * (1 + b))%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_add_mul_r_diag_r :
  rngl_has_1 T = true →
  ∀ a b, (a + b * a = (1 + b) * a)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_add_mul_l_diag_l :
  rngl_has_1 T = true →
  ∀ a b, (a * b + a = a * (b + 1))%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_l.
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_add_mul_l_diag_r :
  rngl_has_1 T = true →
  ∀ a b, (a * b + b = (a + 1) * b)%L.
Proof.
intros Hon *.
rewrite rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_sub_mul_r_diag_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, (a - a * b = a * (1 - b))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_sub_mul_l_diag_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b : T, (a * b - a)%L = (a * (b - 1))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
now rewrite (rngl_mul_1_r Hon).
Qed.

Theorem rngl_mul_opp_l :
  rngl_has_opp T = true →
  ∀ a b, (- a * b = - (a * b))%L.
Proof.
intros Hro *.
specialize (rngl_mul_add_distr_r (- a)%L a b) as H.
rewrite rngl_add_opp_diag_l in H; [ | easy ].
rewrite rngl_mul_0_l in H. 2: {
  now apply rngl_has_opp_or_psub_iff; left.
}
symmetry in H.
now apply rngl_add_move_0_r in H.
Qed.

Theorem rngl_mul_sub_distr_r :
  rngl_has_opp T = true →
  ∀ a b c, ((a - b) * c = a * c - b * c)%L.
Proof.
intros Hop *.
unfold rngl_sub; rewrite Hop.
rewrite rngl_mul_add_distr_r.
now rewrite rngl_mul_opp_l.
Qed.

Theorem rngl_sub_mul_l_diag_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b : T, (a * b - b)%L = ((a - 1) * b)%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_r Hop).
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_sub_mul_r_diag_r :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, (a - b * a = (1 - b) * a)%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_r Hop).
now rewrite (rngl_mul_1_l Hon).
Qed.

Theorem rngl_mul_0_sub_1_comm :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a, ((0 - 1) * a = a * (0 - 1))%L.
Proof.
intros Hon Hop *.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_0_l; [ | now apply rngl_has_opp_or_psub_iff; left ].
rewrite rngl_mul_0_r; [ | now apply rngl_has_opp_or_psub_iff; left ].
now rewrite rngl_mul_1_l, rngl_mul_1_r.
Qed.

Theorem rngl_mul_if_then_else_distr : ∀ (x : bool) a b c d,
  ((if x then a else b) * (if x then c else d) =
    if x then a * c else b * d)%L.
Proof. now destruct x. Qed.

Theorem rngl_characteristic_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T = 1 →
  ∀ x, x = 0%L.
Proof.
intros Hon Hos Hch *.
specialize (rngl_opt_characteristic_prop) as H1.
rewrite Hon, Hch in H1; cbn in H1.
destruct H1 as (_, H1).
rewrite rngl_add_0_r in H1.
rewrite <- (rngl_mul_1_r Hon x).
rewrite H1.
apply (rngl_mul_0_r Hos).
Qed.

Theorem rngl_1_eq_0_iff :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  rngl_characteristic T = 1 ↔ (1 = 0)%L.
Proof.
intros Hon Hos.
split. {
  intros Hc.
  specialize (rngl_characteristic_1 Hon Hos Hc) as H1.
  apply H1.
} {
  intros H10.
  destruct (Nat.eq_dec (rngl_characteristic T) 1) as [H1| H1]; [ easy | ].
  now apply (rngl_1_neq_0_iff Hon) in H1.
}
Qed.

Theorem rngl_mul_opp_opp :
  rngl_has_opp T = true →
  ∀ a b, (- a * - b = a * b)%L.
Proof.
intros Hro *.
rewrite rngl_mul_opp_l; [ | easy ].
rewrite rngl_mul_opp_r; [ | easy ].
now apply rngl_opp_involutive.
Qed.

Theorem rngl_squ_opp_1 :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  (-1 * -1)%L = 1%L.
Proof.
intros Hon Hop.
rewrite (rngl_mul_opp_opp Hop).
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_mul_nat_mul_nat_1 :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  ∀ a n, rngl_mul_nat a n = (a * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction n; cbn. {
  symmetry; apply (rngl_mul_0_r Hos).
}
rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
f_equal.
apply IHn.
Qed.

Theorem rngl_mul_nat_comm :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  ∀ n a, (rngl_of_nat n * a = a * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction n; cbn. {
  rewrite (rngl_mul_0_r Hos).
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_mul_add_distr_l.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_mul_1_l Hon).
rewrite (rngl_mul_1_r Hon).
f_equal.
apply IHn.
Qed.

Theorem fold_rngl_of_nat :
  ∀ n, List.fold_right rngl_add 0%L (List.repeat 1 n)%L = rngl_of_nat n.
Proof. easy. Qed.

Theorem rngl_of_nat_mul :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  ∀ m n : nat, rngl_of_nat (m * n) = (rngl_of_nat m * rngl_of_nat n)%L.
Proof.
intros Hon Hos *.
induction m; cbn; [ symmetry; apply (rngl_mul_0_l Hos) | ].
do 2 rewrite fold_rngl_of_nat.
rewrite rngl_of_nat_add, rngl_mul_add_distr_r.
now rewrite (rngl_mul_1_l Hon); f_equal.
Qed.

Theorem rngl_of_nat_pow :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  ∀ a n, rngl_of_nat (a ^ n) = (rngl_of_nat a ^ n)%L.
Proof.
intros Hon Hos *.
induction n; cbn; [ apply rngl_add_0_r | ].
rewrite fold_rngl_of_nat.
rewrite (rngl_of_nat_mul Hon Hos).
now f_equal.
Qed.

Theorem rngl_mul_nat_pow_comm :
  rngl_has_1 T = true →
  rngl_has_opp_or_psub T = true →
  ∀ a b n, (rngl_of_nat a ^ n * b = b * rngl_of_nat a ^ n)%L.
Proof.
intros Hon Hos *.
rewrite <- (rngl_of_nat_pow Hon Hos).
apply (rngl_mul_nat_comm Hon Hos).
Qed.

Theorem rngl_pow_0_l :
  rngl_has_opp_or_psub T = true →
  ∀ n, (0 ^ n)%L = match n with 0 => 1%L | _ => 0%L end.
Proof.
intros Hos *.
destruct n; [ easy | ].
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_pow_0_r : ∀ a, (a ^ 0 = 1)%L.
Proof. easy. Qed.

Theorem rngl_pow_add_r :
  rngl_has_1 T = true →
  ∀ a i j, (a ^ (i + j) = a ^ i * a ^ j)%L.
Proof.
intros Hon *.
induction i; [ symmetry; apply (rngl_mul_1_l Hon) | ].
cbn in IHi |-*.
rewrite IHi.
now rewrite <- rngl_mul_assoc.
Qed.

Theorem rngl_squ_opp :
  rngl_has_opp T = true →
  ∀ a, rngl_squ (- a)%L = rngl_squ a.
Proof.
intros Hop *.
progress unfold rngl_squ.
apply (rngl_mul_opp_opp Hop).
Qed.

Theorem rngl_squ_add :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b, (rngl_squ (a + b) = rngl_squ a + 2 * a * b + rngl_squ b)%L.
Proof.
intros Hic Hon *.
progress unfold rngl_squ.
rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
rewrite rngl_add_assoc; f_equal.
rewrite <- rngl_add_assoc; f_equal.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_2_l Hon); f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_squ_sub :
  rngl_has_opp T = true →
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b, (rngl_squ (a - b) = rngl_squ a - 2 * a * b + rngl_squ b)%L.
Proof.
intros Hop Hic Hon *.
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_opp Hop).
f_equal; f_equal.
apply (rngl_mul_opp_r Hop).
Qed.

Theorem rngl_squ_sub_comm :
  rngl_has_opp T = true →
  ∀ a b, ((a - b)² = (b - a)²)%L.
Proof.
intros Hop.
intros.
rewrite <- (rngl_squ_opp Hop).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_squ_mul :
  rngl_mul_is_comm T = true →
  ∀ a b, rngl_squ (a * b)%L = (rngl_squ a * rngl_squ b)%L.
Proof.
intros Hic *.
progress unfold rngl_squ.
do 2 rewrite rngl_mul_assoc.
f_equal.
apply (rngl_mul_mul_swap Hic).
Qed.

Theorem rngl_pow_1_r :
  rngl_has_1 T = true →
  ∀ a, (a ^ 1)%L = a.
Proof.
intros Hon *; cbn.
apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_pow_succ_l :
  rngl_has_1 T = true →
  ∀ n a, (a ^ S n = a ^ n * a)%L.
Proof.
intros Hon *.
rewrite <- Nat.add_1_r.
rewrite (rngl_pow_add_r Hon).
now rewrite (rngl_pow_1_r Hon).
Qed.

Theorem rngl_pow_succ_r : ∀ n a, (a ^ S n = a * a ^ n)%L.
Proof. easy. Qed.

Theorem rngl_squ_0 :
  rngl_has_opp_or_psub T = true →
  (0² = 0)%L.
Proof.
intros Hos.
apply (rngl_mul_0_l Hos).
Qed.

Theorem rngl_squ_1 :
  rngl_has_1 T = true →
  (1² = 1)%L.
Proof.
intros Hon.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_squ_sub_squ :
  rngl_has_opp T = true →
  ∀ a b, (a² - b² = (a + b) * (a - b) + a * b - b * a)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold rngl_squ.
rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_sub_swap Hop _ (b * b))%L.
f_equal.
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
symmetry.
apply (rngl_sub_add Hop).
Qed.

Theorem rngl_squ_sub_squ' :
  rngl_has_opp T = true →
  ∀ a b, ((a + b) * (a - b) = a² - b² + b * a - a * b)%L.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
rewrite (rngl_squ_sub_squ Hop).
rewrite (rngl_sub_add Hop).
now rewrite (rngl_add_sub Hos).
Qed.

Theorem rngl_squ_pow_2 :
  rngl_has_1 T = true →
  ∀ a, (a² = a ^ 2)%L.
Proof.
intros Hon *; cbn.
now rewrite rngl_mul_1_r.
Qed.

Theorem rngl_pow_1_l : rngl_has_1 T = true → ∀ n, (1 ^ n = 1)%L.
Proof.
intros Hon *.
induction n; [ easy | cbn ].
rewrite IHn.
apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_pow_mul_l :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  ∀ a b n, ((a * b) ^ n = a ^ n * b ^ n)%L.
Proof.
intros Hic Hon *.
induction n; cbn. {
  symmetry; apply (rngl_mul_1_l Hon).
}
do 2 rewrite <- rngl_mul_assoc.
f_equal.
rewrite IHn.
rewrite (rngl_mul_comm Hic).
rewrite <- rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem rngl_pow_mul_r :
  rngl_has_1 T = true →
  ∀ a m n, (a ^ (m * n) = (a ^ m) ^ n)%L.
Proof.
intros Hon *.
revert m.
induction n; intros. {
  rewrite Nat.mul_0_r.
  now do 2 rewrite rngl_pow_0_r.
}
rewrite Nat.mul_succ_r.
rewrite <- Nat.add_1_r.
do 2 rewrite (rngl_pow_add_r Hon).
rewrite IHn.
progress f_equal.
symmetry.
apply (rngl_pow_1_r Hon).
Qed.

Theorem rngl_pow_opp_1_even :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ n, ((-1) ^ (2 * n) = 1)%L.
Proof.
intros Hon Hop *.
rewrite (rngl_pow_mul_r Hon).
rewrite <- (rngl_squ_pow_2 Hon).
progress unfold rngl_squ.
rewrite (rngl_squ_opp_1 Hon Hop).
apply (rngl_pow_1_l Hon).
Qed.

Theorem rngl_pow_opp_1_odd :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ n, ((-1) ^ S (2 * n) = -1)%L.
Proof.
intros Hon Hop *.
rewrite rngl_pow_succ_r.
rewrite (rngl_pow_opp_1_even Hon Hop).
now apply (rngl_mul_1_r Hon).
Qed.

Theorem rngl_pow_squ :
  rngl_has_1 T = true →
  ∀ a n, ((a ^ n)² = a ^ (2 * n))%L.
Proof.
intros Hon *.
rewrite Nat.mul_comm.
rewrite (rngl_squ_pow_2 Hon).
symmetry; apply (rngl_pow_mul_r Hon).
Qed.

Theorem rngl_div_eq_inv_r :
  rngl_has_inv T = true →
  ∀ a b, (a / b)%L = (a * b⁻¹)%L.
Proof.
intros Hiv *.
progress unfold rngl_div.
now rewrite Hiv.
Qed.

(* (-1) ^ n *)

Definition minus_one_pow n :=
  match n mod 2 with
  | 0 => 1%L
  | _ => (- 1%L)%L
  end.

Theorem minus_one_pow_succ :
  rngl_has_opp T = true →
  ∀ i, minus_one_pow (S i) = (- minus_one_pow i)%L.
Proof.
intros Hop *.
unfold minus_one_pow.
remember (i mod 2) as k eqn:Hk; symmetry in Hk.
destruct k. {
  apply Nat.Div0.mod_divides in Hk.
  destruct Hk as (k, Hk); subst i.
  rewrite <- Nat.add_1_l, Nat.mul_comm.
  now rewrite Nat.Div0.mod_add.
}
destruct k. {
  rewrite <- Nat.add_1_l.
  rewrite <- Nat.Div0.add_mod_idemp_r.
  rewrite Hk; cbn.
  symmetry.
  now apply rngl_opp_involutive.
}
specialize (Nat.mod_upper_bound i 2) as H1.
assert (H : 2 ≠ 0) by easy.
specialize (H1 H); clear H.
rewrite Hk in H1.
do 2 apply Nat.succ_lt_mono in H1.
easy.
Qed.

Theorem minus_one_pow_add :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b, minus_one_pow (a + b) = (minus_one_pow a * minus_one_pow b)%L.
Proof.
intros Hon Hop *.
induction a; cbn; [ now rewrite rngl_mul_1_l | ].
rewrite (minus_one_pow_succ Hop).
rewrite (minus_one_pow_succ Hop).
rewrite IHa.
now rewrite rngl_mul_opp_l.
Qed.

(* end (-1) ^ n *)

Theorem Brahmagupta_Fibonacci_identity :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b c d,
  ((a² + b²) * (c² + d²) = (a * c - b * d)² + (a * d + b * c)²)%L.
Proof.
intros Hic Hon Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
rewrite (rngl_squ_sub Hop Hic Hon).
rewrite (rngl_squ_mul Hic).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
do 2 rewrite <- rngl_add_assoc.
f_equal.
rewrite rngl_add_assoc.
rewrite rngl_add_comm.
rewrite (rngl_squ_mul Hic).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
f_equal.
rewrite (rngl_squ_add Hic Hon).
rewrite (rngl_squ_mul Hic).
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_assoc Hop).
rewrite <- rngl_add_assoc.
f_equal.
rewrite rngl_add_comm.
rewrite <- (rngl_add_sub_swap Hop).
rewrite rngl_add_comm.
apply (rngl_sub_move_l Hop).
rewrite (rngl_squ_mul Hic).
rewrite (rngl_add_sub Hos).
do 3 rewrite <- rngl_mul_assoc.
f_equal.
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_assoc.
f_equal.
apply (rngl_mul_comm Hic).
Qed.

Theorem Brahmagupta_Fibonacci_identity_2 :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  ∀ a b c d,
  ((a² + b²) * (c² + d²) = (a * c + b * d)² + (a * d - b * c)²)%L.
Proof.
intros Hic Hon Hop *.
specialize (Brahmagupta_Fibonacci_identity Hic Hon Hop a b d c) as H1.
rewrite (rngl_add_comm ((_ - _)²))%L in H1.
rewrite (rngl_add_comm d²)%L in H1.
easy.
Qed.

End a.

(** ** For the Rocq tactic "ring"

The Rocq tactics "ring" and "ring_simplify" help to directly simplify
some kinds of expressions in the "ring" world. It can be applied to
ring-like structures, providing the following code is added:
<<
  From Stdlib Require Import Ring.
  Section a.
  Context {T : Type}.
  Context {ro : ring_like_op T}.
  Context {rp : ring_like_prop T}.
  Context {Hic : rngl_mul_is_comm T = true}.
  Context {Hon : rngl_has_1 T = true}.
  Context {Hop : rngl_has_opp T = true}.
  Add Ring rngl_ring : (rngl_ring_theory Hic Hop Hon).
>>

A typical example (you must stay in this section):
<<
  Example a2_b2 : ∀ a b, ((a + b) * (a - b) = a * a - b * b)%L.
  Proof.
  intros.
  ring_simplify. (* just to see what happens *)
  easy.
  Qed.
>>
*)

From Stdlib Require Import Ring_theory.
From Stdlib Require Import Field_theory.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hic : rngl_mul_is_comm T = true).
Context (Hop : rngl_has_opp T = true).
Context (Hon : rngl_has_1 T = true).

Definition rngl_ring_theory
    : ring_theory 0%L 1%L rngl_add rngl_mul rngl_sub rngl_opp eq :=
  {| Radd_0_l := rngl_add_0_l;
     Radd_comm := rngl_add_comm;
     Radd_assoc := rngl_add_assoc;
     Rmul_1_l := rngl_mul_1_l Hon;
     Rmul_comm := rngl_mul_comm Hic;
     Rmul_assoc := rngl_mul_assoc;
     Rdistr_l := rngl_mul_add_distr_r;
     Rsub_def x y := eq_sym (rngl_add_opp_r Hop x y);
     Ropp_def := rngl_add_opp_diag_r Hop |}.

Context (Hiv : rngl_has_inv T = true).
Context (Hc1 : rngl_characteristic T ≠ 1).

Theorem rngl_Finv_l : ∀ p : T, p ≠ 0%L → (p⁻¹ * p)%L = 1%L.
Proof.
intros * Hpz.
specialize rngl_opt_mul_inv_diag_l as H1.
rewrite Hiv, Hon in H1; cbn in H1.
now apply H1.
Qed.

Definition rngl_field_theory :
  field_theory 0%L 1%L rngl_add rngl_mul rngl_sub rngl_opp
    rngl_div rngl_inv eq :=
  {| F_R := rngl_ring_theory;
     F_1_neq_0 := rngl_1_neq_0 Hon Hc1;
     Fdiv_def := rngl_div_eq_inv_r Hiv;
     Finv_l := rngl_Finv_l |}.

(** ** Commutative field

Define the typical properties of what a commutative field
in mathematics is. *)

Record charac_0_field :=
  { cf_has_1 : rngl_has_1 T = true;
    cf_mul_is_comm : rngl_mul_is_comm T = true;
    cf_has_opp : rngl_has_opp T = true;
    cf_has_inv : rngl_has_inv T = true;
    cf_has_eq_dec : rngl_has_eq_dec T = true;
    cf_characteristic : rngl_characteristic T = 0 }.

End a.

Arguments rngl_characteristic_1 {T ro rp} Hon Hos Hch x%_L.
Arguments rngl_mul_assoc {T ro rp} (a b c)%_L : rename.
Arguments rngl_mul_comm {T ro rp} Hic (a b)%_L.
Arguments rngl_mul_mul_swap {T ro rp} Hic (a b c)%_L.
Arguments rngl_mul_0_r {T ro rp} Hom a%_L.
Arguments rngl_mul_1_r {T ro rp} Hon a%_L.
Arguments rngl_mul_2_l {T ro rp} Hon a%_L.
Arguments rngl_pow_squ {T ro rp} Hon a%_L n%_nat.

Arguments charac_0_field T%_type {ro rp}.
