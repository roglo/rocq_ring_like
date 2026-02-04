Set Nested Proofs Allowed.

Require Import Stdlib.ZArith.ZArith.
Require Import Init.Nat.
Import List.ListNotations.
Require Import RingLike.Utf8.

Require Import RingLike.Core.
(*
Require Import RingLike.IterAdd.
Require Import RingLike.RealLike.
Require Import RingLike.Misc.
Require Import TrigoWithoutPi.Core.
Require Import TrigoWithoutPi.Distance.
Require Import TrigoWithoutPi.AngleDiv2Add.

Require Import Misc.

Notation "x ≤ y" := (Z.le x y) : Z_scope.
*)

(* general complex whose real and imaginary parts are of type T
   that is not necessarily the real numbers *)

Class GComplex T := mk_gc {gre : T; gim : T}.

(*
Declare Scope gc_scope.
Delimit Scope gc_scope with C.
Bind Scope gc_scope with GComplex.
*)

Arguments mk_gc {T} gre%_L gim%_L.
Arguments gre {T} GComplex%_L.
Arguments gim {T} GComplex%_L.

(*
Arguments rngl_opt_eq_dec T {ring_like_op}.
Arguments rngl_opt_inv_or_pdiv T {ring_like_op}.
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
(*
Context {rp : ring_like_prop T}.

Theorem eq_gc_eq :
  ∀ a b : GComplex T, gre a = gre b ∧ gim a = gim b ↔ a = b.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct a, b; cbn in Hab.
now f_equal.
Qed.

Theorem neq_gc_neq :
  ∀ a b : GComplex T, gre a ≠ gre b ∨ gim a ≠ gim b → a ≠ b.
Proof.
intros * Hab.
intros H; subst b.
now destruct Hab.
Qed.

Theorem neq_neq_GComplex :
  rngl_has_eq_dec T = true →
  ∀ a b : GComplex T, a ≠ b → gre a ≠ gre b ∨ gim a ≠ gim b.
Proof.
intros Hed.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hab.
destruct a as (ra, ia).
destruct b as (rb, ib); cbn.
destruct (rngl_eqb_dec ra rb) as [Hrab| Hrab]. {
  apply (rngl_eqb_eq Heo) in Hrab.
  subst rb; right.
  now intros Hiab; apply Hab; clear Hab; subst ib.
} {
  apply (rngl_eqb_neq Heo) in Hrab.
  now left.
}
Qed.
*)

Definition gc_zero : GComplex T := {| gre := 0; gim := 0 |}.
Definition gc_one : GComplex T := {| gre := 1; gim := 0 |}.

Definition gc_add (ca cb : GComplex T) :=
  {| gre := gre ca + gre cb; gim := gim ca + gim cb |}.

(*
Definition gc_sub (ca cb : GComplex T) :=
  {| gre := gre ca - gre cb; gim := gim ca - gim cb |}.

Definition gc_opp (c : GComplex T) :=
  {| gre := - gre c; gim := - gim c |}.
*)

Definition gc_mul (ca cb : GComplex T) :=
  {| gre := (gre ca * gre cb - gim ca * gim cb)%L;
     gim := (gim ca * gre cb + gre ca * gim cb)%L |}.

Definition gc_inv c :=
  let d := (gre c * gre c + gim c * gim c)%L in
  mk_gc (gre c / d) (- gim c / d)%L.

(*
Definition gc_div (ca cb : GComplex T) :=
  gc_mul ca (gc_inv cb).
*)

Definition gc_opt_opp_or_psub :
    option
      ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T))
  :=
  match rngl_opt_opp_or_psub T with
  | Some (inl opp) =>
      Some (inl (λ c, mk_gc (opp (gre c)) (opp (gim c))))
  | Some (inr psub) =>
      Some (inr (λ c d, mk_gc (psub (gre c) (gre d)) (psub (gim c) (gim d))))
  | None =>
      None
  end.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition gc_opt_inv_or_pdiv :
  option
    ((GComplex T → GComplex T) + (GComplex T → GComplex T → GComplex T)) :=
  match rngl_opt_inv_or_pdiv T with
  | Some (inl inv) => if rngl_mul_is_comm T then Some (inl gc_inv) else None
  | Some (inr pdiv) => None (* à voir *)
  | None => None
  end.

(*
(* to be moved *)
Theorem rl_integral_modulus_prop :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b : T, (rngl_squ a + rngl_squ b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Hop Hiq Hto * Hab.
now apply (eq_rngl_add_square_0 Hop Hiq Hto) in Hab.
Qed.
*)

Theorem gc_eq_dec :
  rngl_has_eq_dec_or_order T = true →
  ∀ a b : GComplex T, {a = b} + {a ≠ b}.
Proof.
intros Heo.
intros.
destruct a as (ra, ia).
destruct b as (rb, ib).
destruct (rngl_eqb_dec ra rb) as [H1| H1]. {
  apply (rngl_eqb_eq Heo) in H1.
  subst rb.
  destruct (rngl_eqb_dec ia ib) as [H2| H2]. {
   apply (rngl_eqb_eq Heo) in H2.
   now subst ib; left.
  }
  apply (rngl_eqb_neq Heo) in H2.
  right.
  intros H; apply H2.
  now injection H.
} {
  apply (rngl_eqb_neq Heo) in H1.
  right.
  intros H; apply H1.
  now injection H.
}
Qed.

Definition gc_opt_is_zero_divisor : option (GComplex T → Prop) :=
  Some (λ z, ((gre z)² + (gim z)² = 0)%L).

Definition gc_opt_eq_dec : option (∀ a b : GComplex T, {a = b} + {a ≠ b}) :=
  match Bool.bool_dec (rngl_has_eq_dec T) true with
  | left Hed =>
       let Heo := rngl_has_eq_dec_or_is_ordered_l Hed in
       Some (gc_eq_dec Heo)
  | right _ => None
  end.

End a.

Arguments gc_opt_opp_or_psub T {ro}.
Arguments gc_opt_inv_or_pdiv T {ro rp}.

Instance gc_ring_like_op T {ro : ring_like_op T} {rp : ring_like_prop T} :
  ring_like_op (GComplex T) :=
  {| rngl_zero := gc_zero;
     rngl_one := gc_one;
     rngl_add := gc_add;
     rngl_mul := gc_mul;
     rngl_opt_opp_or_psub := gc_opt_opp_or_psub T;
     rngl_opt_inv_or_pdiv := gc_opt_inv_or_pdiv T;
     rngl_opt_is_zero_divisor := gc_opt_is_zero_divisor;
     rngl_opt_eq_dec := gc_opt_eq_dec;
     rngl_opt_leb := None |}.

...

Definition gc_pow_nat {T}
    {ro : ring_like_op T} {rp : ring_like_prop T} {rl : real_like_prop T}
    (z : GComplex T) n :=
  @rngl_power (GComplex T) (gc_ring_like_op T) z n.

Notation "0" := gc_zero : gc_scope.
Notation "1" := gc_one : gc_scope.
Notation "x + y" := (gc_add x y) : gc_scope.
Notation "x - y" := (gc_sub x y) : gc_scope.
Notation "x * y" := (gc_mul x y) : gc_scope.
Notation " x / y" := (gc_div x y) : gc_scope.
Notation "- x" := (gc_opp x) : gc_scope.
Notation "x ⁻¹" := (gc_inv x) : gc_scope.
Notation "x +ℹ y" := (mk_gc x y) (at level 50) : gc_scope.
Notation "z ^ n" := (gc_pow_nat z n) : gc_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

(* to be moved *)
Theorem rngl_between_opp_1_and_1 :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (a² ≤ 1 → -1 ≤ a ≤ 1)%L.
Proof.
intros Hop Hiq Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Ha.
rewrite <- rngl_squ_1 in Ha.
apply (rngl_squ_le_abs_le Hop Hiq Hto) in Ha.
rewrite (rngl_abs_1 Hos Hto) in Ha.
now apply (rngl_abs_le Hop Hto) in Ha.
Qed.

Theorem gc_add_comm : ∀ a b : GComplex T, (a + b)%L = (b + a)%L.
Proof.
intros; cbn.
progress unfold gc_add.
f_equal; apply rngl_add_comm.
Qed.

Theorem gc_add_assoc :
  ∀ a b c : GComplex T, (a + (b + c))%C = (a + b + c)%C.
Proof.
intros; cbn.
progress unfold gc_add; cbn.
f_equal; apply rngl_add_assoc.
Qed.

Theorem gc_add_0_l :
  ∀ a : GComplex T, (0 + a)%C = a.
Proof.
intros; cbn.
progress unfold gc_add; cbn.
do 2 rewrite rngl_add_0_l.
now apply eq_gc_eq.
Qed.

Theorem gc_add_0_r :
  ∀ a : GComplex T, (a + 0)%C = a.
Proof.
intros; cbn.
progress unfold gc_add; cbn.
do 2 rewrite rngl_add_0_r.
now apply eq_gc_eq.
Qed.

Theorem gc_mul_assoc :
  rngl_has_opp T = true →
  ∀ a b c : GComplex T, (a * (b * c))%C = (a * b * c)%C.
Proof.
intros * Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold gc_mul; cbn.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite rngl_mul_add_distr_l.
do 2 rewrite rngl_mul_add_distr_r.
do 8 rewrite rngl_mul_assoc.
do 2 rewrite <- (rngl_sub_add_distr Hos).
f_equal. {
  f_equal.
  rewrite rngl_add_comm.
  symmetry.
  apply rngl_add_assoc.
} {
  unfold rngl_sub; rewrite Hop.
  do 2 rewrite <- rngl_add_assoc.
  f_equal.
  rewrite (rngl_add_opp_l Hop).
  rewrite (rngl_add_opp_r Hop).
  symmetry.
  apply (rngl_add_sub_assoc Hop).
}
Qed.

Theorem gc_opt_mul_1_l :
  rngl_has_opp_or_psub T = true →
  ∀ a : GComplex T, (1 * a)%L = a.
Proof.
intros * Hos.
intros; cbn.
progress unfold gc_mul.
apply eq_gc_eq; cbn.
specialize rngl_mul_1_l as H1.
progress unfold "1"%L in H1; cbn in H1.
progress unfold "1"%L; cbn.
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_l.
Qed.

Theorem gc_mul_add_distr_l :
  rngl_has_opp T = true →
  ∀ a b c : GComplex T, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros * Hop *; cbn.
apply eq_gc_eq; cbn.
progress unfold rngl_sub; rewrite Hop.
do 4 rewrite rngl_mul_add_distr_l.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_sub_swap Hop).
progress unfold rngl_sub; rewrite Hop.
do 4 rewrite <- rngl_add_assoc.
split; f_equal. {
  now rewrite rngl_add_assoc, rngl_add_comm.
} {
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc; f_equal.
  apply rngl_add_comm.
}
Qed.

Theorem gc_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ a b : GComplex T, (a * b)%L = (b * a)%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_comm Hic (gre b)).
do 2 rewrite (rngl_mul_comm Hic (gim b)).
split; [ easy | ].
apply rngl_add_comm.
Qed.

Theorem gc_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ a b, (a * b = b * a)%C.
Proof.
intros Hic.
specialize gc_opt_mul_comm as H1.
now rewrite Hic in H1.
Qed.

Theorem gc_opt_mul_1_r :
  rngl_has_opp_or_psub T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ a : GComplex T, (a * 1)%L = a.
Proof.
intros * Hos.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_gc_eq; cbn.
specialize rngl_mul_1_r as H1.
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
Qed.

Theorem gc_opt_mul_add_distr_r :
  rngl_has_opp T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c : GComplex T, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros * Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_gc_eq; cbn.
do 4 rewrite rngl_mul_add_distr_r.
progress unfold rngl_sub.
rewrite Hop.
rewrite (rngl_opp_add_distr Hop).
rewrite (rngl_opp_sub_swap Hop).
do 4 rewrite <- rngl_add_assoc.
split; f_equal. {
  progress unfold rngl_sub.
  rewrite Hop.
  do 2 rewrite rngl_add_assoc.
  rewrite rngl_add_add_swap; f_equal.
  apply rngl_add_comm.
} {
  rewrite rngl_add_comm.
  rewrite <- rngl_add_assoc; f_equal.
  apply rngl_add_comm.
}
Qed.

Theorem gc_opt_add_opp_diag_l :
  rngl_has_opp T = true →
  if rngl_has_opp (GComplex T) then ∀ a : GComplex T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros * Hop.
remember (rngl_has_opp (GComplex T)) as opc eqn:Hopc; symmetry in Hopc.
destruct opc; [ | easy ].
intros.
apply eq_gc_eq; cbn.
specialize (rngl_add_opp_diag_l Hop) as H1.
progress unfold rngl_opp; cbn.
progress unfold gc_opt_opp_or_psub; cbn.
progress unfold rngl_has_opp in Hop.
progress unfold rngl_opp in H1.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ cbn | easy ].
now do 2 rewrite H1.
Qed.

Theorem gc_opt_add_sub :
  rngl_has_psub T = false →
  if rngl_has_psub (GComplex T) then ∀ a b : GComplex T, (a + b - b)%L = a
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_psub; cbn.
progress unfold gc_opt_opp_or_psub.
progress unfold rngl_has_psub in Hsu.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem gc_opt_sub_add_distr :
  rngl_has_psub T = false →
  if rngl_has_psub (GComplex T) then
    ∀ a b c : GComplex T, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_psub; cbn.
progress unfold gc_opt_opp_or_psub.
progress unfold rngl_has_psub in Hsu.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem gc_inv_re :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gre a⁻¹ = (gre a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros Hic Hiv * Haz.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
progress unfold rngl_inv; cbn.
progress unfold gc_opt_inv_or_pdiv.
progress unfold rngl_has_inv_or_pdiv in Hiq.
progress unfold rngl_has_inv in Hiv.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
destruct iq; [ | easy ].
now rewrite Hic.
Qed.

Theorem gc_inv_im :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ a : GComplex T, a ≠ 0%L →
  gim a⁻¹ = (- gim a / (gre a * gre a + gim a * gim a))%L.
Proof.
intros Hic Hiv * Haz.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
progress unfold rngl_inv; cbn.
progress unfold gc_opt_inv_or_pdiv.
progress unfold rngl_has_inv_or_pdiv in Hiq.
progress unfold rngl_has_inv in Hiv.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
destruct iq; [ | easy ].
now rewrite Hic.
Qed.

Theorem gc_opt_mul_inv_diag_l :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  if rngl_has_inv (GComplex T) then
    ∀ a : GComplex T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
intros Hic Hop Hiv Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
cbn.
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
intros * Haz.
apply eq_gc_eq; cbn.
specialize (rngl_mul_inv_diag_l Hiv) as H1.
rewrite (gc_inv_re Hic Hiv); [ | now intros H; subst a ].
rewrite (gc_inv_im Hic Hiv); [ | now intros H; subst a ].
progress unfold rngl_sub.
progress unfold rngl_div.
rewrite Hop, Hiv.
rewrite (rngl_mul_mul_swap Hic (gre a)).
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_mul_swap Hic (gim a)).
rewrite (rngl_opp_involutive Hop).
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_comm Hic).
split. {
  rewrite H1; [ easy | ].
  intros H2.
  apply (eq_rngl_add_square_0 Hop Hiq Hto) in H2.
  apply Haz.
  apply eq_gc_eq; cbn.
  now f_equal.
} {
  rewrite (rngl_mul_opp_l Hop).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_add_opp_l Hop).
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic).
  apply (rngl_sub_diag Hos).
}
Qed.

Theorem gc_opt_mul_inv_diag_r :
  if (rngl_has_inv (GComplex T) && negb (rngl_mul_is_comm T))%bool then
    ∀ a : GComplex T, a ≠ 0%L → (a * a⁻¹)%L = 1%L
  else not_applicable.
Proof.
cbn.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ now rewrite Bool.andb_false_r | ].
rewrite Bool.andb_true_r.
remember (rngl_has_inv (GComplex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
progress unfold rngl_has_inv in Hivc; cbn in Hivc.
progress unfold gc_opt_inv_or_pdiv in Hivc.
rewrite Hic in Hivc.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem gc_opt_mul_div :
  if rngl_has_pdiv (GComplex T) then
    ∀ a b : GComplex T, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
progress unfold rngl_has_pdiv; cbn.
progress unfold gc_opt_inv_or_pdiv.
remember (rngl_opt_inv_or_pdiv T) as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [iq| ]; [ | easy ].
destruct iq as [inv| pdiv]; [ | easy ].
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
now destruct ic.
Qed.

Theorem gc_integral :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_or_pdiv T && rngl_has_eq_dec_or_order T)%bool =
     true →
  ∀ a b : GComplex T,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros Hic Hop Hio.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hab.
right; right.
progress unfold rngl_is_zero_divisor.
cbn.
injection Hab; intros H1 H2.
apply (f_equal (rngl_mul (gim a))) in H1.
apply (f_equal (rngl_mul (gre a))) in H2.
rewrite rngl_mul_add_distr_l in H1.
rewrite (rngl_mul_sub_distr_l Hop) in H2.
do 2 rewrite rngl_mul_assoc in H1, H2.
rewrite (rngl_mul_comm Hic (gim a) (gre a)) in H1.
rewrite (rngl_mul_0_r Hos) in H1, H2.
rewrite fold_rngl_squ in H1, H2.
eapply (f_equal (rngl_add 0)) in H1.
rewrite <- H2 in H1 at 1.
rewrite rngl_add_assoc in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_add Hop) in H1.
rewrite <- rngl_mul_add_distr_r in H1.
rewrite rngl_add_0_l in H1.
apply (rngl_integral Hos Hio) in H1.
destruct H1 as [H1| H1]; [ now left | ].
rewrite H1 in H2 |-*.
rewrite (rngl_mul_0_r Hos) in H2.
rewrite (rngl_sub_0_l Hop) in H2.
apply (f_equal rngl_opp) in H2.
rewrite (rngl_opp_involutive Hop) in H2.
rewrite (rngl_opp_0 Hop) in H2.
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_l.
apply (rngl_integral Hos Hio) in H2.
destruct H2 as [H2| H2]. 2: {
  rewrite H2, (rngl_squ_0 Hos).
  now right.
}
apply (rngl_integral Hos Hio) in H2.
destruct H2 as [H2| H2]. {
  rewrite H2, (rngl_squ_0 Hos).
  rewrite rngl_add_0_l.
  injection Hab; intros H3 H4.
  rewrite H2 in H4.
  rewrite (rngl_mul_0_l Hos) in H4.
  rewrite (rngl_sub_0_l Hop) in H4.
  apply (f_equal rngl_opp) in H4.
  rewrite (rngl_opp_involutive Hop) in H4.
  rewrite (rngl_opp_0 Hop) in H4.
  apply (rngl_integral Hos Hio) in H4.
  destruct H4 as [H4| H4]. {
    rewrite H4, (rngl_squ_0 Hos).
    now left.
  } {
    rewrite H4, (rngl_squ_0 Hos).
    now right.
  }
} {
  rewrite H2, (rngl_squ_0 Hos).
  rewrite rngl_add_0_r.
  injection Hab; intros H3 H4.
  rewrite H2 in H3.
  rewrite (rngl_mul_0_l Hos) in H3.
  rewrite rngl_add_0_l in H3.
  apply (rngl_integral Hos Hio) in H3.
  destruct H3 as [H3| H3]. {
    rewrite H3, (rngl_squ_0 Hos).
    now left.
  } {
    rewrite H3, (rngl_squ_0 Hos).
    now right.
  }
}
(*
intros Hic Hop Heo Hio.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hab.
now right; right; left.
*)
Qed.

Theorem gc_characteristic_prop :
  if rngl_characteristic T =? 0 then ∀ i : nat, rngl_mul_nat 1 (S i) ≠ 0%C
  else
    (∀ i : nat, 0 < i < rngl_characteristic T → rngl_mul_nat 1 i ≠ 0%C)
    ∧ rngl_mul_nat 1 (rngl_characteristic T) = 0%C.
Proof.
cbn - [ rngl_mul_nat ].
specialize rngl_characteristic_prop as H1.
cbn - [ rngl_mul_nat ] in H1 |-*.
assert
  (Hr :
    ∀ n,
    @rngl_mul_nat _ (gc_ring_like_op T) (mk_gc 1 0) n =
    mk_gc (rngl_mul_nat 1 n) 0). {
  intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat; cbn.
  induction n; [ easy | cbn ].
  rewrite IHn.
  progress unfold gc_add; cbn.
  now rewrite rngl_add_0_l.
}
unfold "1"%L in Hr.
remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  cbn - [ rngl_mul_nat ] in H1 |-*; intros.
  apply neq_gc_neq.
  cbn - [ rngl_mul_nat ].
  left.
  specialize (H1 i).
  intros H2; apply H1; clear H1.
  progress unfold rngl_of_nat.
  now rewrite Hr in H2.
} {
  cbn - [ rngl_mul_nat ] in H1 |-*.
  destruct H1 as (H1, H2).
  split. {
    intros i Hi.
    apply neq_gc_neq.
    cbn; left.
    specialize (H1 i Hi).
    intros H3; apply H1; clear H1.
    progress unfold rngl_of_nat.
    now rewrite Hr in H3; cbn in H3.
  } {
    apply eq_gc_eq.
    cbn - [ rngl_mul_nat ].
    progress unfold rngl_of_nat in H2.
    now rewrite Hr.
  }
}
Qed.

Context {Hic : rngl_mul_is_comm T = true}.
Context {Hop : rngl_has_opp T = true}.
Context {Hiv : rngl_has_inv T = true}.
Context {Hto : rngl_is_totally_ordered T = true}.

Instance gc_ring_like_prop_not_alg_closed : ring_like_prop (GComplex T) :=
  let Hor := rngl_is_totally_ordered_is_ordered Hto in
  let Hos := rngl_has_opp_has_opp_or_psub Hop in
  let Hsu := rngl_has_opp_has_no_psub Hop in
  let Hio := rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := gc_add_comm;
     rngl_add_assoc := gc_add_assoc;
     rngl_add_0_l := gc_add_0_l;
     rngl_mul_assoc := gc_mul_assoc Hop;
     rngl_mul_1_l := gc_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := gc_mul_add_distr_l Hop;
     rngl_opt_mul_comm := gc_opt_mul_comm;
     rngl_opt_mul_1_r := gc_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := gc_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_diag_l := gc_opt_add_opp_diag_l Hop;
     rngl_opt_add_sub := gc_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := gc_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_diag_l := gc_opt_mul_inv_diag_l Hic Hop Hiv Hto;
     rngl_opt_mul_inv_diag_r := gc_opt_mul_inv_diag_r;
     rngl_opt_mul_div := gc_opt_mul_div;
     rngl_opt_integral := gc_integral Hic Hop Hio;
     rngl_opt_alg_closed := NA;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA;
     rngl_characteristic_prop := gc_characteristic_prop |}.

End a.

Arguments gc_ring_like_prop_not_alg_closed {T ro rp rl} Hic Hop Hiv Hto.

(* algebraically closed *)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition gc_modl (z : GComplex T) := rl_modl (gre z) (gim z).

Theorem le_rl_sqrt_add :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (0 ≤ b → a ≤ rl_sqrt (rngl_squ a + b))%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hzb.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
apply (rngl_le_trans Hor _ (rngl_abs a)). {
  apply (rngl_le_abs_diag Hop Hor).
}
apply (rngl_square_le_simpl_nonneg Hop Hiq Hto). {
  apply rl_sqrt_nonneg.
  apply (rngl_le_0_add Hos Hor); [ | easy ].
  apply (rngl_squ_nonneg Hos Hto).
}
do 2 rewrite fold_rngl_squ.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_le_0_add Hos Hor); [ | easy ].
  apply (rngl_squ_nonneg Hos Hto).
}
rewrite (rngl_squ_abs Hop).
now apply (rngl_le_add_r Hos Hor).
Qed.

Theorem rl_sqrt_div_squ_squ :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ x y, (x ≠ 0 ∨ y ≠ 0)%L →
  (-1 ≤ x / rl_sqrt (rngl_squ x + rngl_squ y) ≤ 1)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros * Hxyz.
assert (Hxy : (0 ≤ x² + y²)%L). {
  apply (rngl_le_0_add Hos Hor);
  apply (rngl_squ_nonneg Hos Hto).
}
split. {
  apply (rngl_le_div_r Hop Hiv Hto). {
    remember (rngl_squ x + rngl_squ y)%L as a eqn:Ha.
    symmetry in Ha.
    apply rngl_le_neq.
    split. {
      now apply rl_sqrt_nonneg.
    } {
      intros H3; symmetry in H3.
      apply (f_equal rngl_squ) in H3.
      progress unfold rngl_squ in H3 at 2.
      rewrite (rngl_mul_0_l Hos) in H3.
      rewrite rngl_squ_sqrt in H3; [ | easy ].
      move H3 at top; subst a.
      apply (rl_integral_modulus_prop Hop Hiq Hto) in Ha.
      now destruct Hxyz.
    }
  }
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  destruct (rngl_leb_dec 0 x) as [Hzx| Hzx]. {
    apply rngl_leb_le in Hzx.
    apply (rngl_le_trans Hor _ 0). {
      rewrite <- (rngl_opp_0 Hop).
      now apply -> (rngl_opp_le_compat Hop Hor).
    }
    now apply rl_sqrt_nonneg.
  } {
    apply rngl_leb_nle in Hzx.
    apply (rngl_nle_gt_iff Hto) in Hzx.
    apply (rngl_opp_lt_compat Hop Hor) in Hzx.
    rewrite (rngl_opp_0 Hop) in Hzx.
    rewrite <- (rngl_squ_opp Hop).
    apply (le_rl_sqrt_add Hop Hiv Hto).
    apply (rngl_squ_nonneg Hos Hto).
  }
} {
  apply (rngl_le_div_l Hop Hiv Hto). {
    remember (rngl_squ x + rngl_squ y)%L as a eqn:Ha.
    symmetry in Ha.
    apply rngl_le_neq.
    split. {
      now apply rl_sqrt_nonneg.
    } {
      intros H3; symmetry in H3.
      apply (f_equal rngl_squ) in H3.
      progress unfold rngl_squ in H3 at 2.
      rewrite (rngl_mul_0_l Hos) in H3.
      rewrite rngl_squ_sqrt in H3; [ | easy ].
      move H3 at top; subst a.
      apply (rl_integral_modulus_prop Hop Hiq Hto) in Ha.
      now destruct Hxyz.
    }
  }
  rewrite rngl_mul_1_l.
  destruct (rngl_leb_dec 0 x) as [Hzx| Hzx]. {
    apply (le_rl_sqrt_add Hop Hiv Hto).
    apply (rngl_squ_nonneg Hos Hto).
  } {
    apply rngl_leb_nle in Hzx.
    apply (rngl_nle_gt_iff Hto) in Hzx.
    apply (rngl_le_trans Hor _ 0). {
      now apply rngl_lt_le_incl.
    }
    now apply rl_sqrt_nonneg.
  }
}
Qed.

Arguments rl_sqrt_squ {T ro rp rl} Hto Hop a%_L.

Theorem polar :
  ∀ (z : GComplex T) ρ θ,
  ρ = √((gre z)² + (gim z)²)%L
  → θ =
       (if (0 ≤? gim z)%L then rngl_acos (gre z / ρ)%L
        else angle_opp (rngl_acos (gre z / ρ)%L))
  → z = mk_gc (ρ * rngl_cos θ) (ρ * rngl_sin θ).
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hρ Hθ.
  destruct z as (rz, iz).
  f_equal; rewrite H1; apply H1.
}
intros * Hρ Hθ.
destruct (gc_eq_dec Heo z gc_zero) as [Hz| Hz]. {
  destruct z as (zr, zi).
  progress unfold gc_zero in Hz.
  injection Hz; clear Hz; intros; subst zr zi.
  cbn in Hρ.
  progress unfold rngl_squ in Hρ.
  rewrite (rngl_mul_0_l Hos) in Hρ.
  rewrite rngl_add_0_l in Hρ.
  rewrite (rl_sqrt_0 Hop Hto Hii) in Hρ.
  rewrite Hρ.
  now do 2 rewrite (rngl_mul_0_l Hos).
}
subst θ.
destruct z as (zr, zi).
cbn in Hρ |-*.
assert (Hρz : ρ ≠ 0%L). {
  rewrite Hρ.
  intros H.
  apply (eq_rl_sqrt_0 Hos) in H. 2: {
    apply (rngl_le_0_add Hos Hor);
    apply (rngl_squ_nonneg Hos Hto).
  }
  apply (rl_integral_modulus_prop Hop Hiq Hto) in H.
  now destruct H; subst zr zi.
}
assert (Hzρ : (0 < ρ)%L). {
  apply not_eq_sym in Hρz.
  apply rngl_le_neq.
  split; [ | easy ].
  rewrite Hρ.
  apply rl_sqrt_nonneg.
  apply (rngl_le_0_add Hos Hor);
  apply (rngl_squ_nonneg Hos Hto).
}
assert (Hzr : zr = (ρ * (zr / ρ))%L). {
  rewrite (rngl_mul_comm Hic).
  now symmetry; apply (rngl_div_mul Hiv).
}
assert (Hr : zr = (ρ * rngl_cos (rngl_acos (zr / ρ)))%L). {
  rewrite rngl_cos_acos; [ easy | ].
  apply (rngl_between_opp_1_and_1 Hop Hiq Hto).
  rewrite <- rngl_squ_1.
  apply (rngl_abs_le_squ_le Hop Hto).
  rewrite (rngl_abs_1 Hos Hto).
  rewrite (rngl_abs_div Hop Hiv Hto); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor ρ). 2: {
    now apply rngl_lt_le_incl.
  }
  apply (rngl_le_div_l Hop Hiv Hto); [ easy | ].
  rewrite rngl_mul_1_l.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    rewrite Hρ.
    apply rl_sqrt_nonneg.
    apply (rngl_le_0_add Hos Hor);
    apply (rngl_squ_nonneg Hos Hto).
  }
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_le_0_add Hos Hor);
    apply (rngl_squ_nonneg Hos Hto).
  }
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_squ_nonneg Hos Hto).
}
f_equal; [ now destruct (0 ≤? zi)%L | ].
assert (Hri : ((zr / ρ)² + (zi / ρ)² = 1)%L). {
  rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
  rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
  progress unfold rngl_div.
  rewrite Hiv.
  rewrite <- rngl_mul_add_distr_r.
  rewrite (rngl_mul_inv_r Hiv).
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_le_0_add Hos Hor);
    apply (rngl_squ_nonneg Hos Hto).
  }
  apply (rngl_div_diag Hiq).
  intros H.
  apply (rl_integral_modulus_prop Hop Hiq Hto) in H.
  now move H at top; destruct H; subst zr zi.
}
assert (Hzρ21 : ((zr / ρ)² ≤ 1)%L). {
  rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
  apply (rngl_le_div_l Hop Hiv Hto). {
    now apply (rngl_mul_pos_pos Hop Hiq Hor).
  }
  rewrite rngl_mul_1_l.
  rewrite Hρ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_le_0_add Hos Hor);
    apply (rngl_squ_nonneg Hos Hto).
  }
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_squ_nonneg Hos Hto).
}
remember (0 ≤? zi)%L as zzi eqn:Hzzi; symmetry in Hzzi.
destruct zzi. {
  progress unfold rngl_acos.
  destruct (rngl_leb_dec (zr / ρ)² 1)%L as [Hzρ1| Hzρ1]. 2: {
    now apply rngl_leb_nle in Hzρ1.
  }
  apply rngl_leb_le in Hzzi.
  cbn.
  apply (rngl_add_sub_eq_l Hos) in Hri.
  rewrite Hri.
  rewrite (rl_sqrt_squ Hop Hto).
  rewrite (rngl_abs_div Hop Hiv Hto); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor ρ). 2: {
    now apply rngl_lt_le_incl.
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul Hiv); [ | easy ].
  symmetry.
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  cbn.
  rewrite (rngl_mul_opp_r Hop).
  apply (rngl_opp_inj Hop).
  rewrite (rngl_opp_involutive Hop).
  apply (rngl_leb_gt_iff Hto) in Hzzi.
  apply rngl_lt_le_incl in Hzzi.
  progress unfold rngl_acos.
  destruct (rngl_leb_dec (zr / ρ)² 1)%L as [Hzρ1| Hzρ1]. 2: {
    now apply rngl_leb_nle in Hzρ1.
  }
  cbn.
  apply (rngl_add_sub_eq_l Hos) in Hri.
  rewrite Hri.
  rewrite (rl_sqrt_squ Hop Hto).
  rewrite (rngl_abs_div Hop Hiv Hto); [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor ρ). 2: {
    now apply rngl_lt_le_incl.
  }
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_div_mul Hiv); [ | easy ].
  symmetry.
  now apply (rngl_abs_nonpos_eq Hop Hto).
}
Qed.

Definition seq_converging_to_rat (rad a b n : nat) :=
  (rngl_of_nat (a * rad ^ n / b) / rngl_of_nat rad ^ n)%L.

Theorem gc_cos_add_sin_add_is_mul :
  ∀ a b,
  (rngl_cos (a + b) +ℹ rngl_sin (a + b))%C =
  ((rngl_cos a +ℹ rngl_sin a) * (rngl_cos b +ℹ rngl_sin b))%C.
Proof. easy. Qed.

(* Moivre formula *)
Theorem gc_cos_sin_pow :
  ∀ a n,
  ((rngl_cos a +ℹ rngl_sin a) ^ n)%C =
  (rngl_cos (n * a) +ℹ rngl_sin (n * a))%C.
Proof.
intros.
progress unfold gc_pow_nat.
induction n; [ easy | ].
rewrite rngl_pow_succ_r.
rewrite IHn.
now apply eq_gc_eq.
Qed.

Theorem rngl_rat_frac_part_lt_1 :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b,
  rngl_of_nat b ≠ 0%L
  → (rngl_of_nat a / rngl_of_nat b - rngl_of_nat (a / b) < 1)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
intros * Hrbz.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  now rewrite (H1 (rngl_of_nat b)) in Hrbz.
}
assert (Hbz : b ≠ 0) by now intros H; subst b.
assert (Hzb : (0 < rngl_of_nat b)%L). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
  apply Nat.neq_0_lt_0.
  now intros H; subst b.
}
specialize (Nat.div_mod a b Hbz) as H1.
rewrite H1.
rewrite rngl_of_nat_add.
rewrite Nat.mul_comm.
rewrite Nat.div_add_l; [ | easy ].
rewrite (Nat.div_small (a mod b)). 2: {
  now apply Nat.mod_upper_bound.
}
rewrite Nat.add_0_r.
progress unfold rngl_div.
rewrite Hiv.
rewrite rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_inv_r Hiv).
rewrite (rngl_of_nat_mul Hos).
rewrite (rngl_mul_div Hi1); [ | easy ].
rewrite rngl_add_comm, (rngl_add_sub Hos).
apply (rngl_lt_div_l Hop Hiv Hto); [ easy | ].
rewrite rngl_mul_1_l.
apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
now apply Nat.mod_upper_bound.
Qed.

(* e.g. 1/5 = 1/8 + 1/16 + 1/128 + 1/256 + ...
   corresponding to 1/5 written in binary, which is
     [0; 0; 1; 1; 0; 0; 1; 1; 0; 0]
*)
Theorem rat_is_inf_sum_of_inv_rad_pow :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ rad a b,
  2 ≤ rad
  → rngl_of_nat b ≠ 0%L
  → is_limit_when_seq_tends_to_inf rngl_dist (seq_converging_to_rat rad a b)
       (rngl_of_nat a / rngl_of_nat b)%L.
Proof.
intros Hic Hop Hiv Hto Har.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * H2r Hbz.
intros ε Hε.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite H1 in Hε.
  now apply rngl_lt_irrefl in Hε.
}
specialize (int_part Hop Hc1 Hto Har) as H1.
destruct (H1 (1 / ε)%L) as (N, HN).
clear H1.
rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
  apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
  apply (rngl_0_le_1 Hos Hto).
}
assert (Hnε : (1 / rngl_of_nat (N + 1) < ε)%L). {
  apply (rngl_lt_div_l Hop Hiv Hto). {
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
    now rewrite Nat.add_comm.
  }
  rewrite <- (rngl_mul_comm Hic).
  now apply (rngl_lt_div_l Hop Hiv Hto).
}
assert (Hzr : (0 < rngl_of_nat rad)%L). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
  apply Nat.neq_0_lt_0.
  now intros H; subst rad.
}
assert (Hzb : (0 < rngl_of_nat b)%L). {
  rewrite <- rngl_of_nat_0.
  apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
  apply Nat.neq_0_lt_0.
  now intros H; subst b.
}
assert (Hzr' : rad ≠ 0) by now intros H; subst rad.
assert (Hzb' : b ≠ 0) by now intros H; subst b.
enough (H : ∃ M, ∀ m, M ≤ m → N + 1 ≤ rad ^ m). {
  destruct H as (M, HM).
  exists M.
  intros m Hm.
  eapply (rngl_le_lt_trans Hor); [ | apply Hnε ].
  clear ε Hε HN Hnε.
  progress unfold seq_converging_to_rat.
  cbn.
  progress unfold rngl_dist.
  rewrite (rngl_abs_nonpos_eq Hop Hto). 2: {
    apply (rngl_le_sub_0 Hop Hor).
    clear Hm.
    apply (rngl_le_div_r Hop Hiv Hto); [ easy | ].
    progress unfold rngl_div.
    rewrite Hiv.
    rewrite (rngl_mul_mul_swap Hic).
    rewrite <- (rngl_of_nat_pow Hos).
    rewrite (rngl_mul_inv_r Hiv).
    apply (rngl_le_div_l Hop Hiv Hto). {
      rewrite <- rngl_of_nat_0.
      apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
      apply Nat.neq_0_lt_0.
      now apply Nat.pow_nonzero.
    }
    do 2 rewrite <- (rngl_of_nat_mul Hos).
    apply (rngl_of_nat_inj_le Hos Hc1 Hto).
    rewrite Nat.mul_comm.
    eapply Nat.le_trans; [ apply Nat.Div0.div_mul_le | ].
    now rewrite Nat.mul_comm, Nat.div_mul.
  }
  rewrite (rngl_opp_sub_distr Hop).
  rewrite <- (rngl_of_nat_pow Hos).
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hto) with
    (c := rngl_of_nat (rad ^ m)). {
    rewrite <- rngl_of_nat_0.
    apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite <- (rngl_of_nat_mul Hos).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite <- (rngl_of_nat_mul Hos).
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite rngl_mul_1_l.
  rewrite (rngl_of_nat_mul Hos (a * rad ^ m / b)).
  rewrite (rngl_mul_div Hi1). 2: {
    rewrite (rngl_of_nat_pow Hos).
    apply (rngl_pow_neq_0 Hos Hiq).
    intros H.
    rewrite H in Hzr.
    now apply rngl_lt_irrefl in Hzr.
  }
  remember (a * rad ^ m) as c.
  apply (rngl_le_trans Hor _ 1%L). 2: {
    apply (rngl_le_div_r Hop Hiv Hto). {
      rewrite <- rngl_of_nat_0.
      apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
      now rewrite Nat.add_comm.
    }
    rewrite rngl_mul_1_l.
    apply (rngl_of_nat_inj_le Hos Hc1 Hto).
    now apply HM.
  }
  clear a Heqc.
  rename c into a.
  apply rngl_lt_le_incl.
  now apply rngl_rat_frac_part_lt_1.
}
enough (H : ∃ M : nat, ∀ m : nat, M ≤ m → N + 1 ≤ 2 ^ m). {
  destruct H as (M, HM).
  exists M.
  intros m Hm.
  apply (Nat.le_trans _ (2 ^ m)); [ now apply HM | ].
  now apply Nat.pow_le_mono_l.
}
exists (Nat.log2_up (N + 2)).
intros m Hm.
apply (Nat.pow_le_mono_r 2) in Hm; [ | easy ].
eapply Nat.le_trans; [ | apply Hm ].
eapply Nat.le_trans. 2: {
  apply Nat.log2_up_spec.
  rewrite Nat.add_comm; cbn.
  now apply -> Nat.succ_lt_mono.
}
apply Nat.add_le_mono_l.
now apply -> Nat.succ_le_mono.
Qed.

Theorem rat_is_inf_sum_of_inv_rad_pow' :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  rngl_is_archimedean T = true →
  ∀ rad a i c,
  2 ≤ rad
  → rngl_of_nat i ≠ 0%L
  → is_limit_when_seq_tends_to_inf rngl_dist
      (seq_converging_to_rat rad a i) c
  → rngl_of_nat a = (rngl_of_nat i * c)%L.
Proof.
intros Hic Hop Hiv Hto Har.
intros * H2r Hbz Hlim.
specialize (rat_is_inf_sum_of_inv_rad_pow Hic Hop Hiv Hto Har) as H1.
specialize (H1 _ a i H2r Hbz).
specialize (limit_unique Hop Hiv Hto (rngl_dist_is_dist Hop Hto)) as H2.
specialize (H2 _ _ _ Hlim H1).
subst c.
rewrite (rngl_mul_comm Hic).
symmetry.
now apply (rngl_div_mul Hiv).
Qed.

Arguments rl_sqrt_0 {T ro rp rl} Hop Hto Hii.

Theorem rngl_cos_le_anticompat_when_sin_nonneg :
  ∀ θ1 θ2,
  (0 ≤ rngl_sin θ1)%L
  → (0 ≤ rngl_sin θ2)%L
  → (rngl_cos θ1 ≤ rngl_cos θ2)%L ↔ (θ2 ≤ θ1)%A.
Proof.
intros * Hs1 Hs2.
progress unfold angle_leb.
apply rngl_leb_le in Hs1, Hs2.
rewrite Hs1, Hs2.
apply iff_sym.
apply rngl_leb_le.
Qed.

(*
Notation "⌊ a / b ⌋" := (div a b).
*)

Theorem one_sub_squ_cos_add_squ_sin :
  ∀ θ, ((1 - rngl_cos θ)² + (rngl_sin θ)² = 2 * (1 - rngl_cos θ))%L.
Proof.
destruct_ac; intros.
rewrite (rngl_squ_sub Hop Hic).
rewrite rngl_squ_1.
rewrite rngl_mul_1_r.
rewrite <- rngl_add_assoc.
rewrite cos2_sin2_1.
rewrite <- (rngl_add_sub_swap Hop).
apply (rngl_sub_mul_r_diag_l Hop).
Qed.

Theorem rngl_sin_incr :
  ∀ θ1 θ2,
  (θ1 ≤ θ2 ≤ angle_right)%A
  → (rngl_sin θ1 ≤ rngl_sin θ2)%L.
Proof.
destruct_ac.
intros * (H12, H2s).
progress unfold angle_leb in H12, H2s.
cbn in H2s.
specialize (rngl_0_le_1 Hos Hto) as H1.
apply rngl_leb_le in H1.
rewrite H1 in H2s; clear H1.
remember (0 ≤? rngl_sin θ1)%L as zs1 eqn:Hzs1.
remember (0 ≤? rngl_sin θ2)%L as zs2 eqn:Hzs2.
symmetry in Hzs1, Hzs2.
destruct zs2; [ | easy ].
destruct zs1; [ | easy ].
apply rngl_leb_le in Hzs1, Hzs2, H12, H2s.
apply rngl_cos_cos_sin_sin_nonneg_sin_le_cos_le_iff; try easy.
now apply (rngl_le_trans Hor _ (rngl_cos θ2)).
Qed.

Theorem rngl_cos_add_rngl_cos :
  ∀ p q,
  (rngl_cos p + rngl_cos q =
   2 *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite rngl_mul_1_r.
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_comm Hic (_ - _))%L.
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_comm Hic (_ * _)).
rewrite (rngl_add_sub Hos).
do 4 rewrite fold_rngl_squ.
do 2 rewrite (rngl_squ_mul Hic).
specialize (cos2_sin2_1 p2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 q2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_sub_sub_distr Hop _²)%L.
rewrite <- (rngl_add_sub_swap Hop _²)%L.
rewrite <- rngl_mul_2_l.
rewrite <- (rngl_add_sub_swap Hop (_ * _²))%L.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_add_assoc.
rewrite <- (rngl_mul_2_l _²)%L.
rewrite <- rngl_mul_add_distr_l.
rewrite (rngl_sub_mul_l_diag_l Hop).
f_equal.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite rngl_mul_1_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop _ _ (_ * _))%L.
rewrite (rngl_sub_diag Hos).
rewrite rngl_add_0_l.
rewrite (rngl_sub_sub_distr Hop).
rewrite rngl_add_comm.
apply (rngl_add_sub_swap Hop).
Qed.

Theorem rngl_cos_sub_rngl_cos :
  ∀ p q,
  (rngl_cos p - rngl_cos q =
   - (2%L *
      rngl_sin (angle_div_2 p + angle_div_2 q) *
      rngl_sin (angle_div_2 p - angle_div_2 q)))%L.
Proof.
destruct_ac; intros *.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite rngl_mul_1_r.
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_comm (_ * _)%L).
rewrite (rngl_sub_sub_distr Hop).
rewrite <- rngl_mul_assoc.
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_add_comm (rngl_cos p2 * _))%L.
rewrite (rngl_squ_sub_squ' Hop).
rewrite (rngl_mul_comm Hic (_ * _)).
rewrite (rngl_add_sub Hos).
do 4 rewrite fold_rngl_squ.
do 2 rewrite (rngl_squ_mul Hic).
specialize (cos2_sin2_1 p2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
specialize (cos2_sin2_1 q2) as H1.
apply (rngl_add_move_l Hop) in H1.
rewrite H1; clear H1.
rewrite (rngl_sub_sub_distr Hop _²)%L.
rewrite <- (rngl_add_sub_swap Hop _²)%L.
rewrite <- rngl_mul_2_l.
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_sub_add Hop).
rewrite <- (rngl_sub_add_distr Hos).
rewrite <- (rngl_mul_2_l _²)%L.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- (rngl_mul_opp_r Hop).
f_equal.
rewrite (rngl_mul_sub_distr_l Hop).
rewrite rngl_mul_1_r.
rewrite (rngl_mul_sub_distr_r Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_sub_sub_distr Hop).
rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_sub_add Hop).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_sin_add_rngl_sin :
  ∀ p q,
  (rngl_sin p + rngl_sin q =
   2 *
   rngl_sin (angle_div_2 p + angle_div_2 q) *
   rngl_cos (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite rngl_mul_1_r.
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite <- rngl_mul_assoc.
rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_mul_add_distr_r (_ * _))%L.
do 2 rewrite rngl_add_assoc.
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite <- (rngl_mul_assoc (rngl_sin p2 * _))%L.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite <- (rngl_mul_assoc (rngl_cos p2 * _))%L.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
rewrite fold_rngl_squ.
rewrite (rngl_add_add_swap (_ * _ * _ + _))%L.
rewrite (rngl_add_add_swap (_ * _ * _))%L.
rewrite (rngl_mul_comm Hic (rngl_sin p2)).
rewrite (rngl_mul_comm Hic (rngl_sin q2)).
rewrite <- rngl_mul_add_distr_r.
rewrite <- rngl_add_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite <- rngl_mul_2_l.
rewrite <- (rngl_mul_2_l (rngl_cos _)).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_l.
f_equal.
rewrite <- rngl_mul_add_distr_l.
rewrite cos2_sin2_1.
rewrite rngl_mul_1_r.
rewrite <- (rngl_add_assoc (rngl_cos p2 * _))%L.
rewrite (rngl_mul_mul_swap Hic).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite cos2_sin2_1.
now rewrite rngl_mul_1_l.
Qed.

Theorem rngl_sin_sub_rngl_sin :
  ∀ p q,
  (rngl_sin p - rngl_sin q =
   2%L *
   rngl_cos (angle_div_2 p + angle_div_2 q) *
   rngl_sin (angle_div_2 p - angle_div_2 q))%L.
Proof.
destruct_ac; intros *.
rewrite <- (angle_div_2_mul_2 p) at 1.
rewrite <- (angle_div_2_mul_2 q) at 1.
remember (angle_div_2 p) as p2.
remember (angle_div_2 q) as q2.
cbn.
do 4 rewrite rngl_mul_1_r.
do 4 rewrite (rngl_mul_0_r Hos).
do 2 rewrite (rngl_sub_0_r Hos).
do 2 rewrite rngl_add_0_r.
rewrite (rngl_mul_comm Hic (rngl_cos p2)).
rewrite <- rngl_mul_2_l.
rewrite (rngl_mul_comm Hic (rngl_cos q2)).
rewrite <- (rngl_mul_2_l (_ * _))%L.
rewrite <- (rngl_mul_sub_distr_l Hop).
rewrite <- rngl_mul_assoc.
f_equal.
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_sub_sub_distr Hop).
do 4 rewrite rngl_mul_assoc.
rewrite (rngl_mul_mul_swap Hic (rngl_cos p2)).
rewrite <- rngl_mul_assoc.
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
rewrite fold_rngl_squ.
rewrite (rngl_mul_mul_swap Hic (rngl_sin p2)).
rewrite <- (rngl_mul_assoc (_ * _))%L.
rewrite fold_rngl_squ.
do 2 rewrite <- (rngl_add_sub_swap Hop).
rewrite (rngl_mul_comm Hic (rngl_cos p2)).
rewrite <- rngl_mul_add_distr_l.
rewrite cos2_sin2_1.
rewrite rngl_mul_1_r.
rewrite <- (rngl_sub_add_distr Hos).
rewrite (rngl_mul_mul_swap Hic _ (rngl_cos q2)).
do 2 rewrite <- rngl_mul_assoc.
rewrite <- rngl_mul_add_distr_r.
rewrite rngl_add_comm.
rewrite cos2_sin2_1.
rewrite rngl_mul_1_l.
easy.
Qed.

Theorem angle_eucl_dist_sin_cos :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ∀ θ,
  ((angle_eucl_dist θ angle_right)² =
     (1 - rngl_sin θ)² + (rngl_cos θ)²)%L.
Proof.
intros Hop Hiq Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
cbn.
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_squ_opp Hop).
rewrite rngl_add_comm.
apply rngl_squ_sqrt.
apply (rngl_le_0_add Hos Hor);
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem rngl_sin_angle_eucl_dist_right_r :
  ∀ θ, (rngl_sin θ = 1 - (angle_eucl_dist θ angle_right)² / 2)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
specialize (angle_eucl_dist_sin_cos Hop Hiq Hto θ) as H1.
rewrite (rngl_squ_sub Hop Hic) in H1.
rewrite rngl_squ_1 in H1.
rewrite rngl_mul_1_r in H1.
rewrite rngl_add_add_swap in H1.
rewrite <- rngl_add_assoc in H1.
rewrite cos2_sin2_1 in H1.
rewrite <- (rngl_add_sub_swap Hop) in H1.
rewrite (rngl_sub_mul_r_diag_l Hop) in H1.
symmetry in H1.
apply (rngl_mul_move_l Hic Hi1) in H1. 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
now apply (rngl_sub_move_l Hop) in H1.
Qed.

Theorem rngl_sin_le_iff_angle_eucl_le :
  ∀ θ θ',
  (rngl_sin θ ≤ rngl_sin θ' ↔
     angle_eucl_dist θ' angle_right ≤ angle_eucl_dist θ angle_right)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  split; intros. {
    rewrite H1, (H1 (angle_eucl_dist _ _)).
    apply (rngl_le_refl Hor).
  } {
    rewrite H1, (H1 (rngl_sin _)).
    apply (rngl_le_refl Hor).
  }
}
assert (Hz1ss : ∀ θ, (0 ≤ 1 - rngl_sin θ)%L). {
  intros.
  apply (rngl_le_add_le_sub_r Hop Hor).
  rewrite rngl_add_0_l.
  apply rngl_sin_bound.
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
intros.
progress unfold angle_eucl_dist.
progress unfold rl_modl.
cbn.
do 2 rewrite (rngl_sub_0_l Hop).
do 2 rewrite (rngl_squ_sub Hop Hic).
rewrite rngl_squ_1.
rewrite rngl_mul_1_r.
do 2 rewrite (rngl_squ_opp Hop).
do 2 rewrite rngl_add_assoc.
do 2 rewrite (rngl_add_add_swap _ _ _²)%L.
do 2 rewrite cos2_sin2_1.
do 2 rewrite (rngl_add_sub_assoc Hop).
do 2 rewrite (rngl_sub_mul_r_diag_l Hop).
rewrite rl_sqrt_mul; [ | | easy ]. 2: {
  now apply rngl_lt_le_incl.
}
rewrite rl_sqrt_mul; [ | | easy ]. 2: {
  now apply rngl_lt_le_incl.
}
split; intros Hθθ. {
  apply (rngl_mul_le_mono_nonneg_l Hop Hor). {
    apply rl_sqrt_nonneg.
    now apply rngl_lt_le_incl.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    now apply rl_sqrt_nonneg.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
    now apply rl_sqrt_nonneg.
  }
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  rewrite rngl_squ_sqrt; [ | easy ].
  rewrite rngl_squ_sqrt; [ | easy ].
  now apply (rngl_sub_le_mono_l Hop Hor).
} {
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hto) in Hθθ. 2: {
    rewrite <- (rngl_abs_0 Hop).
    rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
      apply rl_sqrt_nonneg.
      now apply rngl_lt_le_incl.
    }
    apply (rngl_squ_lt_abs_lt Hop Hiq Hto).
    rewrite (rngl_squ_0 Hos).
    rewrite rngl_squ_sqrt; [ easy | ].
    now apply rngl_lt_le_incl.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor) in Hθθ. 2: {
    now apply rl_sqrt_nonneg.
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L in Hθθ. 2: {
    now apply rl_sqrt_nonneg.
  }
  apply (rngl_abs_le_squ_le Hop Hto) in Hθθ.
  rewrite rngl_squ_sqrt in Hθθ; [ | easy ].
  rewrite rngl_squ_sqrt in Hθθ; [ | easy ].
  now apply (rngl_sub_le_mono_l Hop Hor) in Hθθ.
}
Qed.

Theorem rl_sqrt_nonneg : ∀ a, (0 ≤ a → 0 ≤ √ a)%L.
Proof.
intros * Ha.
now apply rl_sqrt_nonneg.
Qed.

Theorem rngl_sin_div_2_pow_nat_nonneg :
  ∀ n θ, n ≠ 0 → (0 ≤ rngl_sin (angle_div_2_pow θ n))%L.
Proof.
intros * Hnz.
destruct n; [ easy | ].
rewrite angle_div_2_pow_succ_r_1.
apply rngl_sin_div_2_nonneg.
Qed.

Theorem rl_sqrt_div_2 :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (0 ≤ a → √(a / 2) = √(2 * a) / 2)%L.
Proof.
intros Hic Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hi1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  intros.
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  now rewrite (H1 √_)%L, (H1 (_ / _))%L.
}
intros * Hza.
assert (Hza2 : (0 ≤ a / 2)%L). {
  apply (rngl_le_div_r Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  now rewrite (rngl_mul_0_l Hos).
}
assert (Hz2a : (0 ≤ 2 * a)%L). {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  apply (rngl_0_le_2 Hos Hto).
}
assert (H2z : (2 ≠ 0)%L) by apply (rngl_2_neq_0 Hos Hc1 Hto).
rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_div_r Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_mul_0_l Hos).
  now apply rl_sqrt_nonneg.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
  now apply rl_sqrt_nonneg.
}
apply (eq_rngl_squ_rngl_abs Hop Hto). {
  now rewrite Bool.orb_true_iff; right.
} {
  apply (rngl_mul_comm Hic).
}
rewrite rngl_squ_sqrt; [ | easy ].
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
progress unfold rngl_squ.
rewrite <- (rngl_div_div Hos Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic).
now rewrite (rngl_mul_div Hi1).
Qed.

Theorem rngl_cos_div_pow_2_succ_r :
  ∀ n θ,
  (0 ≤ rngl_sin θ)%L
  → rngl_cos_div_pow_2 θ (S n) = rngl_cos_div_pow_2 (θ /₂) n.
Proof.
destruct_ac; intros * Hzs.
cbn.
induction n. {
  cbn.
  apply rngl_leb_le in Hzs.
  progress unfold rngl_signp.
  rewrite Hzs; symmetry.
  apply rngl_mul_1_l.
}
cbn.
now rewrite IHn.
Qed.

Theorem rngl_cos_pow_2_div_2_succ_nonneg :
  ∀ n θ, (0 ≤ rngl_cos_div_pow_2 (θ /₂) (S n))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite H1.
  apply (rngl_le_refl Hor).
}
intros.
cbn.
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hop Hiv Hto). 2: {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (rngl_le_opp_l Hop Hor).
apply rngl_cos_div_pow_2_div_2_bound.
Qed.

Theorem angle_div_2_not_straight :
  rngl_characteristic T ≠ 1 →
  ∀ θ, (θ /₂)%A ≠ angle_straight.
Proof.
destruct_ac.
intros Hc1.
intros * H.
apply eq_angle_eq in H.
injection H; clear H; intros Hs Hc.
progress unfold rngl_signp in Hc.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
symmetry in Hzs.
destruct zs. {
  rewrite rngl_mul_1_l in Hc.
  remember √((1 + rngl_cos θ) / 2)%L as a eqn:Ha.
  assert (H1 : (a < 0)%L). {
    rewrite Hc.
    apply (rngl_opp_1_lt_0 Hop Hc1 Hto).
  }
  apply (rngl_nle_gt Hor) in H1.
  apply H1; clear H1.
  rewrite Ha.
  apply rl_sqrt_nonneg.
  apply rngl_1_add_cos_div_2_nonneg.
}
apply (rngl_leb_gt_iff Hto) in Hzs.
rewrite (rngl_mul_opp_l Hop) in Hc.
rewrite rngl_mul_1_l in Hc.
apply (rngl_opp_inj Hop) in Hc.
apply (f_equal rngl_squ) in Hc.
rewrite rngl_squ_sqrt in Hc. 2: {
  apply rngl_1_add_cos_div_2_nonneg.
}
rewrite rngl_squ_1 in Hc.
apply (f_equal (λ x, (x * 2)%L)) in Hc.
rewrite (rngl_div_mul Hiv) in Hc. 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
rewrite rngl_mul_1_l in Hc.
apply (rngl_add_cancel_l Hos) in Hc.
apply eq_rngl_cos_1 in Hc.
rewrite Hc in Hzs.
cbn in Hzs.
now apply rngl_lt_irrefl in Hzs.
Qed.

Theorem rngl_cos_div_pow_2_incr :
  rngl_characteristic T ≠ 1 →
  ∀ n θ,
  (θ ≠ 0)%A
  → (rngl_cos_div_pow_2 (θ /₂) n < rngl_cos_div_pow_2 (θ /₂) (S n))%L.
Proof.
destruct_ac; intros Hc1.
intros * Htz.
destruct (rngl_eqb_dec (rngl_cos θ) (-1)%L) as [Ht1| Ht1]. {
  apply (rngl_eqb_eq Heo) in Ht1.
  apply eq_rngl_cos_opp_1 in Ht1.
  subst θ.
  rewrite angle_straight_div_2.
  remember angle_right as θ.
  assert (Hθ : (θ ≤ angle_right)%A) by (subst θ; apply angle_le_refl).
  assert (Hθz : (θ ≠ 0)%A). {
    intros H; rewrite H in Heqθ.
    injection Heqθ; intros H1 H2.
    now apply rngl_1_neq_0_iff in H2.
  }
  clear Heqθ.
  revert θ Hθ Hθz.
  induction n; intros. {
    now apply (rngl_cos_lt_sqrt_1_add_cos_div_2 Hc1).
  }
  assert (Hzs : (0 ≤ rngl_sin θ)%L). {
    progress unfold angle_leb in Hθ.
    cbn in Hθ.
    specialize (rngl_0_le_1 Hos Hto) as H1.
    apply rngl_leb_le in H1.
    rewrite H1 in Hθ; clear H1.
    apply rngl_leb_le.
    apply Bool.not_false_iff_true.
    now intros H; rewrite H in Hθ.
  }
  rewrite rngl_cos_div_pow_2_succ_r; [ | easy ].
  rewrite rngl_cos_div_pow_2_succ_r; [ | easy ].
  apply IHn. {
    apply (angle_le_trans _ θ); [ | easy ].
    apply angle_div_2_le.
  }
  intros H.
  now apply eq_angle_div_2_0 in H.
}
apply (rngl_eqb_neq Heo) in Ht1.
revert θ Htz Ht1.
induction n; intros. {
  cbn.
  progress unfold rngl_signp.
  remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs. {
    apply rngl_leb_le in Hzs.
    rewrite rngl_mul_1_l.
    apply (rl_sqrt_lt_rl_sqrt Hto). {
      apply rngl_1_add_cos_div_2_nonneg.
    }
    apply (rngl_div_lt_mono_pos_r Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    apply (rngl_add_lt_mono_l Hos Hor).
    remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
    symmetry in Hzc.
    destruct zc. 2: {
      apply (rngl_leb_gt_iff Hto) in Hzc.
      apply (rngl_lt_le_trans Hor _ 0); [ easy | ].
      apply rl_sqrt_nonneg.
      apply (rngl_le_div_r Hop Hiv Hto). {
        apply (rngl_0_lt_2 Hos Hc1 Hto).
      }
      rewrite (rngl_mul_0_l Hos).
      apply (rngl_le_opp_l Hop Hor).
      apply rngl_cos_bound.
    }
    apply rngl_leb_le in Hzc.
    now apply (rngl_cos_lt_sqrt_1_add_cos_div_2 Hc1).
  }
  apply (rngl_leb_gt_iff Hto) in Hzs.
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_lt_le_trans Hor _ 0). {
    apply (rngl_opp_neg_pos Hop Hor).
    apply (rl_sqrt_pos Hos Hor).
    apply rngl_le_neq.
    split; [ apply rngl_1_add_cos_div_2_nonneg | ].
    intros H; symmetry in H.
    progress unfold rngl_div in H.
    rewrite Hiv in H.
    apply (rngl_eq_mul_0_l Hos Hiq) in H. 2: {
      apply (rngl_inv_neq_0 Hos Hiv).
      apply (rngl_2_neq_0 Hos Hc1 Hto).
    }
    rewrite rngl_add_comm in H.
    now apply (rngl_add_move_0_r Hop) in H.
  }
  apply rl_sqrt_nonneg.
  apply (rngl_le_div_r Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_mul_0_l Hos).
  apply (rngl_le_0_sub Hop Hor).
  rewrite <- (rngl_abs_nonneg_eq Hop Hor). 2: {
    apply (rngl_0_le_1 Hos Hto).
  }
  rewrite <- (rngl_abs_nonneg_eq Hop Hor √_)%L. 2: {
    apply rl_sqrt_nonneg.
    apply (rngl_le_div_r Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite (rngl_mul_0_l Hos).
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  rewrite rngl_squ_sqrt. 2: {
    apply rngl_1_add_cos_div_2_nonneg.
  }
  rewrite rngl_squ_1.
  apply (rngl_div_le_1 Hop Hiv Hto). {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  split. {
    apply (rngl_le_opp_l Hop Hor).
    apply rngl_cos_bound.
  }
  apply (rngl_add_le_mono_l Hos Hor).
  apply rngl_cos_bound.
}
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  apply rngl_sin_div_2_nonneg.
}
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  apply rngl_sin_div_2_nonneg.
}
apply IHn. {
  intros H.
  now apply eq_angle_div_2_0 in H.
}
intros H.
apply eq_rngl_cos_opp_1 in H.
now apply (angle_div_2_not_straight Hc1) in H.
Qed.

Theorem squ_rngl_cos_non_0_div_pow_2_bound :
  rngl_characteristic T ≠ 1 →
  ∀ n θ,
  θ ≠ 0%A
  → (squ_rngl_cos_div_pow_2 θ n < 1)%L.
Proof.
destruct_ac.
intros Hc1.
intros * Htz.
induction n; cbn. {
  apply rngl_le_neq.
  split; [ apply rngl_cos_bound | ].
  intros H.
  now apply eq_rngl_cos_1 in H.
}
apply (rngl_lt_div_l Hop Hiv Hto).
apply (rngl_0_lt_2 Hos Hc1 Hto).
rewrite rngl_mul_1_l.
now apply (rngl_add_lt_mono_l Hos Hor).
Qed.

Theorem squ_rngl_cos_div_pow_2_incr :
  rngl_characteristic T ≠ 1 →
  ∀ n θ,
  θ ≠ 0%A
  → (squ_rngl_cos_div_pow_2 θ n < squ_rngl_cos_div_pow_2 θ (S n))%L.
Proof.
destruct_ac.
intros Hc1.
intros * Htz; cbn.
remember (squ_rngl_cos_div_pow_2 θ n) as a eqn:Ha.
apply (rngl_lt_div_r Hop Hiv Hto).
apply (rngl_0_lt_2 Hos Hc1 Hto).
rewrite (rngl_mul_comm Hic).
rewrite rngl_mul_2_l.
apply (rngl_add_lt_mono_r Hos Hor).
subst a.
now apply (squ_rngl_cos_non_0_div_pow_2_bound Hc1).
Qed.

Theorem angle_mul_0_l : ∀ θ, (0 * θ = 0)%A.
Proof. easy. Qed.

Theorem rngl_cos_div_2 :
  ∀ θ,
  rngl_cos (θ /₂) =
  ((if (0 ≤? rngl_sin θ)%L then 1%L else (-1)%L) *
   √((1 + rngl_cos θ) / 2))%L.
Proof. easy. Qed.

Theorem rngl_sin_div_2 :
  ∀ θ, rngl_sin (θ /₂) = √((1 - rngl_cos θ) / 2)%L.
Proof. easy. Qed.

Theorem sequence_false_min :
  ∀ n u,
  u 0 = false
  → u n = true
  → ∃ i, u i = false ∧ u (S i) = true.
Proof.
intros * Huz Hun.
revert u Huz Hun.
induction n; intros; [ now rewrite Huz in Hun | ].
rename Hun into Husn.
remember (u n) as un eqn:Hun.
symmetry in Hun.
destruct un; [ | now exists n ].
now apply IHn.
Qed.

Theorem angle_all_add_not_overflow :
  ∀ n θ,
  (∀ m, m < n → angle_add_overflow θ (m * θ) = false)
  ↔ angle_mul_nat_div_2π n θ = 0.
Proof.
destruct_ac.
intros.
split; intros Ha. {
  induction n; [ easy | ].
  rewrite angle_mul_nat_div_2π_succ_l_false.
  split; [ | now apply Ha ].
  apply IHn.
  intros m Hm.
  apply Ha.
  now apply Nat.lt_lt_succ_r.
} {
  intros m Hm.
  induction n; [ easy | ].
  rewrite angle_mul_nat_div_2π_succ_l_false in Ha.
  destruct Ha as (Ha1, Ha2).
  destruct (Nat.eq_dec m n) as [Hmen| Hmen]; [ now subst m | ].
  apply IHn; [ easy | ].
  flia Hm Hmen.
}
Qed.

Theorem rngl_cos_div_2_nonneg :
  ∀ θ,
  (0 ≤ rngl_sin θ)%L
  → (0 ≤ rngl_cos (θ /₂))%L.
Proof.
destruct_ac.
intros * Hzs.
cbn.
apply rngl_leb_le in Hzs.
progress unfold rngl_signp.
rewrite Hzs.
rewrite rngl_mul_1_l.
apply rl_sqrt_nonneg.
apply rngl_1_add_cos_div_2_nonneg.
Qed.

Theorem rngl_cos_div_pow_2_decr :
  ∀ n θ1 θ2,
  (θ2 ≤ θ1 ≤ angle_straight)%A
  → (rngl_cos_div_pow_2 θ1 n ≤ rngl_cos_div_pow_2 θ2 n)%L.
Proof.
destruct_ac.
intros * H21.
revert θ1 θ2 H21.
induction n; intros; [ now apply rngl_cos_decr | ].
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  destruct H21 as (_, H1).
  progress unfold angle_leb in H1.
  cbn in H1.
  rewrite (rngl_leb_refl Hor) in H1.
  remember (0 ≤? rngl_sin θ1)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  now apply rngl_leb_le in Hzs.
}
rewrite rngl_cos_div_pow_2_succ_r. 2: {
  assert (H2 : (θ2 ≤ angle_straight)%A) by now apply (angle_le_trans _ θ1).
  progress unfold angle_leb in H2.
  cbn in H2.
  rewrite (rngl_leb_refl Hor) in H2.
  remember (0 ≤? rngl_sin θ2)%L as zs eqn:Hzs.
  symmetry in Hzs.
  destruct zs; [ | easy ].
  now apply rngl_leb_le in Hzs.
}
apply IHn.
split; [ | apply angle_div_2_le_straight ].
now apply angle_div_2_le_compat.
Qed.

Definition two_straight_div_2_pow i :=
  match i with
  | 0 => 0%A
  | S i' => (angle_straight /₂^i')%A
  end.

Theorem angle_mul_succ_l : ∀ n θ, (S n * θ = θ + n * θ)%A.
Proof. easy. Qed.

Theorem eq_angle_mul_0 :
  ∀ n θ,
  (n * θ)%A = 0%A
  ↔ n = 0 ∨ rngl_cos (n * θ) = 1%L ∧ rngl_sin (n * θ) = 0%L.
Proof.
intros.
split; intros Hnt. {
  induction n; [ now left | right ].
  cbn in Hnt.
  progress unfold angle_add in Hnt.
  injection Hnt; clear Hnt; intros Hs Hc.
  rewrite <- rngl_cos_add in Hc.
  rewrite <- rngl_sin_add in Hs.
  rewrite <- angle_mul_succ_l in Hs, Hc.
  easy.
}
destruct Hnt as [Hnt| Hnt]. {
  subst n.
  apply angle_mul_0_l.
}
destruct Hnt as (Hc, Hs).
induction n; [ easy | cbn ].
progress unfold angle_add.
apply eq_angle_eq; cbn.
apply pair_equal_spec.
split; [ now rewrite <- rngl_cos_add | ].
now rewrite <- rngl_sin_add.
Qed.

Fixpoint rngl_cos_mul n θ :=
  match n with
  | 0 => 1%L
  | S n' =>
      (rngl_cos θ * rngl_cos_mul n' θ - rngl_sin θ * rngl_sin_mul n' θ)%L
  end
with rngl_sin_mul n θ :=
  match n with
  | 0 => 0%L
  | S n' =>
      (rngl_sin θ * rngl_cos_mul n' θ + rngl_cos θ * rngl_sin_mul n' θ)%L
  end.

Theorem rngl_cos_mul_sin_mul :
  ∀ n θ,
  rngl_cos (n * θ) = rngl_cos_mul n θ ∧
  rngl_sin (n * θ) = rngl_sin_mul n θ.
Proof.
intros.
induction n; intros; [ easy | cbn ].
destruct IHn as (Hc, Hs).
now rewrite Hc, Hs.
Qed.

Theorem rngl_cos_cos_mul :
  ∀ n θ, rngl_cos (n * θ) = rngl_cos_mul n θ.
Proof.
intros.
apply rngl_cos_mul_sin_mul.
Qed.

Theorem rngl_sin_sin_mul :
  ∀ n θ, rngl_sin (n * θ) = rngl_sin_mul n θ.
Proof.
intros.
apply rngl_cos_mul_sin_mul.
Qed.

Theorem rngl_2_x2_sub_1_le_x :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ∀ x, (0 ≤ x ≤ 1)%L → (2 * x² - 1 ≤ x)%L.
Proof.
intros Hop Hiq Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hx.
apply (rngl_le_sub_le_add_l Hop Hor).
apply (rngl_le_sub_le_add_r Hop Hor).
progress unfold rngl_squ.
rewrite rngl_mul_assoc.
rewrite (rngl_sub_mul_l_diag_r Hop).
destruct (rngl_leb_dec 0 (2 * x - 1)%L) as [Hz2c| H2cz]. {
  apply rngl_leb_le in Hz2c.
  rewrite <- (rngl_mul_1_r 1%L) at 4.
  apply (rngl_mul_le_compat_nonneg Hor); [ | easy ].
  split; [ easy | ].
  apply (rngl_le_sub_le_add_r Hop Hor).
  rewrite <- (rngl_mul_1_r 2%L) at 2.
  apply (rngl_mul_le_mono_nonneg_l Hop Hor); [ | easy ].
  apply (rngl_0_le_2 Hos Hto).
}
apply rngl_leb_nle in H2cz.
apply (rngl_nle_gt_iff Hto) in H2cz.
apply (rngl_le_trans Hor _ 0)%L. 2: {
  apply (rngl_0_le_1 Hos Hto).
}
apply rngl_lt_le_incl in H2cz.
now apply (rngl_mul_nonpos_nonneg Hop Hor).
Qed.

End a.
