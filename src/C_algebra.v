Set Nested Proofs Allowed.
Unset Suggest Proof Using.

Require Import Stdlib.ZArith.ZArith.
Require Import Init.Nat.
Import List.ListNotations.

Require Import Utf8.
Require Import Core.

(* general complex whose real and imaginary parts are of type T
   that is not necessarily the real numbers *)

Class Complex T := mk_c {Re : T; Im : T}.

Declare Scope c_scope.
Delimit Scope c_scope with C.
Bind Scope c_scope with Complex.

Arguments mk_c {T} Re%_L Im%_L.
Arguments Re {T} Complex%_C.
Arguments Im {T} Complex%_C.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Theorem eq_c_eq :
  ∀ z₁ z₂ : Complex T, Re z₁ = Re z₂ ∧ Im z₁ = Im z₂ ↔ z₁ = z₂.
Proof.
intros.
split; intros Hzz; [ | now subst ].
destruct z₁, z₂; cbn in Hzz.
now f_equal.
Qed.

Theorem neq_c_neq :
  ∀ z₁ z₂ : Complex T, Re z₁ ≠ Re z₂ ∨ Im z₁ ≠ Im z₂ → z₁ ≠ z₂.
Proof.
intros * Hzz.
intros H; subst.
now destruct Hzz.
Qed.

Definition c_zero : Complex T := {| Re := 0; Im := 0 |}.
Definition c_one : Complex T := {| Re := 1; Im := 0 |}.

Definition c_add (z₁ z₂ : Complex T) :=
  {| Re := Re z₁ + Re z₂; Im := Im z₁ + Im z₂ |}.

Definition c_mul (z₁ z₂ : Complex T) :=
  {| Re := (Re z₁ * Re z₂ - Im z₁ * Im z₂);
     Im := (Im z₁ * Re z₂ + Re z₁ * Im z₂) |}.

Definition c_inv z :=
  let z' := (Re z * Re z + Im z * Im z)%L in
  mk_c (Re z / z') (- Im z / z')%L.

Definition c_opt_opp_or_psub :
    option
      ((Complex T → Complex T) + (Complex T → Complex T → Complex T))
  :=
  match rngl_opt_opp_or_psub T with
  | Some (inl opp) =>
      Some (inl (λ c, mk_c (opp (Re c)) (opp (Im c))))
  | Some (inr psub) =>
      Some (inr (λ c d, mk_c (psub (Re c) (Re d)) (psub (Im c) (Im d))))
  | None =>
      None
  end.

End a.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition c_opt_inv_or_pdiv :
  option
    ((Complex T → Complex T) + (Complex T → Complex T → Complex T)) :=
  match rngl_opt_inv_or_pdiv T with
  | Some (inl inv) => if rngl_mul_is_comm T then Some (inl c_inv) else None
  | Some (inr pdiv) => None (* à voir *)
  | None => None
  end.

Theorem c_eq_dec :
  rngl_has_eq_dec_or_order T = true →
  ∀ z₁ z₂ : Complex T, {z₁ = z₂} + {z₁ ≠ z₂}.
Proof.
intros Heo.
intros.
destruct z₁ as (ra, ia).
destruct z₂ as (rb, ib).
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

Definition c_opt_is_zero_divisor : option (Complex T → Prop) :=
  Some (λ z, ((Re z)² + (Im z)² = 0)%L).

Definition c_opt_eq_dec :
    option (∀ z₁ z₂ : Complex T, {z₁ = z₂} + {z₁ ≠ z₂}) :=
  match Bool.bool_dec (rngl_has_eq_dec T) true with
  | left Hed =>
       let Heo := rngl_has_eq_dec_or_is_ordered_l Hed in
       Some (c_eq_dec Heo)
  | right _ => None
  end.

End a.

Arguments c_opt_opp_or_psub T {ro}.
Arguments c_opt_inv_or_pdiv T {ro rp}.

Instance c_ring_like_op T {ro : ring_like_op T} {rp : ring_like_prop T} :
  ring_like_op (Complex T) :=
  {| rngl_zero := c_zero;
     rngl_one := c_one;
     rngl_add := c_add;
     rngl_mul := c_mul;
     rngl_opt_opp_or_psub := c_opt_opp_or_psub T;
     rngl_opt_inv_or_pdiv := c_opt_inv_or_pdiv T;
     rngl_opt_is_zero_divisor := c_opt_is_zero_divisor;
     rngl_opt_eq_dec := c_opt_eq_dec;
     rngl_opt_leb := None |}.

Notation "0" := c_zero : c_scope.
Notation "1" := c_one : c_scope.
Notation "x + y" := (c_add x y) : c_scope.
Notation "x * y" := (c_mul x y) : c_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem c_add_comm : ∀ z₁ z₂ : Complex T, (z₁ + z₂)%C = (z₂ + z₁)%C.
Proof.
intros; cbn.
progress unfold c_add.
f_equal; apply rngl_add_comm.
Qed.

Theorem c_add_assoc :
  ∀ z₁ z₂ z₃ : Complex T, (z₁ + (z₂ + z₃))%C = ((z₁ + z₂) + z₃)%C.
Proof.
intros; cbn.
progress unfold c_add; cbn.
f_equal; apply rngl_add_assoc.
Qed.

Theorem c_add_0_l : ∀ z : Complex T, (0 + z)%C = z.
Proof.
intros; cbn.
progress unfold c_add; cbn.
do 2 rewrite rngl_add_0_l.
now destruct z.
Qed.

Theorem c_mul_assoc :
  rngl_has_opp T = true →
  ∀ z₁ z₂ z₃ : Complex T, (z₁ * (z₂ * z₃))%C = ((z₁ * z₂) * z₃)%C.
Proof.
intros * Hop *; cbn.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold c_mul; cbn.
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

Theorem c_mul_1_l :
  rngl_has_opp_or_psub T = true →
  ∀ z : Complex T, (1 * z)%C = z.
Proof.
intros * Hos.
intros; cbn.
progress unfold c_mul.
apply eq_c_eq; cbn.
specialize rngl_mul_1_l as H1.
progress unfold "1"%L in H1; cbn in H1.
progress unfold "1"%L; cbn.
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_l.
Qed.

Theorem c_mul_add_distr_l :
  rngl_has_opp T = true →
  ∀ z₁ z₂ z₃ : Complex T, (z₁ * (z₂ + z₃))%L = (z₁ * z₂ + z₁ * z₃)%L.
Proof.
intros * Hop *; cbn.
apply eq_c_eq; cbn.
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

Theorem c_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ z₁ z₂ : Complex T, (z₁ * z₂)%L = (z₂ * z₁)%L
  else not_applicable.
Proof.
intros; cbn.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_c_eq; cbn.
do 2 rewrite (rngl_mul_comm Hic (Re z₂)).
do 2 rewrite (rngl_mul_comm Hic (Im z₂)).
split; [ easy | ].
apply rngl_add_comm.
Qed.

Theorem c_opt_mul_1_r :
  rngl_has_opp_or_psub T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ z : Complex T, (z * 1)%L = z.
Proof.
intros * Hos.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_c_eq; cbn.
specialize rngl_mul_1_r as H1.
do 2 rewrite H1.
do 2 rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_r.
Qed.

Theorem c_opt_mul_add_distr_r :
  rngl_has_opp T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ z₁ z₂ z₃ : Complex T, ((z₁ + z₂) * z₃)%L = (z₁ * z₃ + z₂ * z₃)%L.
Proof.
intros * Hop.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_c_eq; cbn.
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

Theorem c_opt_add_opp_diag_l :
  rngl_has_opp T = true →
  if rngl_has_opp (Complex T) then ∀ z : Complex T, (- z + z)%L = 0%L
  else not_applicable.
Proof.
intros * Hop.
remember (rngl_has_opp (Complex T)) as opc eqn:Hopc; symmetry in Hopc.
destruct opc; [ | easy ].
intros.
apply eq_c_eq; cbn.
specialize (rngl_add_opp_diag_l Hop) as H1.
progress unfold rngl_opp; cbn.
progress unfold c_opt_opp_or_psub; cbn.
progress unfold rngl_has_opp in Hop.
progress unfold rngl_opp in H1.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
destruct os as [opp| psub]; [ cbn | easy ].
now do 2 rewrite H1.
Qed.

Theorem c_opt_add_sub :
  rngl_has_psub T = false →
  if rngl_has_psub (Complex T) then
    ∀ z₁ z₂ : Complex T, (z₁ + z₂ - z₂)%L = z₁
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_psub; cbn.
progress unfold c_opt_opp_or_psub.
progress unfold rngl_has_psub in Hsu.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem c_opt_sub_add_distr :
  rngl_has_psub T = false →
  if rngl_has_psub (Complex T) then
    ∀ z₁ z₂ z₃ : Complex T, (z₁ - (z₂ + z₃))%L = (z₁ - z₂ - z₃)%L
  else not_applicable.
Proof.
intros * Hsu.
progress unfold rngl_has_psub; cbn.
progress unfold c_opt_opp_or_psub.
progress unfold rngl_has_psub in Hsu.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem c_inv_re :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ z : Complex T, z ≠ 0%L →
  Re z⁻¹ = (Re z / (Re z * Re z + Im z * Im z))%L.
Proof.
intros Hic Hiv * Haz.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
progress unfold rngl_inv; cbn.
progress unfold c_opt_inv_or_pdiv.
progress unfold rngl_has_inv_or_pdiv in Hiq.
progress unfold rngl_has_inv in Hiv.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
destruct iq; [ | easy ].
now rewrite Hic.
Qed.

Theorem c_inv_im :
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  ∀ z : Complex T, z ≠ 0%L →
  Im z⁻¹ = (- Im z / (Re z * Re z + Im z * Im z))%L.
Proof.
intros Hic Hiv * Haz.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
progress unfold rngl_inv; cbn.
progress unfold c_opt_inv_or_pdiv.
progress unfold rngl_has_inv_or_pdiv in Hiq.
progress unfold rngl_has_inv in Hiv.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
destruct iq; [ | easy ].
now rewrite Hic.
Qed.

Theorem c_opt_mul_inv_diag_l :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  if rngl_has_inv (Complex T) then
    ∀ z : Complex T, z ≠ 0%L → (z⁻¹ * z)%L = 1%L
  else not_applicable.
Proof.
intros Hic Hop Hiv Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
cbn.
remember (rngl_has_inv (Complex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
intros * Haz.
apply eq_c_eq; cbn.
specialize (rngl_mul_inv_diag_l Hiv) as H1.
rewrite (c_inv_re Hic Hiv); [ | now intros H; subst ].
rewrite (c_inv_im Hic Hiv); [ | now intros H; subst ].
progress unfold rngl_sub.
progress unfold rngl_div.
rewrite Hop, Hiv.
rewrite (rngl_mul_mul_swap Hic (Re z)).
do 2 rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_mul_swap Hic (Im z)).
rewrite (rngl_opp_involutive Hop).
rewrite <- rngl_mul_add_distr_r.
rewrite (rngl_mul_comm Hic).
split. {
  rewrite H1; [ easy | ].
  intros H2.
  apply (eq_rngl_add_square_0 Hop Hiq Hto) in H2.
  apply Haz.
  apply eq_c_eq; cbn.
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

Theorem c_opt_mul_inv_diag_r :
  if (rngl_has_inv (Complex T) && negb (rngl_mul_is_comm T))%bool then
    ∀ z : Complex T, z ≠ 0%L → (z * z⁻¹)%L = 1%L
  else not_applicable.
Proof.
cbn.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ now rewrite Bool.andb_false_r | ].
rewrite Bool.andb_true_r.
remember (rngl_has_inv (Complex T)) as ivc eqn:Hivc; symmetry in Hivc.
destruct ivc; [ | easy ].
progress unfold rngl_has_inv in Hivc; cbn in Hivc.
progress unfold c_opt_inv_or_pdiv in Hivc.
rewrite Hic in Hivc.
destruct (rngl_opt_inv_or_pdiv T) as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem c_opt_mul_div :
  if rngl_has_pdiv (Complex T) then
    ∀ z₁ z₂ : Complex T, z₂ ≠ 0%L → (z₁ * z₂ / z₂)%L = z₁
  else not_applicable.
Proof.
progress unfold rngl_has_pdiv; cbn.
progress unfold c_opt_inv_or_pdiv.
remember (rngl_opt_inv_or_pdiv T) as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [iq| ]; [ | easy ].
destruct iq as [inv| pdiv]; [ | easy ].
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
now destruct ic.
Qed.

Theorem c_integral'' :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_or_pdiv T && rngl_has_eq_dec_or_order T)%bool =
     true →
  ∀ z₁ z₂ : Complex T,
  (z₁ * z₂)%C = 0%C
  → z₁ = 0%C ∨ z₂ = 0%C ∨ rngl_is_zero_divisor z₁ ∨ rngl_is_zero_divisor z₂.
Proof.
intros Hic Hop Hio.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hab.
right; right.
progress unfold rngl_is_zero_divisor.
cbn.
injection Hab; intros H1 H2.
apply (f_equal (rngl_mul (Im z₁))) in H1.
apply (f_equal (rngl_mul (Re z₁))) in H2.
rewrite rngl_mul_add_distr_l in H1.
rewrite (rngl_mul_sub_distr_l Hop) in H2.
do 2 rewrite rngl_mul_assoc in H1, H2.
rewrite (rngl_mul_comm Hic (Im z₁) (Re z₁)) in H1.
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
Qed.

Theorem c_characteristic_prop :
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
    @rngl_mul_nat _ (c_ring_like_op T) (mk_c 1 0) n =
    mk_c (rngl_mul_nat 1 n) 0). {
  intros.
  progress unfold rngl_mul_nat.
  progress unfold mul_nat; cbn.
  induction n; [ easy | cbn ].
  rewrite IHn.
  progress unfold c_add; cbn.
  now rewrite rngl_add_0_l.
}
unfold "1"%L in Hr.
remember (rngl_characteristic T) as ch eqn:Hch; symmetry in Hch.
destruct ch. {
  cbn - [ rngl_mul_nat ] in H1 |-*; intros.
  apply neq_c_neq.
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
    apply neq_c_neq.
    cbn; left.
    specialize (H1 i Hi).
    intros H3; apply H1; clear H1.
    progress unfold rngl_of_nat.
    now rewrite Hr in H3; cbn in H3.
  } {
    apply eq_c_eq.
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

Instance c_ring_like_prop_not_alg_closed : ring_like_prop (Complex T) :=
  let Hor := rngl_is_totally_ordered_is_ordered Hto in
  let Hos := rngl_has_opp_has_opp_or_psub Hop in
  let Hsu := rngl_has_opp_has_no_psub Hop in
  let Hio := rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm a b := c_add_comm a b;
     rngl_add_assoc := c_add_assoc;
     rngl_add_0_l := c_add_0_l;
     rngl_mul_assoc := c_mul_assoc Hop;
     rngl_mul_1_l := c_mul_1_l Hos;
     rngl_mul_add_distr_l := c_mul_add_distr_l Hop;
     rngl_opt_mul_comm := c_opt_mul_comm;
     rngl_opt_mul_1_r := c_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := c_opt_mul_add_distr_r Hop;
     rngl_opt_add_opp_diag_l := c_opt_add_opp_diag_l Hop;
     rngl_opt_add_sub := c_opt_add_sub Hsu;
     rngl_opt_sub_add_distr := c_opt_sub_add_distr Hsu;
     rngl_opt_mul_inv_diag_l := c_opt_mul_inv_diag_l Hic Hop Hiv Hto;
     rngl_opt_mul_inv_diag_r := c_opt_mul_inv_diag_r;
     rngl_opt_mul_div := c_opt_mul_div;
     rngl_opt_integral := c_integral'' Hic Hop Hio;
     rngl_opt_alg_closed := NA;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA;
     rngl_characteristic_prop := c_characteristic_prop |}.

End a.

Arguments c_ring_like_prop_not_alg_closed {T ro rp} Hic Hop Hiv Hto.

Require Import RealLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition c_eqb z₁ z₂ := ((Re z₁ =? Re z₂)%L && (Im z₁ =? Im z₂)%L)%bool.

Definition c_opp (z : Complex T) := {| Re := - Re z; Im := - Im z |}.
Definition c_sub (z₁ z₂ : Complex T) :=
  {| Re := Re z₁ - Re z₂; Im := Im z₁ - Im z₂ |}.
Definition c_div (z₁ z₂ : Complex T) := c_mul z₁ (c_inv z₂).
Definition c_squ z := (z * z)%C.
Definition c_pow_nat (z : Complex T) n := rngl_power z n.
Definition c_modulus (z : Complex T) := rl_modl (Re z) (Im z).

(* The square root of a complex number is defined as the complex
   number whose imaginary part is non-negative. If the imaginary part
   is zero, the real part is taken to be non-negative. *)
Definition c_sqrt (z : Complex T) :=
  let x := (rngl_signp (Im z) * √((c_modulus z + Re z)/2))%L in
  let y := √((c_modulus z - Re z)/2) in
  mk_c x y.

End a.

Notation "x =? y" := (c_eqb x y) : c_scope.
Notation "x ≠? y" := (negb (c_eqb x y)) : c_scope.
Notation "- x" := (c_opp x) : c_scope.
Notation "- 1" := (c_opp c_one) : c_scope.
Notation "x - y" := (c_sub x y) : c_scope.
Notation " x / y" := (c_div x y) : c_scope.
Notation "x +ℹ y" := (mk_c x y) (at level 50) : c_scope.
Notation "x ⁻¹" := (c_inv x) : c_scope.
Notation "z ²" := (c_squ z) : c_scope.
Notation "z ^ n" := (c_pow_nat z n) : c_scope.
Notation "√ z" := (c_sqrt z) : c_scope.
Notation "‖ x ‖" := (c_modulus x) (at level 35, x at level 30).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem c_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ z₁ z₂, (z₁ * z₂ = z₂ * z₁)%C.
Proof.
intros Hic.
specialize c_opt_mul_comm as H1.
now rewrite Hic in H1.
Qed.

Theorem c_sub_diag :
  rngl_has_opp_or_psub T = true →
  ∀ z, (z - z = 0)%C.
Proof.
intros Hos *.
progress unfold c_sub.
now do 2 rewrite (rngl_sub_diag Hos).
Qed.

Theorem c_add_opp_r :
  rngl_has_opp T = true →
  ∀ z1 z2, (z1 + - z2 = z1 - z2)%C.
Proof.
intros Hop *.
apply eq_c_eq; cbn.
now do 2 rewrite (rngl_add_opp_r Hop).
Qed.

Theorem c_add_move_0_r :
  rngl_has_opp T = true →
  ∀ z₁ z₂, (z₁ + z₂ = 0)%C ↔ z₁ = (- z₂)%C.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Hab. {
  apply eq_c_eq in Hab; cbn in Hab.
  apply eq_c_eq.
  destruct Hab as (H1, H2).
  apply (rngl_add_move_0_r Hop) in H1, H2.
  now rewrite H1, H2.
}
rewrite c_add_comm; subst.
rewrite (c_add_opp_r Hop).
apply (c_sub_diag Hos).
Qed.

Theorem c_sub_move_0_r :
  rngl_has_opp T = true →
  ∀ z₁ z₂, (z₁ - z₂ = 0)%C ↔ z₁ = z₂.
Proof.
intros Hop.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Hab; [ | subst; apply (c_sub_diag Hos) ].
progress unfold c_sub in Hab.
injection Hab; clear Hab; intros H1 H2.
apply -> (rngl_sub_move_0_r Hop) in H1.
apply -> (rngl_sub_move_0_r Hop) in H2.
now apply eq_c_eq.
Qed.

Theorem c_squ_mul :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  ∀ z₁ z₂, ((z₁ * z₂)² = z₁² * z₂²)%C.
Proof.
intros Hic Hop *.
progress unfold c_squ.
do 2 rewrite (c_mul_assoc Hop).
progress f_equal.
do 2 rewrite <- (c_mul_assoc Hop).
progress f_equal.
apply (c_mul_comm Hic).
Qed.

Theorem c_modulus_0 :
  rngl_has_opp T = true →
  (rngl_is_integral_domain T || rngl_has_inv_or_pdiv T)%bool = true →
  rngl_is_totally_ordered T = true →
  (‖ 0 ‖ = 0)%L.
Proof.
intros Hop Hii Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold c_modulus.
progress unfold rl_modl.
cbn.
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_l.
apply (rl_sqrt_0 Hop Hto Hii).
Qed.

Theorem c_modulus_1 :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ‖ 1 ‖ = 1%L.
Proof.
intros Hop Hiq Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold c_modulus.
progress unfold rl_modl.
cbn.
rewrite rngl_squ_1.
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_r.
apply (rl_sqrt_1 Hop Hiq Hto).
Qed.

Theorem c_modulus_mul :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ z1 z2, ‖ z1 * z2 ‖ = (‖ z1 ‖ * ‖ z2 ‖)%L.
Proof.
intros Hic Hop Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold c_modulus.
progress unfold rl_modl; cbn.
rewrite (rngl_add_comm (Im z1 * Re z2)).
rewrite <- (Brahmagupta_Fibonacci_identity Hic Hop).
apply rl_sqrt_mul. {
  apply (rngl_add_squ_nonneg Hos Hto).
} {
  apply (rngl_add_squ_nonneg Hos Hto).
}
Qed.

Theorem c_abs_re_le_modulus :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (rngl_abs (Re z) ≤ ‖ z ‖)%L.
Proof.
intros Hop Hiq Hto.
intros.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
progress unfold c_modulus.
progress unfold rl_modl.
rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (rngl_squ_le_abs_le Hop Hiq Hto).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (rngl_le_add_r Hos Hor).
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem Re_opp : ∀ z, Re (- z) = (- Re z)%L.
Proof. easy. Qed.

Theorem Im_opp : ∀ z, Im (- z) = (- Im z)%L.
Proof. easy. Qed.

Theorem c_modulus_opp :
  rngl_has_opp T = true →
  ∀ z, (‖ - z ‖ = ‖ z ‖)%C.
Proof.
intros Hop.
intros.
progress unfold c_modulus; cbn.
progress unfold rl_modl; cbn.
now do 2 rewrite (rngl_squ_opp Hop).
Qed.

Theorem c_add_modulus_re :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ ‖ z ‖ + Re z)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
rewrite rngl_add_comm.
apply (rngl_le_opp_l Hop Hor).
apply (rngl_le_trans Hor _ (rngl_abs (Re z))). {
  apply (rngl_le_opp_abs_diag Hop Hto).
}
apply (c_abs_re_le_modulus Hop Hiq Hto).
Qed.

Theorem c_sub_modulus_re :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ ‖ z ‖ - Re z)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
apply (rngl_le_0_sub Hop Hor).
apply (rngl_le_trans Hor _ (rngl_abs (Re z))). {
  apply (rngl_le_abs_diag Hop Hor).
}
apply (c_abs_re_le_modulus Hop Hiq Hto).
Qed.

Theorem c_modulus_add_re_div_2_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ (‖ z ‖ + Re z) / 2)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / 2)%L).
  apply (rngl_le_refl Hor).
}
intros.
apply (rngl_div_nonneg Hop Hiv Hto); [ | apply (rngl_0_lt_2 Hos Hc1 Hto) ].
apply (c_add_modulus_re Hop Hiv Hto).
Qed.

Theorem c_modulus_sub_re_div_2_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ (‖ z ‖ - Re z) / 2)%L.
Proof.
intros Hop Hiv Hto.
intros.
rewrite <- (rngl_add_opp_r Hop).
rewrite <- Re_opp.
rewrite <- (c_modulus_opp Hop).
apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
Qed.

Context {Hic : rngl_mul_is_comm T = true}.
Context {Hop : rngl_has_opp T = true}.
Context {Hiv : rngl_has_inv T = true}.
Context {Hto : rngl_is_totally_ordered T = true}.

Add Ring rngl_ring : (rngl_ring_theory Hic Hop).
Theorem strange_let :
  ∀ x,
    match
      (let (_, _, _, _, rngl_opt_opp_or_psub, _, _, _, _) := ro in
       rngl_opt_opp_or_psub)
    with
    | Some (inl rngl_opp) => rngl_opp x
    | _ => 0%L
    end = rngl_opp x.
Proof. easy. Qed.
Ltac fold_rngl_in H :=
  replace (let (_, _, _, rngl_mul, _, _, _, _, _) := ro in rngl_mul)
    with rngl_mul in H by easy;
  replace (let (_, _, rngl_add, _, _, _, _, _, _) := ro in rngl_add)
    with rngl_add in H by easy;
  replace (let (rngl_zero, _, _, _, _, _, _, _, _) := ro in rngl_zero)
    with rngl_zero in H by easy;
  replace (let (_, rngl_one, _, _, _, _, _, _, _) := ro in rngl_one)
    with rngl_one in H by easy;
  repeat try rewrite strange_let in H.

Theorem c_eqb_eq z₁ z₂ : (z₁ =? z₂)%C = true ↔ z₁ = z₂.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
split; intros H12. {
  apply eq_c_eq.
  apply Bool.andb_true_iff in H12.
  destruct H12 as (H1, H2).
  now apply (rngl_eqb_eq Heo) in H1, H2.
}
subst.
(* lemma to do: c_eqb_refl *)
apply Bool.andb_true_iff.
now do 2 rewrite (rngl_eqb_refl Heo).
Qed.

Theorem c_squ_sub_squ : ∀ z₁ z₂, (z₁² - z₂² = (z₁ + z₂) * (z₁ - z₂))%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
apply eq_c_eq.
split; cbn; ring.
Qed.

Theorem c_inv_rngl_inv : ∀ z, z⁻¹%C = z⁻¹.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold c_inv.
progress unfold rngl_div.
rewrite Hiv.
progress unfold rngl_inv.
cbn.
progress unfold c_opt_inv_or_pdiv.
rewrite Hic.
progress unfold c_inv.
progress unfold rngl_div.
progress unfold rngl_inv.
rewrite Hiv.
remember (rngl_opt_inv_or_pdiv T) as iq' eqn:Hiq'.
symmetry in Hiq'.
destruct iq' as [inv| ]. {
  destruct inv as [inv| ]; [ easy | ].
  now do 2 rewrite (rngl_mul_0_r Hos).
}
now do 2 rewrite (rngl_mul_0_r Hos).
Qed.

Theorem rl_modl_comm a b : rl_modl a b = rl_modl b a.
Proof.
progress unfold rl_modl; f_equal.
apply rngl_add_comm.
Qed.

Theorem rl_modl_opp_l x y : rl_modl (- x) y = rl_modl x y.
Proof.
progress unfold rl_modl.
f_equal; f_equal.
apply (rngl_squ_opp Hop).
Qed.

Theorem rngl_add_modl_nonneg : ∀ a b, (0 ≤ rl_modl a b + a)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rl_modl.
rewrite rngl_add_comm.
apply (rngl_le_opp_l Hop Hor).
apply (rngl_le_trans Hor _ (rngl_abs a)). {
  apply (rngl_le_abs Hop Hto); right.
  apply (rngl_le_refl Hor).
}
rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (rngl_squ_le_abs_le Hop Hiq Hto).
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (rngl_le_add_r Hos Hor).
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem c_squ_sqrt z : c_squ (c_sqrt z) = z.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  apply eq_c_eq.
  rewrite (H1 (Re _)), (H1 (Re z)).
  rewrite (H1 (Im _)), (H1 (Im z)).
  easy.
}
destruct z as (x, y).
progress unfold c_sqrt.
progress unfold c_squ.
progress unfold c_modulus.
progress unfold c_mul.
cbn.
f_equal. {
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic (rngl_signp y)).
  rewrite fold_rngl_squ.
  rewrite (rngl_squ_signp Hop), rngl_mul_1_l.
  do 2 rewrite fold_rngl_squ.
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_div_nonneg Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    apply rngl_add_modl_nonneg.
  }
  rewrite rngl_squ_sqrt. 2: {
    apply (rngl_div_nonneg Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite <- (rngl_add_opp_r Hop).
    rewrite <- rl_modl_opp_l.
    apply rngl_add_modl_nonneg.
  }
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  rewrite (rngl_sub_sub_distr Hop).
  rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  rewrite rngl_add_0_l.
  rewrite <- rngl_mul_2_r.
  apply (rngl_mul_div Hiq).
  apply (rngl_2_neq_0 Hos Hc1 Hto).
} {
  rewrite (rngl_mul_comm Hic).
  rewrite <- rngl_mul_assoc.
  rewrite <- rngl_mul_add_distr_l.
  rewrite <- rngl_mul_2_l.
  rewrite <- rl_sqrt_mul; cycle 1. {
    apply (rngl_div_nonneg Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    apply rngl_add_modl_nonneg.
  } {
    apply (rngl_div_nonneg Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite <- (rngl_add_opp_r Hop).
    rewrite <- rl_modl_opp_l.
    apply rngl_add_modl_nonneg.
  }
  rewrite (rngl_div_mul_mul_div Hic Hiv).
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite (rngl_div_div Hos Hiv).
  2, 3 : apply (rngl_2_neq_0 Hos Hc1 Hto).
  rewrite (rngl_squ_sub_squ' Hop).
  rewrite (rngl_mul_comm Hic x).
  rewrite (rngl_add_sub Hos).
  progress unfold rl_modl.
  rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
  rewrite (rngl_add_comm x²), (rngl_add_sub Hos).
  rewrite fold_rngl_squ.
  rewrite <- (rngl_squ_div Hic Hos Hiv). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  rewrite (rl_sqrt_squ Hop Hto).
  rewrite (rngl_abs_div Hop Hiv Hto). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  rewrite (rngl_abs_nonneg_eq Hop Hor 2). 2: {
    apply (rngl_0_le_2 Hos Hto).
  }
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite (rngl_mul_comm Hic 2).
  rewrite (rngl_mul_div Hiq). 2: {
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  apply (rngl_mul_signp_abs Hop Hto).
}
Qed.

Fixpoint c_nth_2_pow_root n z :=
  match n with
  | 0 => z
  | S n' => c_sqrt (c_nth_2_pow_root n' z)
  end.

Definition c_seq_to_div_nat (z : Complex T) (n k : nat) :=
  (c_nth_2_pow_root k z ^ (2 ^ k / n))%L.

Definition c_eucl_dist z1 z2 := c_modulus (z1 - z2).

(* trigonometry equivalent to cos (θ₁ - θ₂) formula *)
Theorem c_div_re :
  ∀ z1 z2,
  Re (z1 / z2) = ((Re z1 * Re z2 + Im z1 * Im z2) / (‖ z2 ‖)²)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold c_div; cbn.
do 2 rewrite fold_rngl_squ.
progress unfold c_modulus.
progress unfold rl_modl.
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
remember ((Re z2)² + (Im z2)²)%L as m eqn:Hm.
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- (rngl_div_add_distr_r Hiv).
easy.
Qed.

Theorem rl_modl_squ : ∀ z₁ z₂, (z₁² + z₂²)%L = (rl_modl z₁ z₂)².
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold rl_modl.
symmetry.
apply rngl_squ_sqrt.
apply (rngl_add_squ_nonneg Hos Hto).
Qed.

Theorem fold_c_modulus : ∀ z, rl_modl (Re z) (Im z) = ‖ z ‖.
Proof. easy. Qed.

Theorem gre_lt_c_eucl_dist_lt :
  ∀ a z₁ z₂,
  (0 ≤ a)%L
  → z₁ ≠ 0%C
  → (((‖ z₁ ‖)² + (‖ z₂ ‖)²) / 2 - a² / 2 < Re (z₂ / z₁) * (‖ z₁ ‖)²)%L
  ↔ (c_eucl_dist z₁ z₂ < a)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hza H1z.
  rewrite (H1 (_ - _)%L), (H1 (Re _ * _)%L).
  rewrite (H1 (c_eucl_dist _ _)), (H1 a).
  easy.
}
intros * Hza H1z.
progress unfold c_eucl_dist.
progress unfold c_modulus.
progress unfold rl_modl.
symmetry.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_). 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hos Hto).
}
symmetry.
rewrite <- (rngl_abs_nonneg_eq Hop Hor a) at 2; [ | easy ].
rewrite fold_rl_modl.
rewrite fold_c_modulus.
rewrite c_div_re.
rewrite (rngl_div_mul Hiv). 2: {
  intros H.
  apply (eq_rngl_squ_0 Hos Hio) in H.
  (* lemma *)
  progress unfold c_modulus in H.
  progress unfold rl_modl in H.
  apply (eq_rl_sqrt_0 Hos) in H. 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (eq_rngl_add_square_0 Hop Hiq Hto) in H.
  destruct z₁ as (x, y).
  cbn in H.
  now destruct H; subst x y.
}
split. {
  intros Hc.
  apply (rngl_squ_lt_abs_lt Hop Hiq Hto).
  rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
  cbn.
  do 2 rewrite (rngl_squ_sub Hop Hic).
  rewrite rngl_add_assoc.
  rewrite (rngl_add_sub_assoc Hop).
  do 4 rewrite <- (rngl_add_sub_swap Hop).
  rewrite (rngl_add_add_swap (Re z₁)²).
  rewrite <- rngl_add_assoc.
  rewrite <- (rngl_sub_add_distr Hos).
  do 2 rewrite <- rngl_mul_assoc.
  rewrite <- rngl_mul_add_distr_l.
  do 2 rewrite rl_modl_squ.
  do 2 rewrite fold_c_modulus.
  apply (rngl_div_lt_mono_pos_r Hop Hiv Hto 2). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_div_sub_distr_r Hop Hiv).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  rewrite (rngl_add_comm (_ / _)).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  rewrite (rngl_mul_comm Hic (Re z₁)).
  rewrite (rngl_mul_comm Hic (Im z₁)).
  easy.
} {
  intros Ha.
  apply (rngl_abs_lt_squ_lt Hop Hiq Hto) in Ha. 2: {
    apply (rngl_mul_comm Hic).
  }
  rewrite rngl_squ_sqrt in Ha; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
  cbn in Ha.
  do 2 rewrite (rngl_squ_sub Hop Hic) in Ha.
  rewrite rngl_add_assoc in Ha.
  rewrite (rngl_add_sub_assoc Hop) in Ha.
  do 4 rewrite <- (rngl_add_sub_swap Hop) in Ha.
  rewrite (rngl_add_add_swap (Re z₁)²) in Ha.
  rewrite <- rngl_add_assoc in Ha.
  rewrite <- (rngl_sub_add_distr Hos) in Ha.
  do 2 rewrite <- rngl_mul_assoc in Ha.
  rewrite <- rngl_mul_add_distr_l in Ha.
  do 2 rewrite rl_modl_squ in Ha.
  do 2 rewrite fold_c_modulus in Ha.
  apply (rngl_div_lt_mono_pos_r Hop Hiv Hto 2) in Ha. 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_div_sub_distr_r Hop Hiv) in Ha.
  rewrite (rngl_mul_comm Hic) in Ha.
  rewrite (rngl_mul_div Hiq) in Ha; [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Ha.
  rewrite (rngl_add_comm (_ / _)) in Ha.
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Ha.
  rewrite (rngl_mul_comm Hic (Re z₁)) in Ha.
  rewrite (rngl_mul_comm Hic (Im z₁)) in Ha.
  easy.
}
Qed.

Theorem c_sqrt_modulus : ∀ z, ‖ √z ‖ = √ ‖ z ‖.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite H1; apply H1.
}
intros.
progress unfold c_sqrt.
progress unfold c_modulus.
progress unfold rl_modl; cbn.
progress f_equal.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_trans Hor _ (rngl_abs (Re z))). {
    apply (rngl_le_abs_diag Hop Hor).
  }
  rewrite fold_rl_modl.
  rewrite fold_c_modulus.
  apply (c_abs_re_le_modulus Hop Hiq Hto).
}
rewrite fold_rl_modl.
rewrite fold_c_modulus.
rewrite (rngl_squ_mul Hic).
rewrite (rngl_squ_signp Hop).
rewrite rngl_mul_1_l.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_trans Hor _ (rngl_abs (Re z))). {
    rewrite <- (rngl_abs_opp Hop Hto).
    apply (rngl_le_abs_diag Hop Hor).
  }
  apply (c_abs_re_le_modulus Hop Hiq Hto).
}
rewrite (rngl_div_add_distr_r Hiv).
rewrite (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_add_sub Hos).
rewrite <- rngl_mul_2_l.
rewrite (rngl_mul_comm Hic).
apply (rngl_div_mul Hiv).
apply (rngl_2_neq_0 Hos Hc1 Hto).
Qed.

Theorem c_modulus_nonneg : ∀ z, (0 ≤ ‖ z ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold c_modulus.
progress unfold rl_modl.
apply rl_sqrt_nonneg.
apply (rngl_add_squ_nonneg Hos Hto).
Qed.

Theorem eq_rngl_add_squ_0 : ∀ z₁ z₂, (z₁² + z₂² = 0 → z₁ = 0 ∧ z₂ = 0)%L.
Proof.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
apply (eq_rngl_add_square_0 Hop Hiq Hto).
Qed.

Theorem c_pow_neq_0 :
  rngl_characteristic T ≠ 1 →
  ∀ z n, z ≠ 0%C → (z ^ n)%C ≠ 0%C.
Proof.
intros Hc1.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz.
specialize (@rngl_pow_neq_0 (Complex T)) as H1.
specialize (H1 (c_ring_like_op T)).
specialize (H1 (c_ring_like_prop_not_alg_closed Hic Hop Hiv Hto)).
apply H1; [ | | easy ]. {
  progress unfold rngl_has_opp_or_psub; cbn.
  progress unfold rngl_has_opp_or_psub in Hos.
  progress unfold c_opt_opp_or_psub.
  destruct (rngl_opt_opp_or_psub T); [ | easy ].
  now destruct s.
} {
  progress unfold rngl_has_inv in Hiv.
  progress unfold rngl_has_inv_or_pdiv; cbn.
  progress unfold c_opt_inv_or_pdiv.
  rewrite Hic.
  destruct (rngl_opt_inv_or_pdiv T); [ | easy ].
  now destruct s.
}
Qed.

Theorem c_mul_0_l :
  rngl_has_opp_or_psub T = true →
  ∀ z : Complex T, (0 * z = 0)%C.
Proof.
intros Hos *.
apply eq_c_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem c_mul_0_r :
  rngl_has_opp_or_psub T = true →
  ∀ z : Complex T, (z * 0 = 0)%C.
Proof.
intros Hos *.
apply eq_c_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem c_sqrt_1 : (√1 = 1)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  apply eq_c_eq.
  do 2 rewrite (H1 (Re _)) ,(H1 (Im _)).
  easy.
}
progress unfold c_sqrt; cbn.
rewrite (c_modulus_1 Hop Hiq Hto).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_diag Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
rewrite (rngl_div_0_l Hos Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
rewrite (rl_sqrt_1 Hop Hiq Hto).
rewrite (rl_sqrt_0 Hop Hto Hii).
(* lemma *)
progress unfold rngl_signp.
rewrite (rngl_leb_refl Hor).
rewrite rngl_mul_1_l.
easy.
Qed.

Theorem rngl_signp_mul :
  ∀ z₁ z₂,
  (z₁ * z₂ ≠ 0)%L
  → rngl_signp (z₁ * z₂) = (rngl_signp z₁ * rngl_signp z₂)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Habz.
progress unfold rngl_signp.
remember (0 ≤? z₁)%L as za eqn:Hza.
remember (0 ≤? z₂)%L as zb eqn:Hzb.
remember (0 ≤? z₁ * z₂)%L as zab eqn:Hzab.
symmetry in Hza, Hzb, Hzab.
destruct za, zb, zab. {
  symmetry; apply rngl_mul_1_l.
} {
  exfalso.
  apply rngl_leb_le in Hza, Hzb.
  apply Bool.not_true_iff_false in Hzab.
  apply Hzab; clear Hzab.
  apply rngl_leb_le.
  now apply (rngl_mul_nonneg_nonneg Hos Hor).
} {
  exfalso.
  apply rngl_leb_le in Hza, Hzab.
  apply Bool.not_true_iff_false in Hzb.
  apply Hzb; clear Hzb.
  apply rngl_leb_le.
  apply (rngl_le_0_mul Hop Hiq Hto) in Hzab.
  destruct Hzab as [| Hzab]; [ easy | ].
  destruct Hzab as (Haz, _).
  apply (rngl_le_antisymm Hor) in Haz; [ | easy ].
  now subst; rewrite (rngl_mul_0_l Hos) in Habz.
} {
  symmetry; apply rngl_mul_1_l.
} {
  exfalso.
  apply rngl_leb_le in Hzb, Hzab.
  apply Bool.not_true_iff_false in Hza.
  apply Hza; clear Hza.
  apply rngl_leb_le.
  apply (rngl_le_0_mul Hop Hiq Hto) in Hzab.
  destruct Hzab as [| Hzab]; [ easy | ].
  destruct Hzab as (_, Hbz).
  apply (rngl_le_antisymm Hor) in Hbz; [ | easy ].
  now subst; rewrite (rngl_mul_0_r Hos) in Habz.
} {
  symmetry; apply rngl_mul_1_r.
} {
  symmetry; apply (rngl_squ_opp_1 Hop).
} {
  exfalso.
  apply (rngl_leb_gt_iff Hto) in Hza, Hzb, Hzab.
  apply (rngl_lt_mul_0_if Hos Hto) in Hzab.
  destruct Hzab as [(_, Hbz)| (Haz, _)]. {
    now apply (rngl_lt_asymm Hor) in Hbz.
  } {
    now apply (rngl_lt_asymm Hor) in Haz.
  }
}
Qed.

(* trigonometry equivalent to cos bound *)
Theorem Re_bound : ∀ z, (- ‖ z ‖ ≤ Re z ≤ ‖ z ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold c_modulus.
progress unfold rl_modl.
split. {
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (rngl_le_trans Hor _ (rngl_abs (Re z))). {
    apply (rngl_le_opp_abs_diag Hop Hto).
  }
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_squ_nonneg Hos Hto).
} {
  rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (rngl_le_trans Hor _ (rngl_abs (Re z))). {
    apply (rngl_le_abs_diag Hop Hor).
  }
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_squ_nonneg Hos Hto).
}
Qed.

Theorem c_integral :
  ∀ z₁ z₂ : Complex T, (z₁ * z₂)%C = 0%C → z₁ = 0%C ∨ z₂ = 0%C.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hab.
specialize (c_integral'' Hic Hop Hio z₁ z₂ Hab) as H.
destruct H as [H| H]; [ now left | ].
destruct H as [H| H]; [ now right | ].
destruct H as [H| H]; cbn in H. {
  apply eq_rngl_add_squ_0 in H.
  now left; apply eq_c_eq.
} {
  apply eq_rngl_add_squ_0 in H.
  now right; apply eq_c_eq.
}
Qed.

Theorem c_eq_cases : ∀ z₁ z₂, (z₁² = z₂² → z₁ = z₂ ∨ z₁ = - z₂)%C.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hab.
apply (c_sub_move_0_r Hop) in Hab.
rewrite c_squ_sub_squ in Hab.
apply c_integral in Hab.
destruct Hab as [H| H]. {
  now apply (c_add_move_0_r Hop) in H; right.
} {
  now apply -> (c_sub_move_0_r Hop z₁) in H; left.
}
Qed.

Theorem c_squ_sqrt_mul : ∀ z₁ z₂, (√(z₁ * z₂))²%C = (√z₁ * √z₂)²%C.
Proof.
intros.
rewrite c_squ_sqrt.
rewrite (c_squ_mul Hic Hop).
now do 2 rewrite c_squ_sqrt.
Qed.

Theorem rngl_signp_0 : rngl_signp 0 = 1%L.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
progress unfold rngl_signp.
now rewrite (rngl_leb_refl Hor).
Qed.

Theorem c_sqrt_0 : (√0 = 0)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  apply eq_c_eq.
  now do 2 rewrite (H1 (Re _)), (H1 (Im _)).
}
apply eq_c_eq; cbn.
rewrite rngl_signp_0, rngl_mul_1_l.
rewrite (c_modulus_0 Hop Hii Hto).
rewrite rngl_add_0_l.
rewrite (rngl_sub_diag Hos).
rewrite (rngl_div_0_l Hos Hiq). 2: {
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
split; apply (rl_sqrt_0 Hop Hto Hii).
Qed.

Theorem c_opp_0 : (- 0)%C = 0%C.
Proof.
apply eq_c_eq; cbn.
split; apply (rngl_opp_0 Hop).
Qed.

Theorem rl_sqrt_add_mod_re_div_2_nonneg : ∀ z, (0 ≤ √((‖ z ‖ + Re z) / 2))%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (√_)).
  apply (rngl_le_refl Hor).
}
intros.
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hop Hiv Hto). 2: {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (c_add_modulus_re Hop Hiv Hto).
Qed.

Theorem rl_sqrt_sub_mod_re_div_2_nonneg : ∀ z, (0 ≤ √((‖ z ‖ - Re z) / 2))%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (√_)).
  apply (rngl_le_refl Hor).
}
intros.
apply rl_sqrt_nonneg.
apply (rngl_div_nonneg Hop Hiv Hto). 2: {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (c_sub_modulus_re Hop Hiv Hto).
Qed.

Theorem eq_rngl_add_modulus_re_0 :
  ∀ z, (‖ z ‖ + Re z = 0)%L → (Re z ≤ 0 ∧ Im z = 0)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz.
generalize Hzz; intros H1.
apply (rngl_add_move_0_r Hop) in H1.
apply (f_equal rngl_squ) in H1.
progress unfold c_modulus in H1.
progress unfold rl_modl in H1.
rewrite (rngl_squ_sqrt) in H1; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
rewrite (rngl_squ_opp Hop) in H1.
rewrite rngl_add_comm in H1.
apply (rngl_add_move_r Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
progress unfold c_modulus in Hzz.
progress unfold rl_modl in Hzz.
rewrite H1, rngl_add_0_r in Hzz.
rewrite (rl_sqrt_squ Hop Hto) in Hzz.
apply (rngl_add_move_0_r Hop) in Hzz.
apply (rngl_abs_nonpos_eq_iff Hop Hto) in Hzz.
now apply (eq_rngl_squ_0 Hos Hio) in H1.
Qed.

Theorem eq_rngl_sub_modulus_re_0 :
  ∀ z, (‖ z ‖ - Re z = 0)%L → (0 ≤ Re z ∧ Im z = 0)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz.
generalize Hzz; intros H1.
apply -> (rngl_sub_move_0_r Hop) in H1.
apply (f_equal rngl_squ) in H1.
progress unfold c_modulus in H1.
progress unfold rl_modl in H1.
rewrite (rngl_squ_sqrt) in H1; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
rewrite rngl_add_comm in H1.
apply (rngl_add_move_r Hop) in H1.
rewrite (rngl_sub_diag Hos) in H1.
progress unfold c_modulus in Hzz.
progress unfold rl_modl in Hzz.
rewrite H1, rngl_add_0_r in Hzz.
rewrite (rl_sqrt_squ Hop Hto) in Hzz.
apply -> (rngl_sub_move_0_r Hop) in Hzz.
apply (rngl_abs_nonneg_eq_iff Hop Hto) in Hzz.
now apply (eq_rngl_squ_0 Hos Hio) in H1.
Qed.

Theorem c_opp_involutive : ∀ z, (- - z)%C = z.
Proof.
intros.
apply eq_c_eq; cbn.
now do 2 rewrite (rngl_opp_involutive Hop).
Qed.

Theorem c_mul_opp_r : ∀ z₁ z2, (z₁ * - z2 = - (z₁ * z2))%C.
Proof.
intros.
apply eq_c_eq; cbn.
do 4 rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop), (rngl_add_opp_r Hop).
rewrite (rngl_add_opp_l Hop), (rngl_opp_sub_distr Hop).
rewrite (rngl_opp_add_distr Hop).
easy.
Qed.

Theorem c_sqrt_neg :
  ∀ z, (√(- z))%C = (rngl_signp (- Im z) * Im √z +ℹ ∣ Re √z ∣)%C.
Proof.
intros.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold c_sqrt; cbn.
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
rewrite (c_modulus_opp Hop).
progress f_equal.
rewrite (rngl_abs_mul Hop Hiq Hto).
rewrite (rngl_abs_signp Hop Hto), rngl_mul_1_l.
symmetry.
apply (rngl_abs_sqrt Hop Hor).
apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
Qed.

Theorem Re_sqrt_nonneg : ∀ z, (0 ≤ Im z)%L → (0 ≤ Re √z)%L.
Proof.
intros * Hiz; cbn.
rewrite rngl_signp_of_nonneg; [ | easy ].
rewrite rngl_mul_1_l.
apply rl_sqrt_add_mod_re_div_2_nonneg.
Qed.

Theorem Im_sqrt_nonneg : ∀ z, (0 ≤ Im √z)%L.
Proof.
intros; cbn.
apply rl_sqrt_sub_mod_re_div_2_nonneg.
Qed.

Theorem eq_c_sqrt_add_modulus_Re_div_2_0 :
  ∀ z, √((‖ z ‖ + Re z) / 2) = 0%L ↔ (Re z ≤ 0)%L ∧ Im z = 0%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros (x, y).
  rewrite (H1 (√_)%L), (H1 x), (H1 y); cbn.
  split; [ intros | easy ].
  split; [ | easy ].
  apply (rngl_le_refl Hor).
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
intros.
split; intros H. {
  apply eq_rngl_add_modulus_re_0.
  apply (eq_rl_sqrt_0 Hos) in H. {
    apply (f_equal (λ a, (a * 2)%L)) in H.
    rewrite (rngl_div_mul Hiv) in H; [ | easy ].
    now rewrite (rngl_mul_0_l Hos) in H.
  }
  apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
} {
  destruct H as (H1, H2); cbn.
  progress unfold c_modulus.
  progress unfold rl_modl.
  rewrite H2, (rngl_squ_0 Hos), rngl_add_0_r.
  rewrite (rl_sqrt_squ Hop Hto).
  rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
  rewrite (rngl_add_opp_l Hop), (rngl_sub_diag Hos).
  rewrite (rngl_div_0_l Hos Hiq); [ | easy ].
  apply (rl_sqrt_0 Hop Hto Hii).
}
Qed.

Theorem eq_c_sqrt_sub_modulus_Re_div_2_0 :
  ∀ z, √((‖ z ‖ - Re z) / 2) = 0%L ↔ (0 ≤ Re z)%L ∧ Im z = 0%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros (x, y).
  rewrite (H1 (√_)%L), (H1 x), (H1 y); cbn.
  split; [ intros | easy ].
  split; [ | easy ].
  apply (rngl_le_refl Hor).
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
intros.
split; intros H. {
  remember (-z)%C as z' eqn:Hz'.
  apply (f_equal c_opp) in Hz'.
  rewrite c_opp_involutive in Hz'.
  subst z; rename z' into z.
  cbn in H.
  rewrite (c_modulus_opp Hop) in H.
  rewrite (rngl_sub_opp_r Hop) in H.
  apply eq_c_sqrt_add_modulus_Re_div_2_0 in H.
  cbn.
  split.
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
  rewrite (proj2 H).
  apply (rngl_opp_0 Hop).
} {
  destruct H as (H1, H2); cbn.
  progress unfold c_modulus.
  progress unfold rl_modl.
  rewrite H2, (rngl_squ_0 Hos), rngl_add_0_r.
  rewrite (rl_sqrt_squ Hop Hto).
  rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_div_0_l Hos Hiq); [ | easy ].
  apply (rl_sqrt_0 Hop Hto Hii).
}
Qed.

Theorem eq_c_modulus_add_re_div_2_opp_re :
  ∀ z, ((‖ z ‖ + Re z) / 2 = Re z)%L ↔ (0 ≤ Re z)%L ∧ Im z = 0%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (Re z)), (H1 (Im z)).
  rewrite (H1 (_ / _)%L).
  split; [ intros _ | easy ].
  split; [ | easy ].
  apply (rngl_le_refl Hor).
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
intros.
split. {
  intros Hz.
  split. {
    rewrite <- Hz.
    apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
  }
  apply (f_equal (rngl_mul 2)) in Hz.
  rewrite (rngl_mul_comm Hic) in Hz.
  rewrite (rngl_div_mul Hiv _ _ H2z) in Hz.
  apply (rngl_add_move_r Hop) in Hz.
  rewrite rngl_mul_2_l in Hz.
  rewrite (rngl_add_sub Hos) in Hz.
  progress unfold c_modulus in Hz.
  progress unfold rl_modl in Hz.
  apply (f_equal rngl_squ) in Hz.
  rewrite rngl_squ_sqrt in Hz.
  2: apply (rngl_add_squ_nonneg Hos Hto).
  apply (rngl_add_move_l Hop) in Hz.
  rewrite (rngl_sub_diag Hos) in Hz.
  now apply (eq_rngl_squ_0 Hos Hio) in Hz.
}
intros (Hrz, Hiz).
apply (rngl_mul_cancel_r Hiq _ _ 2 H2z).
rewrite (rngl_div_mul Hiv _ _ H2z).
apply (rngl_add_move_r Hop).
rewrite rngl_mul_2_r.
rewrite (rngl_add_sub Hos).
progress unfold c_modulus.
progress unfold rl_modl.
rewrite Hiz, (rngl_squ_0 Hos), rngl_add_0_r.
rewrite (rl_sqrt_squ Hop Hto).
now apply (rngl_abs_nonneg_eq Hop Hor).
Qed.

Theorem eq_c_modulus_sub_re_div_2_opp_re :
  ∀ z, ((‖ z ‖ - Re z) / 2 = - Re z)%L ↔ (Re z ≤ 0)%L ∧ Im z = 0%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (Re z)), (H1 (Im z)).
  rewrite (H1 (_ / _)%L), (H1 (- _)%L).
  split; [ intros _ | easy ].
  split; [ | easy ].
  apply (rngl_le_refl Hor).
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
intros.
split. {
  intros Hz.
  split. {
    apply (f_equal rngl_opp) in Hz.
    rewrite (rngl_opp_involutive Hop) in Hz.
    rewrite <- Hz.
    apply (rngl_le_opp_0 Hop Hor).
    apply (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto).
  }
  apply (f_equal (rngl_mul 2)) in Hz.
  rewrite (rngl_mul_comm Hic) in Hz.
  rewrite (rngl_div_mul Hiv _ _ H2z) in Hz.
  apply (rngl_sub_move_r Hop) in Hz.
  rewrite rngl_mul_2_l in Hz.
  rewrite (rngl_add_opp_r Hop) in Hz.
  rewrite (rngl_sub_add Hop) in Hz.
  progress unfold c_modulus in Hz.
  progress unfold rl_modl in Hz.
  apply (f_equal rngl_squ) in Hz.
  rewrite rngl_squ_sqrt in Hz; cycle 1. {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  rewrite (rngl_squ_opp Hop) in Hz.
  apply (rngl_add_move_l Hop) in Hz.
  rewrite (rngl_sub_diag Hos) in Hz.
  now apply (eq_rngl_squ_0 Hos Hio) in Hz.
}
intros (Hrz, Hiz).
apply (rngl_mul_cancel_r Hiq _ _ 2 H2z).
rewrite (rngl_div_mul Hiv _ _ H2z).
apply (rngl_sub_move_r Hop).
rewrite rngl_mul_2_r.
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_sub_add Hop).
progress unfold c_modulus.
progress unfold rl_modl.
rewrite Hiz, (rngl_squ_0 Hos), rngl_add_0_r.
rewrite (rl_sqrt_squ Hop Hto).
now apply (rngl_abs_nonpos_eq Hop Hto).
Qed.

Theorem eq_c_sqrt_0: ∀ z, (√z = 0 → z = 0)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros (x, y) _.
  now rewrite (H1 x), (H1 y).
}
intros * Hzz.
progress unfold c_sqrt in Hzz.
injection Hzz; clear Hzz; intros H2 H1.
move H1 after H2.
apply (rngl_integral Hos Hio) in H1.
destruct H1 as [H1| H1]. {
  progress unfold rngl_signp in H1.
  destruct (0 ≤? Im z)%L.
  now apply (rngl_1_neq_0 Hc1) in H1.
  now apply (rngl_opp_1_neq_0 Hop Hc1) in H1.
}
apply eq_c_sqrt_add_modulus_Re_div_2_0 in H1.
apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H2.
destruct H1 as (H1, _).
destruct H2 as (H2, H3).
apply (rngl_le_antisymm Hor) in H2; [ | easy ].
now apply eq_c_eq.
Qed.

Theorem eq_Im_sqrt_0 : ∀ z, Im √z = 0%L → (0 ≤ Re z)%L ∧ Im z = 0%L.
Proof.
intros * Hiz.
cbn in Hiz.
now apply eq_c_sqrt_sub_modulus_Re_div_2_0 in Hiz.
Qed.

Theorem Re_neg_signp_Im_opp_1 :
  ∀ z, (Re √z < 0)%L → rngl_signp (Im z) = (-1)%L.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hzz.
cbn in Hzz.
progress unfold rngl_signp in Hzz.
progress unfold rngl_signp.
remember (0 ≤? Im z)%L as zi eqn:Hzi.
symmetry in Hzi.
destruct zi; [ exfalso | easy ].
rewrite rngl_mul_1_l in Hzz.
apply (rngl_nle_gt Hor) in Hzz.
apply Hzz; clear Hzz.
apply rl_sqrt_add_mod_re_div_2_nonneg.
Qed.

Theorem eq_Re_sqrt_0 : ∀ z, Re √z = 0%L ↔ (Re z ≤ 0)%L ∧ Im z = 0%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (Re z)), (H1 (Im z)), (H1 (Re √z)).
  split; [ intros | easy ].
  split; [ | easy ].
  apply (rngl_le_refl Hor).
}
intros.
split; intros Hrz. {
  cbn in Hrz.
  apply (rngl_integral Hos Hio) in Hrz.
  destruct Hrz as [Hrz| Hrz].
  now apply (rngl_signp_neq_0 Hop Hc1) in Hrz.
  now apply eq_c_sqrt_add_modulus_Re_div_2_0 in Hrz.
} {
  destruct Hrz as (H1, H2).
  cbn; rewrite H2.
  rewrite rngl_signp_0, rngl_mul_1_l.
  now apply eq_c_sqrt_add_modulus_Re_div_2_0.
}
Qed.

Theorem eq_c_modulus_0 : ∀ z, (‖ z ‖ = 0)%L ↔ z = 0%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros.
split; intros Hz; [ | subst; apply (c_modulus_0 Hop Hii Hto) ].
progress unfold c_modulus in Hz.
progress unfold rl_modl in Hz.
apply (eq_rl_sqrt_0 Hos) in Hz. 2: {
  apply (rngl_add_squ_nonneg Hos Hto).
}
apply (eq_rngl_add_square_0 Hop Hiq Hto) in Hz.
now apply eq_c_eq.
Qed.

Theorem Re_mul : ∀ z₁ z2, Re (z₁ * z2) = (Re z₁ * Re z2 - Im z₁ * Im z2)%L.
Proof. easy. Qed.

Theorem Im_mul : ∀ z₁ z2, Im (z₁ * z2) = (Im z₁ * Re z2 + Re z₁ * Im z2)%L.
Proof. easy. Qed.

Definition is_negative_real z := ((Re z <? 0)%L && (Im z =? 0)%L)%bool.
Definition is_negative_real_prop z := (Re z < 0 ∧ Im z = 0)%L.

Theorem is_negative_real_bool_prop z :
  is_negative_real z = true ↔ is_negative_real_prop z.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
split; intros Hz. {
  apply Bool.andb_true_iff in Hz.
  split.
  now apply (rngl_ltb_lt Heo).
  now apply (rngl_eqb_eq Heo).
} {
  destruct Hz as (H1, H2).
  apply Bool.andb_true_iff.
  split.
  now apply (rngl_ltb_lt Heo).
  now apply (rngl_eqb_eq Heo).
}
Qed.

Theorem is_not_negative_real_bool_prop z :
  is_negative_real z = false ↔ ¬ is_negative_real_prop z.
Proof.
split; intros Hz. {
  apply Bool.not_true_iff_false in Hz.
  intros H; apply Hz; clear Hz.
  now apply is_negative_real_bool_prop.
} {
  apply Bool.not_true_iff_false.
  intros H; apply Hz; clear Hz.
  now apply is_negative_real_bool_prop.
}
Qed.

Theorem c_sqrt_mul_when_Im_nonneg_nonneg :
  ∀ z₁ z₂,
  (0 ≤ Im z₁)%L
  → (0 ≤ Im z₂)%L
  → ¬ (is_negative_real_prop z₁ ∧ is_negative_real_prop z₂)
  → (√(z₁ * z₂) = √z₁ * √z₂)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  apply eq_c_eq.
  now do 2 rewrite (H1 (Re _)), (H1 (Im _)).
}
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hi1 Hi2 Hrab.
destruct (c_eq_dec Heo z₁ 0) as [H1z| H1z]. {
  subst z₁.
  rewrite (c_mul_0_l Hos).
  rewrite c_sqrt_0.
  symmetry; apply (c_mul_0_l Hos).
}
destruct (c_eq_dec Heo z₂ 0) as [H2z| H2z]. {
  subst z₂.
  rewrite (c_mul_0_r Hos).
  rewrite c_sqrt_0.
  symmetry; apply (c_mul_0_r Hos).
}
specialize (c_squ_sqrt_mul z₁ z₂) as H12.
apply c_eq_cases in H12.
destruct H12 as [| H12]; [ easy | exfalso ].
progress unfold c_sqrt in H12.
rewrite (rngl_signp_of_nonneg (Im z₁)) in H12; [ | easy ].
rewrite (rngl_signp_of_nonneg (Im z₂)) in H12; [ | easy ].
do 2 rewrite rngl_mul_1_l in H12.
remember (z₁ * z₂)%C as z.
move z before z₂.
progress unfold c_mul in H12; cbn in H12.
injection H12; clear H12; intros H2 H1.
move H1 after H2.
specialize (rl_sqrt_nonneg ((‖ z ‖ + Re z) / 2)%L) as H3.
specialize (H3 (c_modulus_add_re_div_2_nonneg Hop Hiv Hto _)).
specialize (rl_sqrt_nonneg ((‖ z ‖ - Re z) / 2)%L) as H4.
specialize (H4 (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto _)).
apply (rngl_nlt_ge Hor) in H4.
apply H4; clear H4.
rewrite H2.
apply (rngl_opp_neg_pos Hop Hor).
apply rngl_le_neq.
split. {
  apply (rngl_add_nonneg_nonneg Hos Hor). {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
    apply rl_sqrt_add_mod_re_div_2_nonneg.
  } {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply rl_sqrt_add_mod_re_div_2_nonneg.
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
  }
}
intros H4; symmetry in H4.
apply (rngl_eq_add_0 Hos Hor) in H4; cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply rl_sqrt_sub_mod_re_div_2_nonneg.
  apply rl_sqrt_add_mod_re_div_2_nonneg.
} {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply rl_sqrt_add_mod_re_div_2_nonneg.
  apply rl_sqrt_sub_mod_re_div_2_nonneg.
}
clear Hi1.
destruct H4 as (H4, H5).
rewrite H4, rngl_add_0_l in H2.
rewrite H5, (rngl_opp_0 Hop) in H2.
apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H2.
clear H3.
destruct H2 as (H2, H3).
rewrite H3, rngl_signp_0, rngl_mul_1_l in H1.
apply (rngl_integral Hos Hio) in H4.
destruct H4 as [H4| H4]. {
  rewrite H4, (rngl_mul_0_l Hos), (rngl_sub_0_r Hos) in H1.
  apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H4.
  destruct H4 as (H4, H6).
  move H6 after Hi2; rename H6 into Hi1.
  apply (rngl_integral Hos Hio) in H5.
  destruct H5 as [H5| H5]. {
    rewrite H5, (rngl_mul_0_l Hos), (rngl_opp_0 Hop) in H1.
    apply eq_c_sqrt_add_modulus_Re_div_2_0 in H1.
    destruct H1 as (H1, _).
    apply (rngl_le_antisymm Hor) in H2; [ clear H1 | easy ].
    assert (H : z = 0%C) by now apply eq_c_eq.
    rewrite Heqz in H.
    now apply c_integral in H; destruct H.
  } {
    apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H5.
    destruct H5 as (H5, H6).
    move H6 before Hi2; clear Hi2; rename H6 into Hi2.
    apply (rngl_add_move_0_r Hop) in H1.
    apply (rngl_eq_add_0 Hos Hor) in H1; cycle 1.
    apply rl_sqrt_add_mod_re_div_2_nonneg.
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    1, 2: apply rl_sqrt_add_mod_re_div_2_nonneg.
    destruct H1 as (H1, H6).
    apply eq_c_sqrt_add_modulus_Re_div_2_0 in H1.
    destruct H1 as (H1, _).
    apply (rngl_le_antisymm Hor) in H2; [ clear H1 | easy ].
    assert (H : z = 0%C) by now apply eq_c_eq.
    rewrite Heqz in H.
    now apply c_integral in H; destruct H.
  }
}
rewrite H4, (rngl_mul_0_r Hos), (rngl_sub_0_l Hop) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
apply eq_c_sqrt_add_modulus_Re_div_2_0 in H4.
destruct H4 as (Hrb, H6).
clear Hi2; rename H6 into Hi2.
apply (rngl_integral Hos Hio) in H5.
destruct H5 as [H5| H5]; cycle 1. {
  rewrite H5, (rngl_mul_0_r Hos) in H1.
  apply eq_c_sqrt_add_modulus_Re_div_2_0 in H1.
  destruct H1 as (H1, _).
  apply (rngl_le_antisymm Hor) in H2; [ clear H1 | easy ].
  assert (H : z = 0%C) by now apply eq_c_eq.
  rewrite Heqz in H.
  now apply c_integral in H; destruct H.
}
clear z Heqz H1 H2 H3.
apply eq_c_sqrt_add_modulus_Re_div_2_0 in H5.
destruct H5 as (Hra, Hia).
progress unfold is_negative_real_prop in Hrab.
apply Hrab; clear Hrab.
split. {
  split; [ | easy ].
  apply rngl_le_neq.
  split; [ easy | ].
  now intros H; apply H1z; apply eq_c_eq.
} {
  split; [ | easy ].
  apply rngl_le_neq.
  split; [ easy | ].
  now intros H; apply H2z; apply eq_c_eq.
}
Qed.

Theorem c_sqrt_mul_when_Im_nonneg_neg :
  ∀ z₁ z₂,
  (0 ≤ Im z₁)%L
  → (Im z₂ < 0)%L
  → (Re z₂ * ‖ z₁ ‖ < Re z₁ * ‖ z₂ ‖)%L
  → (√(z₁ * z₂) = √z₁ * √z₂)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  apply eq_c_eq.
  now do 2 rewrite (H1 (Re _)), (H1 (Im _)).
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2nz.
intros * Hi1 Hi2 Hrr.
destruct (c_eq_dec Heo z₁ 0) as [H1z| H1z]. {
  subst z₁.
  rewrite (c_mul_0_l Hos).
  rewrite c_sqrt_0; symmetry.
  apply (c_mul_0_l Hos).
}
destruct (c_eq_dec Heo z₂ 0) as [H2z| H2z]. {
  subst z₂.
  rewrite (c_mul_0_r Hos).
  rewrite c_sqrt_0; symmetry.
  apply (c_mul_0_r Hos).
}
specialize (c_squ_sqrt_mul z₁ z₂) as H12.
apply c_eq_cases in H12.
destruct H12 as [H12| H12]; [ easy | exfalso ].
progress unfold c_sqrt in H12.
rewrite (rngl_signp_of_nonneg (Im z₁)) in H12; [ | easy ].
rewrite (rngl_signp_of_neg Hor (Im z₂)) in H12; [ | easy ].
rewrite (rngl_mul_opp_l Hop) in H12.
do 2 rewrite rngl_mul_1_l in H12.
remember (z₁ * z₂)%C as z.
move z before z₂.
progress unfold c_mul in H12; cbn in H12.
do 2 rewrite (rngl_mul_opp_r Hop) in H12.
injection H12; clear H12; intros H2 H1.
move H1 after H2.
rewrite (rngl_opp_sub_distr Hop) in H1.
rewrite (rngl_sub_opp_r Hop) in H1.
rewrite (rngl_opp_add_distr Hop) in H2.
rewrite (rngl_opp_involutive Hop) in H2.
specialize (rl_sqrt_nonneg ((‖ z ‖ + Re z) / 2)%L) as H3.
specialize (H3 (c_modulus_add_re_div_2_nonneg Hop Hiv Hto _)).
specialize (rl_sqrt_nonneg ((‖ z ‖ - Re z) / 2)%L) as H4.
specialize (H4 (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto _)).
apply (rngl_nlt_ge Hor) in H4.
apply H4; clear H4.
rewrite H2.
apply  (rngl_lt_sub_0 Hop Hor).
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto).
} {
  apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
}
rewrite <- rl_sqrt_mul; cycle 1. {
  apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
} {
  apply (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto).
}
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 2 rewrite (rngl_mul_div_assoc Hiv).
do 2 rewrite (rngl_div_div Hos Hiv _ _ _ H2nz H2nz).
rewrite fold_rngl_squ.
rewrite (rl_sqrt_div Hop Hiv Hto _ 2²); cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (c_sub_modulus_re Hop Hiv Hto).
  apply (c_add_modulus_re Hop Hiv Hto).
} {
  apply (rngl_squ_pos Hos Hto Hio _ H2nz).
}
rewrite (rl_sqrt_div Hop Hiv Hto _ 2²); cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (c_add_modulus_re Hop Hiv Hto).
  apply (c_sub_modulus_re Hop Hiv Hto).
} {
  apply (rngl_squ_pos Hos Hto Hio _ H2nz).
}
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | apply (rngl_0_le_2 Hos Hto) ].
apply (rngl_div_lt_mono_pos_r Hop Hiv Hto). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
apply (rl_sqrt_lt_rl_sqrt Hto). {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply (c_sub_modulus_re Hop Hiv Hto).
  apply (c_add_modulus_re Hop Hiv Hto).
}
rewrite rngl_mul_add_distr_l, rngl_mul_add_distr_r.
do 2 rewrite (rngl_mul_sub_distr_l Hop).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
do 2 rewrite (rngl_add_sub_assoc Hop).
apply (rngl_sub_lt_mono_r Hop Hor).
do 2 rewrite <- (rngl_add_sub_swap Hop).
do 2 rewrite <- (rngl_add_sub_assoc Hop).
apply (rngl_add_lt_mono_l Hos Hor).
apply (rngl_lt_add_lt_sub_l Hop Hor).
rewrite (rngl_add_sub_assoc Hop).
apply (rngl_lt_sub_lt_add_l Hop Hor).
do 2 rewrite <- (rngl_mul_2_l (_ * _)).
apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
now rewrite (rngl_mul_comm Hic).
Qed.

Theorem c_sqrt_mul_im_nonneg_neg_nonneg :
  ∀ z₁ z₂,
  (√(z₁ * z₂))%C = (√z₁ * √z₂)%C
  → z₁ ≠ 0%C
  → (0 ≤ Im z₁)%L
  → (Im z₂ < 0)%L
  → (0 ≤ Im (z₁ * z₂))%L
  → (Re z₂ * ‖ z₁ ‖ < Re z₁ * ‖ z₂ ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz H1z Hzz1 Hzz2 Hizz.
progress unfold c_sqrt in Hzz.
rewrite (rngl_signp_of_nonneg (Im z₁)) in Hzz; [ | easy ].
rewrite rngl_mul_1_l in Hzz.
rewrite (rngl_signp_of_neg Hor (Im z₂)) in Hzz; [ | easy ].
rewrite (rngl_mul_opp_l Hop) in Hzz.
rewrite rngl_mul_1_l in Hzz.
remember (z₁ * z₂)%C as z.
move z before z₂.
injection Hzz; clear Hzz; intros H2 H1.
move H1 after H2.
rewrite (rngl_mul_opp_r Hop) in H1, H2.
rewrite (rngl_signp_of_nonneg (Im z)) in H1; [ | easy ].
rewrite rngl_mul_1_l in H1.
apply (rngl_add_move_l Hop) in H1.
apply (rngl_add_move_0_l Hop) in H1.
rewrite rngl_add_assoc in H1.
rewrite rngl_add_comm in H1.
apply (rngl_eq_add_0 Hos Hor) in H1; cycle 1. {
  apply rl_sqrt_add_mod_re_div_2_nonneg.
} {
  apply (rngl_add_nonneg_nonneg Hos Hor). {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply rl_sqrt_add_mod_re_div_2_nonneg.
    apply rl_sqrt_add_mod_re_div_2_nonneg.
  } {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
  }
}
destruct H1 as (H1, H3).
apply eq_c_sqrt_add_modulus_Re_div_2_0 in H1.
clear Hizz.
destruct H1 as (Hrzz, Hizz).
apply (rngl_eq_add_0 Hos Hor) in H3; cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply rl_sqrt_add_mod_re_div_2_nonneg.
  apply rl_sqrt_add_mod_re_div_2_nonneg.
} {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply rl_sqrt_sub_mod_re_div_2_nonneg.
  apply rl_sqrt_sub_mod_re_div_2_nonneg.
}
destruct H3 as (H3, H4).
apply (rngl_integral Hos Hio) in H3.
apply (rngl_integral Hos Hio) in H4.
destruct H3 as [H3| H3]. {
  apply eq_c_sqrt_add_modulus_Re_div_2_0 in H3.
  destruct H3 as (Hr1z, Hi1z).
  clear Hzz1.
  destruct H4 as [H4| H4]. {
    apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H4.
    destruct H4 as (Hzr1, _).
    apply (rngl_le_antisymm Hor) in Hzr1; [ | easy ].
    now exfalso; apply H1z, eq_c_eq.
  } {
    apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H4.
    destruct H4 as (_, H).
    rewrite H in Hzz2.
    now apply rngl_lt_irrefl in Hzz2.
  }
}
apply eq_c_sqrt_add_modulus_Re_div_2_0 in H3.
destruct H3 as (_, H).
rewrite H in Hzz2.
now apply rngl_lt_irrefl in Hzz2.
Qed.

Theorem c_sqrt_mul_im_nonneg_neg_neg :
  ∀ z₁ z₂,
  (√(z₁ * z₂))%C = (√z₁ * √z₂)%C
  → (0 ≤ Im z₁)%L
  → (Im z₂ < 0)%L
  → (Im (z₁ * z₂) < 0)%L
  → (Re z₂ * ‖ z₁ ‖ < Re z₁ * ‖ z₂ ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hzz Hzz1 Hzz2 Hizz.
  rewrite (H1 (Im z₂)) in Hzz2.
  now apply rngl_lt_irrefl in Hzz2.
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2nz.
intros * Hzz Hzz1 Hzz2 Hizz.
progress unfold c_sqrt in Hzz.
rewrite (rngl_signp_of_nonneg (Im z₁)) in Hzz; [ | easy ].
rewrite rngl_mul_1_l in Hzz.
rewrite (rngl_signp_of_neg Hor (Im z₂)) in Hzz; [ | easy ].
rewrite (rngl_mul_opp_l Hop) in Hzz.
rewrite rngl_mul_1_l in Hzz.
remember (z₁ * z₂)%C as z.
move z before z₂.
injection Hzz; clear Hzz; intros H2 H1.
move H1 after H2.
rewrite (rngl_mul_opp_r Hop) in H1, H2.
rewrite (rngl_add_opp_l Hop) in H2.
assert (H3 : (0 < √((‖ z ‖ - Re z) / 2))%L). {
  apply rngl_le_neq.
  split.
  apply rl_sqrt_sub_mod_re_div_2_nonneg.
  intros H; symmetry in H.
  apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H.
  destruct H as (_, H).
  rewrite H in Hizz.
  now apply rngl_lt_irrefl in Hizz.
}
rewrite H2 in H3; clear H2.
rename H3 into H2.
apply -> (rngl_lt_0_sub Hop Hor) in H2.
apply (rngl_lt_lt_squ Hop Hiq Hto) in H2; cycle 1.
apply (rngl_mul_comm Hic).
apply (rngl_mul_nonneg_nonneg Hos Hor).
apply rl_sqrt_sub_mod_re_div_2_nonneg.
apply rl_sqrt_add_mod_re_div_2_nonneg.
do 2 rewrite (rngl_squ_mul Hic) in H2.
rewrite rngl_squ_sqrt in H2; cycle 1.
apply (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto).
rewrite rngl_squ_sqrt in H2; cycle 1.
apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
rewrite rngl_squ_sqrt in H2; cycle 1.
apply (c_modulus_add_re_div_2_nonneg Hop Hiv Hto).
rewrite rngl_squ_sqrt in H2; cycle 1.
apply (c_modulus_sub_re_div_2_nonneg Hop Hiv Hto).
do 2 rewrite (rngl_div_mul_mul_div Hic Hiv) in H2.
do 2 rewrite (rngl_mul_div_assoc Hiv) in H2.
apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto 2) in H2; cycle 1.
apply (rngl_0_lt_2 Hos Hc1 Hto).
do 2 rewrite (rngl_div_mul Hiv _ _ H2nz) in H2.
apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto 2) in H2; cycle 1.
apply (rngl_0_lt_2 Hos Hc1 Hto).
do 2 rewrite (rngl_div_mul Hiv _ _ H2nz) in H2.
ring_simplify in H2.
apply (rngl_sub_lt_mono_r Hop Hor) in H2.
rewrite <- (rngl_add_sub_assoc Hop) in H2.
rewrite <- (rngl_add_sub_swap Hop) in H2.
rewrite <- (rngl_add_sub_assoc Hop) in H2.
apply (rngl_add_lt_mono_l Hos Hor) in H2.
apply (rngl_lt_sub_lt_add_l Hop Hor) in H2.
rewrite (rngl_add_sub_assoc Hop) in H2.
apply (rngl_lt_add_lt_sub_l Hop Hor) in H2.
do 2 rewrite <- (rngl_mul_2_l (_ * _)) in H2.
rewrite (rngl_mul_comm Hic (c_modulus _)) in H2.
apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto) in H2; [ easy | ].
now apply (rngl_0_lt_2 Hos Hc1 Hto).
Qed.

Definition c_mul_is_small (z₁ z₂ : Complex T) :=
   ((z₁ =? 0)%C ||
    (z₂ =? 0)%C ||
    if (0 ≤? Im z₁)%L then
      if (0 ≤? Im z₂)%L then
        negb (is_negative_real z₁ && is_negative_real z₂)
      else
        (Re z₂ * ‖ z₁ ‖ <? Re z₁ * ‖ z₂ ‖)%L
    else
      if (0 ≤? Im z₂)%L then
        (Re z₁ * ‖ z₂ ‖ <? Re z₂ * ‖ z₁ ‖)%L
      else
        false)%bool.

Definition c_mul_is_small_prop z₁ z₂ :=
  z₁ = 0%C ∨
  z₂ = 0%C ∨
  if (0 ≤? Im z₁)%L then
    if (0 ≤? Im z₂)%L then
      ¬ (is_negative_real_prop z₁ ∧ is_negative_real_prop z₂)%L
    else
      (Re z₂ * ‖ z₁ ‖ < Re z₁ * ‖ z₂ ‖)%L
  else
    if (0 ≤? Im z₂)%L then
      (Re z₁ * ‖ z₂ ‖ < Re z₂ * ‖ z₁ ‖)%L
    else
      False.

Theorem c_mul_is_small_bool_prop z₁ z₂ :
  c_mul_is_small z₁ z₂ = true ↔ c_mul_is_small_prop z₁ z₂.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
split; intros H12. {
  progress unfold c_mul_is_small in H12.
  apply Bool.orb_true_iff in H12.
  destruct H12 as [H12| H12]. {
    apply Bool.orb_true_iff in H12.
    destruct H12 as [H12| H12]; [ | right ].
    1, 2: now left; apply c_eqb_eq.
  }
  right; right.
  remember (0 ≤? Im z₁)%L as zi1 eqn:Hzi1.
  remember (0 ≤? Im z₂)%L as zi2 eqn:Hzi2.
  symmetry in Hzi1, Hzi2.
  destruct zi1. {
    destruct zi2. {
      intros H1.
      apply Bool.eq_true_not_negb_iff in H12.
      apply H12; clear H12.
      apply Bool.andb_true_iff.
      now split; apply is_negative_real_bool_prop.
    }
    now apply (rngl_ltb_lt Heo).
  }
  destruct zi2; [ now apply (rngl_ltb_lt Heo) | easy ].
} {
  apply Bool.orb_true_iff.
  destruct H12 as [H12| H12]. {
    left; apply Bool.orb_true_iff.
    now left; apply c_eqb_eq.
  }
  destruct H12 as [H12| H12]. {
    left; apply Bool.orb_true_iff.
    now right; apply c_eqb_eq.
  }
  right.
  remember (0 ≤? Im z₁)%L as zi1 eqn:Hzi1.
  remember (0 ≤? Im z₂)%L as zi2 eqn:Hzi2.
  symmetry in Hzi1, Hzi2.
  destruct zi1. {
    destruct zi2; [ | now apply (rngl_ltb_lt Heo) ].
    apply Bool.eq_true_not_negb_iff.
    intros H1; apply H12; clear H12.
    apply Bool.andb_true_iff in H1.
    now split; apply is_negative_real_bool_prop.
  }
  destruct zi2; [ now apply (rngl_ltb_lt Heo) | easy ].
}
Qed.

Theorem c_mul_is_not_small_bool_prop z₁ z₂ :
  c_mul_is_small z₁ z₂ = false ↔ ¬ c_mul_is_small_prop z₁ z₂.
Proof.
split; intros H12. {
  apply Bool.not_true_iff_false in H12.
  intros H; apply H12; clear H12.
  now apply c_mul_is_small_bool_prop.
} {
  apply Bool.not_true_iff_false.
  intros H; apply H12; clear H12.
  now apply c_mul_is_small_bool_prop.
}
Qed.

Theorem c_mul_is_small_symm :
  ∀ z₁ z₂, c_mul_is_small_prop z₁ z₂ → c_mul_is_small_prop z₂ z₁.
Proof.
intros * H12.
progress unfold c_mul_is_small_prop.
destruct H12 as [H12| H12]; [ now right; left | ].
destruct H12 as [H12| H12]; [ now left | right; right ].
remember (0 ≤? Im z₁)%L as zi1 eqn:Hzi1.
remember (0 ≤? Im z₂)%L as zi2 eqn:Hzi2.
symmetry in Hzi1, Hzi2.
destruct zi1; [ | easy ].
destruct zi2; [ | easy ].
intros H1; apply H12; clear H12.
now apply and_comm.
Qed.

Theorem c_mul_is_small_comm :
  ∀ z₁ z₂, c_mul_is_small z₁ z₂ = c_mul_is_small z₂ z₁.
Proof.
intros.
remember (c_mul_is_small z₂ z₁) as ov eqn:Hov.
symmetry in Hov.
destruct ov. {
  apply c_mul_is_small_bool_prop.
  apply c_mul_is_small_symm.
  now apply c_mul_is_small_bool_prop.
} {
  apply Bool.not_true_iff_false in Hov.
  apply Bool.not_true_iff_false.
  intros H; apply Hov; clear Hov.
  apply c_mul_is_small_bool_prop.
  apply c_mul_is_small_symm.
  now apply c_mul_is_small_bool_prop.
}
Qed.

Theorem c_sqrt_mul_im_nonneg_nonneg_not_ov :
  ∀ z₁ z₂,
  (√(z₁ * z₂))%C = (√z₁ * √z₂)%C
  → (0 ≤ Im z₁)%L
  → (0 ≤ Im z₂)%L
  → c_mul_is_small_prop z₁ z₂.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz Hzz1 Hzz2.
destruct (rngl_leb_dec 0 (Re z₁)) as [Hzr1| Hzr1]. {
  apply rngl_leb_le in Hzr1.
  right; right.
  apply rngl_leb_le in Hzz1, Hzz2.
  rewrite Hzz1, Hzz2.
  progress unfold is_negative_real_prop.
  intros ((H1, _), (H2, _)).
  now apply (rngl_nle_gt Hor) in H1.
}
apply (rngl_leb_gt_iff Hto) in Hzr1.
move Hzr1 before Hzz2.
destruct (rngl_leb_dec 0 (Re z₂)) as [Hzr2| Hzr2]. {
  apply rngl_leb_le in Hzr2.
  right; right.
  apply rngl_leb_le in Hzz1, Hzz2.
  rewrite Hzz1, Hzz2.
  progress unfold is_negative_real_prop.
  intros ((H1, _), (H2, _)).
  now apply (rngl_nle_gt Hor) in H2.
}
apply (rngl_leb_gt_iff Hto) in Hzr2.
move Hzr2 before Hzr1.
destruct (rngl_eqb_dec (Im z₁) 0) as [Hi1z| Hi1z]. {
  apply (rngl_eqb_eq Heo) in Hi1z.
  move Hi1z before Hzz1; clear Hzz1.
  destruct (rngl_eqb_dec (Im z₂) 0) as [Hi2z| Hi2z]. {
    apply (rngl_eqb_eq Heo) in Hi2z.
    move Hi2z before Hzz2; clear Hzz2.
    progress unfold c_sqrt in Hzz.
    rewrite Hi1z, Hi2z in Hzz.
    rewrite rngl_signp_0 in Hzz.
    rewrite rngl_mul_1_l in Hzz.
    remember (z₁ * z₂)%C as z.
    move z before z₂.
    injection Hzz; clear Hzz; intros H2 H1.
    move H1 after H2.
    rewrite rngl_signp_of_nonneg in H1; cycle 1. {
      rewrite Heqz; cbn.
      rewrite Hi1z, Hi2z.
      rewrite (rngl_mul_0_l Hos), (rngl_mul_0_r Hos).
      rewrite rngl_add_0_l.
      apply (rngl_le_refl Hor).
    }
    rewrite rngl_mul_1_l in H1.
    clear H2.
    generalize Hzr1; intros Hzr1'.
    generalize Hzr2; intros Hzr2'.
    apply rngl_lt_le_incl in Hzr1', Hzr2'.
    rewrite (proj2 (eq_c_sqrt_add_modulus_Re_div_2_0 z₁)) in H1; [ | easy ].
    rewrite (proj2 (eq_c_sqrt_add_modulus_Re_div_2_0 z₂)) in H1; [ | easy ].
    clear Hzr1' Hzr2'.
    rewrite (rngl_mul_0_l Hos) in H1.
    rewrite (rngl_sub_0_l Hop) in H1.
    apply (rngl_add_move_0_r Hop) in H1.
    apply (rngl_eq_add_0 Hos Hor) in H1; cycle 1. {
      apply rl_sqrt_add_mod_re_div_2_nonneg.
    } {
      apply (rngl_mul_nonneg_nonneg Hos Hor).
      apply rl_sqrt_sub_mod_re_div_2_nonneg.
      apply rl_sqrt_sub_mod_re_div_2_nonneg.
    }
    destruct H1 as (_, H1).
    apply (rngl_integral Hos Hio) in H1.
    destruct H1 as [H1| H1]. {
      apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H1.
      destruct H1 as (H1, _).
      now apply (rngl_nlt_ge Hor) in H1.
    } {
      apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H1.
      destruct H1 as (H1, _).
      now apply (rngl_nlt_ge Hor) in H1.
    }
  }
  apply (rngl_eqb_neq Heo) in Hi2z.
  move Hi2z before Hzz2.
  right; right.
  apply rngl_leb_le in Hzz2.
  rewrite Hi1z, Hzz2, (rngl_leb_refl Hor).
  progress unfold is_negative_real_prop.
  now intros (_, (_, H1)).
}
apply (rngl_eqb_neq Heo) in Hi1z.
right; right.
apply rngl_leb_le in Hzz1, Hzz2.
rewrite Hzz1, Hzz2.
progress unfold is_negative_real_prop.
now intros ((_, H1), _).
Qed.

Theorem c_sqrt_mul_im_nonneg_neg_not_ov :
  ∀ z₁ z₂,
  (√(z₁ * z₂))%C = (√z₁ * √z₂)%C
  → z₁ ≠ 0%C
  → (0 ≤ Im z₁)%L
  → (Im z₂ < 0)%L
  → c_mul_is_small_prop z₁ z₂.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hzz H1z Hzz1 Hzz2.
right; right.
generalize Hzz1; intros H.
apply rngl_leb_le in H.
rewrite H; clear H.
generalize Hzz2; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H; clear H.
destruct (rngl_leb_dec 0 (Im (z₁ * z₂))) as [Hizz| Hizz]. {
  apply rngl_leb_le in Hizz.
  now apply c_sqrt_mul_im_nonneg_neg_nonneg.
} {
  apply (rngl_leb_gt_iff Hto) in Hizz.
  now apply c_sqrt_mul_im_nonneg_neg_neg.
}
Qed.

Theorem c_sqrt_mul_im_neg_neg_not_eq :
  ∀ z₁ z₂,
  (Im z₁ < 0)%L
  → (Im z₂ < 0)%L
  → (√(z₁ * z₂))%C ≠ (√z₁ * √z₂)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz1 Hzz2 Hzz.
remember (z₁ * z₂)%C as z.
move z before z₂.
injection Hzz; clear Hzz; intros H2 H1.
move H1 after H2.
rewrite (rngl_signp_of_neg Hor (Im z₁)) in H2; [ | easy ].
rewrite (rngl_signp_of_neg Hor (Im z₂)) in H2; [ | easy ].
do 3 rewrite (rngl_mul_opp_l Hop) in H2.
do 2 rewrite rngl_mul_1_l in H2.
rewrite (rngl_mul_opp_r Hop) in H2.
rewrite (rngl_add_opp_r Hop) in H2.
rewrite <- (rngl_opp_add_distr Hop) in H2.
apply (rngl_add_move_0_r Hop) in H2.
rewrite rngl_add_assoc in H2.
apply (rngl_eq_add_0 Hos Hor) in H2; cycle 1. {
  apply (rngl_add_nonneg_nonneg Hos Hor). {
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
  } {
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
    apply rl_sqrt_add_mod_re_div_2_nonneg.
  }
} {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  apply rl_sqrt_add_mod_re_div_2_nonneg.
  apply rl_sqrt_sub_mod_re_div_2_nonneg.
}
destruct H2 as (H2, H3).
apply (rngl_integral Hos Hio) in H3.
destruct H3 as [H3| H3]. {
  apply eq_c_sqrt_add_modulus_Re_div_2_0 in H3.
  destruct H3 as (_, H3).
  rewrite H3 in Hzz1.
  now apply rngl_lt_irrefl in Hzz1.
} {
  apply eq_c_sqrt_sub_modulus_Re_div_2_0 in H3.
  destruct H3 as (_, H3).
  rewrite H3 in Hzz2.
  now apply rngl_lt_irrefl in Hzz2.
}
Qed.

Theorem c_sqrt_mul_not_ov :
  ∀ z₁ z₂ : Complex T,
  c_mul_is_small_prop z₁ z₂
  ↔ (√(z₁ * z₂))%C = (√z₁ * √z₂)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
split; intros Hzz. {
  destruct Hzz as [Hzz| Hzz]. {
    subst; rewrite (c_mul_0_l Hos).
    rewrite c_sqrt_0; symmetry.
    apply (c_mul_0_l Hos).
  }
  destruct Hzz as [Hzz| Hzz]. {
    subst; rewrite (c_mul_0_r Hos).
    rewrite c_sqrt_0; symmetry.
    apply (c_mul_0_r Hos).
  }
  remember (0 ≤? Im z₁)%L as zi1 eqn:Hzi1.
  remember (0 ≤? Im z₂)%L as zi2 eqn:Hzi2.
  symmetry in Hzi1, Hzi2.
  destruct zi1. {
    apply rngl_leb_le in Hzi1.
    destruct zi2.
    apply rngl_leb_le in Hzi2.
    now apply c_sqrt_mul_when_Im_nonneg_nonneg.
    apply (rngl_leb_gt_iff Hto) in Hzi2.
    now apply c_sqrt_mul_when_Im_nonneg_neg.
  }
  destruct zi2; [ | easy ].
  apply (rngl_leb_gt_iff Hto) in Hzi1.
  apply rngl_leb_le in Hzi2.
  rewrite (c_mul_comm Hic z₁).
  rewrite (c_mul_comm Hic √z₁).
  now apply c_sqrt_mul_when_Im_nonneg_neg.
}
destruct (c_eq_dec Heo z₁ 0) as [H1z| H1z]; [ now left | ].
destruct (c_eq_dec Heo z₂ 0) as [H2z| H2z]; [ now right; left | ].
destruct (rngl_leb_dec 0 (Im z₁)) as [Hzz1| Hzz1]. {
  clear H2z.
  apply rngl_leb_le in Hzz1.
  destruct (rngl_leb_dec 0 (Im z₂)) as [Hzz2| Hzz2]. {
    apply rngl_leb_le in Hzz2.
    now apply c_sqrt_mul_im_nonneg_nonneg_not_ov.
  }
  apply (rngl_leb_gt_iff Hto) in Hzz2.
  now apply c_sqrt_mul_im_nonneg_neg_not_ov.
}
apply (rngl_leb_gt_iff Hto) in Hzz1.
destruct (rngl_leb_dec 0 (Im z₂)) as [Hzz2| Hzz2]. {
  clear H1z.
  apply rngl_leb_le in Hzz2.
  apply c_mul_is_small_symm.
  rewrite (c_mul_comm Hic z₁) in Hzz.
  rewrite (c_mul_comm Hic √_) in Hzz.
  now apply c_sqrt_mul_im_nonneg_neg_not_ov.
}
apply (rngl_leb_gt_iff Hto) in Hzz2.
exfalso; revert Hzz.
now apply c_sqrt_mul_im_neg_neg_not_eq.
Qed.

Theorem rngl_pow_nonneg : ∀ a n, (0 ≤ a → 0 ≤ a ^ n)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hza.
induction n; cbn.
apply (rngl_0_le_1 Hos Hto).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
Qed.

Theorem rngl_sqrt_pow : ∀ n a, (0 ≤ a)%L → (√a ^ n)%L = √(a ^ n).
Proof.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Hza.
symmetry.
induction n; cbn; [ apply (rl_sqrt_1 Hop Hiq Hto) | ].
rewrite <- IHn.
apply rl_sqrt_mul; [ easy | ].
now apply rngl_pow_nonneg.
Qed.

Theorem c_opp_rngl_opp : ∀ z, (- z)%C = (- z)%L.
Proof.
intros.
progress unfold c_ring_like_op.
progress unfold c_opp.
progress unfold rngl_opp.
progress unfold c_opt_opp_or_psub.
cbn.
destruct (rngl_opt_opp_or_psub T) as [s| ]; [ | easy ].
now destruct s.
Qed.

Theorem c_mul_rngl_mul : ∀ z₁ z₂, (z₁ * z₂)%C = (z₁ * z₂)%L.
Proof. easy. Qed.

Theorem c_squ_rngl_squ : ∀ z, z²%C = z²%L.
Proof. easy. Qed.

Theorem c_pow_rngl_pow : ∀ z n, (z ^ n)%C = (z ^ n)%L.
Proof. easy. Qed.

Theorem fold_c_squ: ∀ z, (z * z)%C = z²%C.
Proof. easy. Qed.

Theorem c_mul_1_r : ∀ z, (z * 1)%C = z.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
rewrite (c_mul_comm Hic).
apply (c_mul_1_l Hos).
Qed.

Theorem c_pow_1 : 1²%C = 1%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
apply eq_c_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite rngl_mul_1_l, (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos), rngl_add_0_l.
Qed.

Theorem c_pow_squ : ∀ z n, (z ^ n)²%C = (z ^ (2 * n))%C.
Proof.
intros.
rewrite Nat.mul_comm.
induction n; [ apply c_pow_1 | cbn ].
rewrite (c_squ_mul Hic Hop).
rewrite <- c_pow_rngl_pow, IHn.
now rewrite (c_mul_assoc Hop).
Qed.

(* trigonometry equivalent to (θ₁+θ₂)/2 = θ₁/2 + θ₂/2, which
   works only if θ₁+θ₂ < 2π. Otherwise π has to be added. *)
Theorem c_sqrt_mul :
  ∀ z₁ z₂,
  (√(z₁ * z₂) =
     if c_mul_is_small z₁ z₂ then √z₁ * √z₂ else - (√z₁ * √z₂))%C.
Proof.
intros.
remember (c_mul_is_small _ _) as ov eqn:Hov.
symmetry in Hov.
destruct ov. {
  apply c_sqrt_mul_not_ov.
  now apply c_mul_is_small_bool_prop.
}
specialize (c_squ_sqrt_mul z₁ z₂) as H1.
apply c_eq_cases in H1.
destruct H1 as [H1| H1]; [ exfalso | easy ].
apply Bool.not_true_iff_false in Hov.
apply Hov; clear Hov.
apply c_mul_is_small_bool_prop.
now apply c_sqrt_mul_not_ov.
Qed.

Theorem c_sqrt_squ :
  ∀ z,
  (√z²)%C =
    if ((0 ≤? Im z)%L && negb (is_negative_real z))%bool then z else (-z)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
remember (_ && _)%bool as zi eqn:Hzi.
symmetry in Hzi.
destruct zi. {
  apply Bool.andb_true_iff in Hzi.
  destruct Hzi as (Hzi, Hnr).
  apply Bool.negb_true_iff in Hnr.
  progress unfold c_squ.
  rewrite (proj1 (c_sqrt_mul_not_ov _ _)); cycle 1. {
    right; right.
    rewrite Hzi.
    intros (H1, _).
    apply is_negative_real_bool_prop in H1.
    congruence.
  }
  rewrite fold_c_squ.
  apply c_squ_sqrt.
} {
  apply Bool.andb_false_iff in Hzi.
  progress unfold c_squ.
  rewrite c_sqrt_mul.
  progress unfold c_mul_is_small.
  remember (z =? 0)%C as zz eqn:Hzz.
  symmetry in Hzz.
  destruct zz. {
    apply c_eqb_eq in Hzz; subst z; cbn.
    rewrite c_sqrt_0, c_opp_0.
    apply (c_mul_0_l Hos).
  }
  cbn.
  destruct Hzi as [Hzi| Hzi]. {
    rewrite Hzi.
    progress f_equal.
    rewrite fold_c_squ.
    apply c_squ_sqrt.
  }
  apply Bool.negb_false_iff in Hzi.
  rewrite Hzi; cbn.
  progress unfold is_negative_real in Hzi.
  apply Bool.andb_true_iff in Hzi.
  destruct Hzi as (Hrz, Hiz).
  apply (rngl_eqb_eq Heo) in Hiz.
  rewrite Hiz, (rngl_leb_refl Hor).
  progress f_equal.
  apply c_squ_sqrt.
}
Qed.

Theorem c_seq_to_div_nat_0_l :
  ∀ n k, 0 < 2 ^ k / n → c_seq_to_div_nat 0 n k = 0%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hkn.
  apply eq_c_eq; cbn.
  now rewrite (H1 (Re _)), (H1 (Im _)).
}
intros * Hkn.
progress unfold c_seq_to_div_nat.
remember (2 ^ k / n) as m eqn:Hm.
clear n Hm; rename m into n.
destruct n; [ easy | clear Hkn ].
induction k; cbn; [ apply (c_mul_0_l Hos) | ].
cbn.
cbn in IHk.
apply c_integral in IHk.
destruct IHk as [H| H]. {
  rewrite H.
  (* lemma *)
  progress unfold c_sqrt; cbn.
  rewrite rngl_add_0_r.
  rewrite (c_modulus_0 Hop Hii Hto).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_div_0_l Hos Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  rewrite (rl_sqrt_0 Hop Hto Hii).
  rewrite (rngl_mul_0_r Hos).
  apply (c_mul_0_l Hos).
}
destruct (c_eq_dec Heo (c_nth_2_pow_root k 0) 0) as [Hcz| Hcz]. {
  rewrite Hcz.
  rewrite c_sqrt_0.
  apply (c_mul_0_l Hos).
}
now apply (c_pow_neq_0 Hc1) in H.
Qed.

Theorem c_eucl_dist_diag : ∀ z, c_eucl_dist z z = 0%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros.
progress unfold c_eucl_dist.
rewrite (c_sub_diag Hos).
apply (c_modulus_0 Hop Hii Hto).
Qed.

Theorem c_pow_mul_r: ∀ z m n, (z ^ (m * n))%C = ((z ^ m) ^ n)%C.
Proof.
intros.
do 3 rewrite c_pow_rngl_pow.
set (rpc := c_ring_like_prop_not_alg_closed Hic Hop Hiv Hto).
apply rngl_pow_mul_r.
Qed.

Theorem c_squ_pow_2 : ∀ z, (z² = z ^ 2)%C.
Proof.
intros; cbn.
now rewrite c_mul_1_r.
Qed.

Theorem c_nth_2_pow_root_pow_2_pow :
  ∀ n z, (c_nth_2_pow_root n z ^ 2 ^ n)%C = z.
Proof.
intros.
induction n; [ apply c_mul_1_r | ].
cbn - [ "^" ].
rewrite Nat.pow_succ_r'.
rewrite c_pow_mul_r.
rewrite <- c_squ_pow_2.
now rewrite c_squ_sqrt.
Qed.

Fixpoint c_pow_nat_nb_turns n z :=
  match n with
  | 0 => 0
  | S m =>
      c_pow_nat_nb_turns m z + Nat.b2n (negb (c_mul_is_small z (z ^ m)))
  end.

Theorem c_mul_nat_nb_turns_succ_l_false :
  ∀ n z,
  c_pow_nat_nb_turns (S n) z = 0
  ↔ c_pow_nat_nb_turns n z = 0 ∧ c_mul_is_small z (z ^ n) = true.
Proof.
intros; cbn.
destruct (c_pow_nat_nb_turns _ _); [ | easy ].
now destruct (c_mul_is_small _ _).
Qed.

Theorem c_sqrt_pow :
  ∀ n z,
  c_pow_nat_nb_turns n z = 0
  → (√z ^ n = √(z ^ n))%C.
Proof.
intros * Hs.
symmetry.
induction n; cbn; [ apply c_sqrt_1 | ].
do 2 rewrite <- c_pow_rngl_pow.
apply c_mul_nat_nb_turns_succ_l_false in Hs.
rewrite <- IHn; [ | easy ].
apply c_sqrt_mul_not_ov.
now apply c_mul_is_small_bool_prop.
Qed.

Theorem rngl_characteristic_1_c_0 :
  rngl_characteristic T = 1 →
  ∀ z, (z = 0)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros Hc1 *.
specialize (rngl_characteristic_1 Hos Hc1) as H1.
apply eq_c_eq.
do 2 rewrite (H1 (Re _)).
now do 2 rewrite (H1 (Im _)).
Qed.

Theorem c_modulus_when_Im_0 : ∀ z, Im z = 0%L → ‖ z ‖ = rngl_abs (Re z).
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hiz.
progress unfold c_modulus.
progress unfold rl_modl.
rewrite Hiz, (rngl_squ_0 Hos), rngl_add_0_r.
apply (rl_sqrt_squ Hop Hto).
Qed.

Definition c_arg_leb z1 z2 :=
  if (0 ≤? Im z1)%L then
    if (0 ≤? Im z2)%L then (Re z2 * ‖ z1 ‖ ≤? Re z1 * ‖ z2 ‖)%L
    else true
  else
    if (0 ≤? Im z2)%L then false
    else (Re z1 * ‖ z2 ‖ ≤? Re z2 * ‖ z1 ‖)%L.

Notation "z1 ≤ z2" := (c_arg_leb z1 z2 = true) : c_scope.

Theorem c_modulus_pos : ∀ z, (0 < ‖ z ‖)%L ↔ z ≠ 0%C.
Proof.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros.
split; intros Hz. {
  intros H; rewrite H in Hz.
  rewrite (c_modulus_0 Hop Hii Hto) in Hz.
  now apply rngl_lt_irrefl in Hz.
}
apply rngl_le_neq.
split; [ apply c_modulus_nonneg | ].
intros H; symmetry in H.
now apply eq_c_modulus_0 in H.
Qed.

Theorem c_mul_is_small_le :
  ∀ z1 z2 z3,
  z2 ≠ 0%C
  → (z3 ≤ z2)%C
  → c_mul_is_small z1 z2 = true
  → c_mul_is_small z1 z3 = true.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_c_0 Hc1) as H1.
  intros * H2z H32 H12.
  rewrite (H1 z1).
  apply c_mul_is_small_bool_prop.
  now left.
}
intros * H2z H32 H12.
apply c_mul_is_small_bool_prop in H12.
apply c_mul_is_small_bool_prop.
progress unfold c_mul_is_small_prop in H12.
progress unfold c_mul_is_small_prop.
progress unfold c_arg_leb in H32.
destruct H12 as [H12| H12]; [ now left | ].
destruct H12 as [H12| H12]; [ easy | ].
destruct (c_eq_dec Heo z1 0) as [H1z| H1z]; [ now left | right ].
destruct (c_eq_dec Heo z3 0) as [H3z| H3z]; [ now left | right ].
move H1z after H2z; move H3z before H2z.
remember (0 ≤? Im z1)%L as zi1 eqn:Hzi1.
remember (0 ≤? Im z2)%L as zi2 eqn:Hzi2.
remember (0 ≤? Im z3)%L as zi3 eqn:Hzi3.
symmetry in Hzi1, Hzi2, Hzi3.
destruct zi1. {
  destruct zi3. {
    intros ((H1, H2), (H3, H4)).
    move H3 before H1.
    destruct zi2. {
      apply H12; clear H12.
      split; [ easy | ].
      progress unfold is_negative_real_prop.
      move Hzi1 after Hzi2.
      apply rngl_leb_le in Hzi1, Hzi2, Hzi3, H32.
      clear Hzi1 Hzi3.
      rewrite c_modulus_when_Im_0 in H32; [ | easy ].
      split. {
        apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto (rngl_abs (Re z3))). {
          apply rngl_le_neq.
          split; [ apply (rngl_abs_nonneg Hop Hto) | ].
          intros H; symmetry in H.
          apply (eq_rngl_abs_0 Hop) in H.
          rewrite H in H3.
          now apply rngl_lt_irrefl in H3.
        }
        rewrite (rngl_mul_0_l Hos).
        eapply (rngl_le_lt_trans Hor); [ apply H32 | ].
        rewrite (rngl_mul_comm Hic).
        apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
        now apply c_modulus_pos.
      }
      clear Hzi2.
      rewrite (rngl_abs_nonpos_eq Hop Hto) in H32; cycle 1. {
        now apply rngl_lt_le_incl.
      }
      rewrite (rngl_mul_opp_r Hop), (rngl_mul_comm Hic) in H32.
      apply (rngl_le_opp_l Hop Hor) in H32.
      rewrite <- rngl_mul_add_distr_l in H32.
      destruct (rngl_eqb_dec (Im z2) 0) as [Hi2| Hi2]. {
        now apply (rngl_eqb_eq Heo).
      }
      exfalso; apply (rngl_eqb_neq Heo) in Hi2.
      apply (rngl_nlt_ge Hor) in H32.
      apply H32; clear H32.
      rewrite (rngl_mul_comm Hic).
      apply (rngl_mul_pos_neg Hop Hiq Hor); [ | easy ].
      rewrite rngl_add_comm.
      apply rngl_le_neq.
      split; [ apply (c_add_modulus_re Hop Hiv Hto) | ].
      intros H; symmetry in H.
      now apply eq_rngl_add_modulus_re_0 in H.
    } {
      clear H32.
      rewrite c_modulus_when_Im_0 in H12; [ | easy ].
      rewrite (rngl_abs_nonpos_eq Hop Hto) in H12; cycle 1. {
        now apply rngl_lt_le_incl.
      }
      rewrite (rngl_mul_opp_r Hop), (rngl_mul_comm Hic) in H12.
      apply (rngl_lt_opp_l Hop Hor) in H12.
      rewrite <- rngl_mul_add_distr_l in H12.
      apply (rngl_nle_gt Hor) in H12.
      apply H12; clear H12.
      apply (rngl_mul_nonpos_nonneg Hop Hor).
      now apply rngl_lt_le_incl.
      rewrite rngl_add_comm.
      apply (c_add_modulus_re Hop Hiv Hto).
    }
  }
  destruct zi2; [ easy | ].
  move Hzi1 after Hzi2.
  apply rngl_leb_le in H32.
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto (‖ z2 ‖)). {
    now apply c_modulus_pos.
  }
  rewrite (rngl_mul_mul_swap Hic).
  eapply (rngl_le_lt_trans Hor). {
    apply (rngl_mul_le_mono_pos_r Hop Hiq Hto _ _ (‖ z1 ‖)) in H32; cycle 1. {
      now apply c_modulus_pos.
    }
    apply H32.
  }
  do 2 rewrite (rngl_mul_mul_swap Hic _ (‖ z3 ‖)).
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto); [ | easy ].
  now apply c_modulus_pos.
}
destruct zi2; [ | easy ].
destruct zi3; [ | easy ].
move Hzi1 after Hzi2.
apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto (‖ z2 ‖)). {
  now apply c_modulus_pos.
}
rewrite (rngl_mul_mul_swap Hic).
eapply (rngl_lt_le_trans Hor). {
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto (‖ z3 ‖)) in H12; cycle 1. {
    now apply c_modulus_pos.
  }
  apply H12.
}
do 2 rewrite (rngl_mul_mul_swap Hic _ (‖ z1 ‖)).
apply (rngl_mul_le_mono_pos_r Hop Hiq Hto). {
  now apply c_modulus_pos.
}
now apply rngl_leb_le.
Qed.

Theorem c_arg_le_refl : ∀ z, (z ≤ z)%C.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold c_arg_leb.
destruct (0 ≤? Im z)%L; apply (rngl_leb_refl Hor).
Qed.

Theorem c_arg_le_0_r : ∀ z, (z ≤ 0)%C ↔ (0 ≤ Im z)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros.
progress unfold c_arg_leb; cbn.
rewrite (rngl_leb_refl Hor).
rewrite (rngl_mul_0_l Hos).
rewrite (c_modulus_0 Hop Hii Hto).
rewrite (rngl_mul_0_r Hos).
rewrite (rngl_leb_refl Hor).
remember (0 ≤? Im z)%L as zi eqn:Hzi.
symmetry in Hzi.
apply iff_sym.
destruct zi; [ now apply rngl_leb_le in Hzi | ].
now apply rngl_leb_nle in Hzi.
Qed.

Theorem mul_Re_mod_le_mul_Re_mod :
  ∀ z1 z2,
  (0 ≤ Im z1)%L
  → (Re z1 ≤ 0)%L
  → (Re z2 ≤ 0)%L
  → (Im z2 ≤ 0)%L
  → (0 ≤ Im z1 * Re z2 + Re z1 * Im z2)%L
  → (Re z1 * ‖ z2 ‖ ≤ Re z2 * ‖ z1 ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hzi1 Hzr1 Hr2z Hi2z Hzi12.
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_l Hop).
rewrite <- (rngl_abs_nonneg_eq Hop Hor (- _ * _)%L); cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
  apply c_modulus_nonneg.
}
rewrite <- (rngl_abs_nonneg_eq Hop Hor (- Re z1 * _)); cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
  apply c_modulus_nonneg.
}
apply (rngl_squ_le_abs_le Hop Hiq Hto).
do 2 rewrite (rngl_squ_mul Hic).
progress unfold c_modulus.
progress unfold rl_modl.
rewrite rngl_squ_sqrt; cycle 1.
apply (rngl_add_squ_nonneg Hos Hto).
rewrite rngl_squ_sqrt; cycle 1.
apply (rngl_add_squ_nonneg Hos Hto).
do 2 rewrite rngl_mul_add_distr_l.
do 2 rewrite (rngl_squ_opp Hop).
rewrite (rngl_mul_comm Hic (Re z1)²).
apply (rngl_add_le_mono_l Hos Hor).
rewrite <- (rngl_squ_opp Hop (Re z2)).
rewrite <- (rngl_squ_opp Hop (Re z1)).
rewrite <- (rngl_squ_opp Hop (Im z2)).
do 2 rewrite <- (rngl_squ_mul Hic).
apply (rngl_abs_le_squ_le Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor); cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ | easy ].
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
}
rewrite (rngl_abs_nonneg_eq Hop Hor); cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
  now apply (rngl_opp_nonneg_nonpos Hop Hor).
}
rewrite (rngl_mul_opp_l Hop).
rewrite (rngl_mul_opp_opp Hop).
apply (rngl_le_opp_l Hop Hor).
now rewrite (rngl_mul_comm Hic).
Qed.

Theorem Im_mul_nonneg_c_mul_is_not_small :
  ∀ z1 z2,
  z1 ≠ 0%C
  → (Re z2 < 0)%L
  → (Im z2 < 0)%L
  → (0 ≤ Im (z1 * z2))%L
  → c_mul_is_small z1 z2 = false.
Proof.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * H1z Hr2z Hi2z Hzi12.
assert (H2z : z2 ≠ 0%C). {
  intros H; subst.
  now apply rngl_lt_irrefl in Hi2z.
}
apply c_mul_is_not_small_bool_prop.
intros Hs12.
progress unfold c_mul_is_small_prop in Hs12.
destruct Hs12 as [Hs12| Hs12]; [ easy | ].
destruct Hs12 as [Hs12| Hs12]; [ easy | ].
generalize Hi2z; intros H.
apply (rngl_leb_gt_iff Hto) in H.
rewrite H in Hs12; clear H.
remember (0 ≤? Im z1)%L as zi1 eqn:Hzi1.
symmetry in Hzi1.
destruct zi1; [ | easy ].
apply rngl_leb_le in Hzi1.
cbn in Hzi12.
destruct (rngl_ltb_dec 0 (Re z1)) as [Hzr1| Hzr1]. {
  apply (rngl_ltb_lt Heo) in Hzr1.
  apply (rngl_nlt_ge Hor) in Hzi12.
  apply Hzi12; clear Hzi12.
  apply (rngl_add_nonpos_neg Hop Hor). {
    apply (rngl_mul_nonneg_nonpos Hop Hor); [ easy | ].
    now apply rngl_lt_le_incl.
  } {
    now apply (rngl_mul_pos_neg Hop Hiq Hor).
  }
}
apply (rngl_ltb_ge_iff Hto) in Hzr1.
move Hzi1 after Hr2z; move Hzr1 before Hzi1.
apply rngl_lt_le_incl in Hr2z, Hi2z.
apply (rngl_nle_gt Hor) in Hs12.
apply Hs12; clear Hs12.
now apply mul_Re_mod_le_mul_Re_mod.
Qed.

Theorem c_im_neg_neg_mul_is_not_small :
  ∀ z1 z2,
  (Im z1 < 0)%L
  → (Im z2 < 0)%L
  → c_mul_is_small z1 z2 = false.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hi1z Hi2z.
apply c_mul_is_not_small_bool_prop.
intros Hs.
progress unfold c_mul_is_small_prop in Hs.
destruct Hs as [H| Hs]; [ now subst; apply rngl_lt_irrefl in Hi1z | ].
destruct Hs as [H| Hs]; [ now subst; apply rngl_lt_irrefl in Hi2z | ].
remember (0 ≤? Im z1)%L as zi1 eqn:Hzi1.
symmetry in Hzi1.
destruct zi1. {
  apply rngl_leb_le in Hzi1.
  now apply (rngl_nlt_ge Hor) in Hzi1.
}
apply (rngl_leb_gt Hor) in Hi2z.
now rewrite Hi2z in Hs.
Qed.

Theorem c_squ_modulus : ∀ z, ‖ z ‖² = ((Re z)² + (Im z)²)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold c_modulus.
progress unfold rl_modl.
apply rngl_squ_sqrt.
apply (rngl_add_squ_nonneg Hos Hto).
Qed.

Theorem c_mul_small_Im_mul_nonneg :
  ∀ z1 z2,
  z1 ≠ 0%C
  → z2 ≠ 0%C
  → c_mul_is_small z1 z2 = true
  → (0 ≤ Im (z1 * z2))%L
  → (0 ≤ Re z2)%L
  → (0 ≤ Im z1)%L
  → (0 ≤ Re z1)%L
  → (0 ≤ Im z2)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * H1z H2z Hs12 Hzi12 Hzc2 Hzi1 Hzr1.
apply c_mul_is_small_bool_prop in Hs12.
progress unfold c_mul_is_small_prop in Hs12.
destruct Hs12 as [Hs12| Hs12]; [ easy | ].
destruct Hs12 as [Hs12| Hs12]; [ easy | ].
generalize Hzi1; intros H.
apply rngl_leb_le in H.
rewrite H in Hs12; clear H.
apply (rngl_nlt_ge_iff Hto).
intros Hzi2.
generalize Hzi2; intros H.
apply (rngl_leb_gt Hor) in H.
rewrite H in Hs12; clear H.
apply (rngl_lt_lt_squ Hop Hiq Hto) in Hs12; [ | ring | ]; cycle 1. {
  apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
  apply c_modulus_nonneg.
}
do 2 rewrite (rngl_squ_mul Hic) in Hs12.
do 2 rewrite c_squ_modulus in Hs12.
do 2 rewrite rngl_mul_add_distr_l in Hs12.
rewrite (rngl_mul_comm Hic) in Hs12.
apply (rngl_add_lt_mono_l Hos Hor) in Hs12.
cbn in Hzi12.
apply (rngl_nlt_ge Hor) in Hzi12.
apply Hzi12; clear Hzi12.
apply (rngl_lt_opp_r Hop Hor).
rewrite <- (rngl_mul_opp_r Hop).
apply (rngl_lt_squ_lt Hop Hiq Hto).
now apply (rngl_mul_nonneg_nonneg Hos Hor).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_opp_nonneg_nonpos Hop Hor).
now apply rngl_lt_le_incl.
rewrite (rngl_mul_comm Hic).
do 2 rewrite (rngl_squ_mul Hic).
now rewrite (rngl_squ_opp Hop).
Qed.

(* to be completed
Theorem c_seq_to_div_nat_is_Cauchy :
  rngl_is_archimedean T = true →
  ∀ n z, is_Cauchy_sequence c_eucl_dist (c_seq_to_div_nat z n).
Proof.
intros Har.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * ε Hε.
  rewrite H1 in Hε.
  now apply rngl_lt_irrefl in Hε.
}
intros.
destruct (c_eq_dec Heo z 0) as [Hzz| Hzz]. {
  subst z.
  exists (Nat.log2_up n).
  intros * Hp Hq.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n.
    progress unfold c_seq_to_div_nat; cbn.
    (* lemma *)
    progress unfold c_eucl_dist.
    rewrite (c_sub_diag Hos).
    now rewrite (c_modulus_0 Hop Hii Hto).
  }
  apply Nat.log2_up_le_pow2 in Hp; [ | now apply Nat.neq_0_lt_0 ].
  apply Nat.log2_up_le_pow2 in Hq; [ | now apply Nat.neq_0_lt_0 ].
  rewrite c_seq_to_div_nat_0_l; cycle 1. {
    apply Nat.div_str_pos.
    split; [ | easy ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite c_seq_to_div_nat_0_l; cycle 1. {
    apply Nat.div_str_pos.
    split; [ | easy ].
    now apply Nat.neq_0_lt_0.
  }
  progress unfold c_eucl_dist.
  rewrite (c_sub_diag Hos).
  now rewrite (c_modulus_0 Hop Hii Hto).
}
intros * ε Hε.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n.
  exists 0.
  intros * _ _.
  cbn.
  now rewrite c_eucl_dist_diag.
}
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]. {
  subst n.
  exists 0.
  intros * _ _.
  progress unfold c_seq_to_div_nat.
  do 2 rewrite Nat.div_1_r.
  do 2 rewrite <- c_pow_rngl_pow.
  do 2 rewrite c_nth_2_pow_root_pow_2_pow.
  now rewrite c_eucl_dist_diag.
}
(* see SeqAngleIsCauchy.v in TrigoWithoutPi *)
assert (Hss : ∀ i, (0 ≤ Im (c_seq_to_div_nat z n i))%L). {
  intros.
(*
  progress unfold c_seq_to_div_nat.
*)
(*
Print c_nth_2_pow_root.
*)
(*
  → (seq_angle_to_div_nat α n i ≤ π /₂^(Nat.log2 n - 1))%A.

  π /₂^(Nat.log2 n - 1), c'est
  c_nth_2_pow_root (Nat.log2 n - 1) (-1)
*)
  set (z' := mk_c (Re z / ‖z‖) (Im z / ‖z‖)).
  rename i into j.
  assert (H1 : ∀ k, (0 ≤ Im (c_nth_2_pow_root k (-1)))%L). {
    intros.
    destruct k; cbn. {
      rewrite (rngl_opp_0 Hop).
      apply (rngl_le_refl Hor).
    }
    apply rl_sqrt_sub_mod_re_div_2_nonneg.
  }
  specialize (H1 (Nat.log2 n - 1)).
  remember (c_nth_2_pow_root (Nat.log2 j - 1) (- 1)) as x.
  remember (c_seq_to_div_nat z n j) as y.
  assert (0 ≤ Im x ∧ Re y ≤ Re x)%L. {
    subst x y.
    progress unfold c_seq_to_div_nat.
    destruct n; [ easy | clear Hnz ].
    destruct n; [ easy | clear Hn1 ].
Theorem sqrt_c_seq_to_div_nat_ge_div_pow2_log2 :
  ∀ n i α,
    (Re (c_nth_2_pow_root (Nat.log2 n) (-1)) ≤
     Re √(c_seq_to_div_nat α n i))%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (Re (c_nth_2_pow_root _ _))).
  rewrite (H1 (Re √_))%L.
  apply (rngl_le_refl Hor).
}
intros.
progress unfold c_seq_to_div_nat.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn.
  rewrite rngl_signp_0, rngl_mul_1_l.
  apply (rngl_le_trans Hor _ 0).
  apply (rngl_opp_1_le_0 Hop Hto).
  apply rl_sqrt_nonneg.
  apply (rngl_div_nonneg Hop Hiv Hto).
  apply (rngl_add_nonneg_nonneg Hos Hor).
  apply c_modulus_nonneg.
  apply (rngl_0_le_1 Hos Hto).
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
assert (Hin : 2 ^ i / n ≤ 2 ^ i). {
  apply Nat.Div0.div_le_upper_bound.
  now apply Nat.le_mul_l.
}
rewrite <- c_pow_rngl_pow.
rewrite <- c_sqrt_pow; cycle 1. {
(* AngleAddLeMonoL.v *)
Theorem angle_mul_nat_not_overflow_le_l :
  ∀ m n,
  m ≤ n
  → ∀ z, c_pow_nat_nb_turns n z = 0
  → c_pow_nat_nb_turns m z = 0.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_c_0 Hc1) as H1.
  intros * Hmn * Hn.
  rewrite (H1 z).
  clear Hmn.
  induction m; [ easy | ].
  apply c_mul_nat_nb_turns_succ_l_false.
  split; [ easy | ].
  now apply c_mul_is_small_bool_prop; left.
}
intros * Hmn * Hn.
destruct (c_eq_dec Heo z 0) as [Hzz| Hzz]. {
  subst z.
  clear n Hmn Hn.
  induction m; intros; [ easy | ].
  apply c_mul_nat_nb_turns_succ_l_false.
  split; [ easy | ].
  now apply c_mul_is_small_bool_prop; left.
}
revert m Hmn Hn.
induction n; intros; [ now apply Nat.le_0_r in Hmn; subst m | ].
apply c_mul_nat_nb_turns_succ_l_false in Hn.
destruct m; [ easy | ].
apply Nat.succ_le_mono in Hmn.
apply c_mul_nat_nb_turns_succ_l_false.
split; [ now apply IHn | ].
apply (c_mul_is_small_le _ (z ^ n)); [ | | easy ]. {
  now apply (c_pow_neq_0 Hc1).
}
Search (_ ^ _ ≤ _ ^ _)%C.
Theorem c_arg_pow_le_mono_r :
  ∀ z a b,
  c_pow_nat_nb_turns b z = 0
  → a ≤ b
  → (z ^ a ≤ z ^ b)%C.
Proof.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hb Hab.
revert a Hab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  apply c_arg_le_refl.
}
destruct a. {
  clear Hab.
  progress unfold c_arg_leb.
  remember (z ^ S b)%C as x; cbn; subst x.
  rewrite (rngl_leb_refl Hor).
  rewrite (c_modulus_1 Hop Hiq Hto).
  rewrite rngl_mul_1_l, rngl_mul_1_r.
  remember (0 ≤? _)%L as ziz eqn:Hziz.
  symmetry in Hziz.
  destruct ziz; [ | easy ].
  apply rngl_leb_le.
  apply Re_bound.
}
move a after b.
apply Nat.succ_le_mono in Hab.
apply c_mul_nat_nb_turns_succ_l_false in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
cbn.
Theorem c_mul_le_mono_nonneg_l :
  ∀ z1 z2 z3,
  z3 ≠ 0%C
  → c_mul_is_small_prop z1 z3
  → (z2 ≤ z3)%C
  → (z1 * z2 ≤ z1 * z3)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
intros * H3z Hs13 Hz23.
destruct (c_eq_dec Heo z1 0) as [H1z| H1z]. {
  subst z1.
  do 2 rewrite (c_mul_0_l Hos).
  apply c_arg_le_refl.
}
destruct (c_eq_dec Heo z2 0) as [H2z| H2z]. {
  subst z2.
  rewrite (c_mul_0_r Hos).
  progress unfold c_arg_leb.
  cbn - [ "*"%C ].
  rewrite (rngl_leb_refl Hor).
  rewrite (c_modulus_0 Hop Hii Hto).
  rewrite (rngl_mul_0_r Hos), (rngl_mul_0_l Hos).
  rewrite (rngl_leb_refl Hor).
  now destruct (_ ≤? _)%L.
}
progress unfold c_arg_leb.
remember (0 ≤? Im (z1 * z2))%L as zi12 eqn:Hzi12.
symmetry in Hzi12.
destruct zi12. {
  remember (0 ≤? Im (z1 * z3))%L as zi13 eqn:Hzi13.
  symmetry in Hzi13.
  destruct zi13; [ | easy ].
  apply rngl_leb_le in Hzi12, Hzi13.
  apply rngl_leb_le.
  (* lemma *)
  progress unfold c_arg_leb in Hz23.
  remember (0 ≤? Im z2)%L as zi2 eqn:Hzi2.
  remember (0 ≤? Im z3)%L as zi3 eqn:Hzi3.
  symmetry in Hzi2, Hzi3.
  move Hz23 at bottom.
  destruct zi2; cycle 1. {
    destruct zi3; [ easy | ].
    apply (rngl_leb_gt_iff Hto) in Hzi2, Hzi3.
    apply rngl_leb_le in Hz23.
    apply c_mul_is_small_bool_prop in Hs13.
    assert (Haov12 : c_mul_is_small z1 z2 = true). {
      apply (c_mul_is_small_le _ z3); [ easy | | easy ].
      progress unfold c_arg_leb.
      apply (rngl_leb_gt Hor) in Hzi2, Hzi3.
      rewrite Hzi2, Hzi3.
      now apply rngl_leb_le.
    }
    destruct (rngl_ltb_dec (Re z3) 0)%L as [Hc3z| Hzc3]. {
      apply (rngl_ltb_lt Heo) in Hc3z.
      exfalso.
      apply Bool.not_false_iff_true in Hs13.
      apply Hs13; clear Hs13.
      now apply Im_mul_nonneg_c_mul_is_not_small.
    }
    assert (Hzi1 : (0 ≤ Im z1)%L). {
      apply (rngl_nlt_ge_iff Hto).
      intros Hzi1.
      apply (c_im_neg_neg_mul_is_not_small z1) in Hzi2; [ | easy ].
      congruence.
    }
    apply (rngl_ltb_ge_iff Hto) in Hzc3.
    apply c_mul_is_small_bool_prop in Haov12.
    destruct Haov12 as [Hs21| Hs21]; [ easy | ].
    destruct Hs21 as [Hs21| Hs21]; [ easy | ].
    generalize Hzi1; intros H.
    apply rngl_leb_le in H.
    rewrite H in Hs21; clear H.
    generalize Hzi2; intros H.
    apply (rngl_leb_gt Hor) in H.
    rewrite H in Hs21; clear H.
    destruct (rngl_leb_dec (Re z2) 0)%L as [Hr2z| Hr2z]. {
      apply rngl_leb_le in Hr2z.
      exfalso.
      destruct (rngl_ltb_dec 0 (Re z1))%L as [Hzr1| Hzr1]. {
        apply (rngl_ltb_lt Heo) in Hzr1.
        cbn in Hzi12.
        apply (rngl_nlt_ge Hor) in Hzi12.
        apply Hzi12; clear Hzi12.
        apply (rngl_add_nonpos_neg Hop Hor).
        now apply (rngl_mul_nonneg_nonpos Hop Hor).
        now apply (rngl_mul_pos_neg Hop Hiq Hor).
      }
      apply (rngl_ltb_ge_iff Hto) in Hzr1.
      cbn in Hzi12.
      apply (rngl_nle_gt Hor) in Hs21.
      apply Hs21; clear Hs21.
      apply rngl_lt_le_incl in Hzi2.
      now apply mul_Re_mod_le_mul_Re_mod.
    }
    apply (rngl_leb_gt_iff Hto) in Hr2z.
    destruct (rngl_leb_dec 0 (Re z1))%L as [Hzr1| Hzr1]. {
      apply rngl_leb_le in Hzr1.
      apply (rngl_nle_gt Hor) in Hzi3.
      now apply (c_mul_small_Im_mul_nonneg z1 z3) in Hzi13.
    }
    exfalso.
    apply (rngl_leb_gt_iff Hto) in Hzr1.
    apply (rngl_nle_gt Hor) in Hs21.
    apply Hs21; clear Hs21.
    apply (rngl_le_trans Hor _ 0). {
      apply (rngl_mul_nonpos_nonneg Hop Hor).
      now apply rngl_lt_le_incl.
      apply c_modulus_nonneg.
    }
    apply (rngl_mul_nonneg_nonneg Hos Hor).
    now apply rngl_lt_le_incl.
    apply c_modulus_nonneg.
  }
  apply rngl_leb_le in Hzi2.
  destruct zi3. {
    apply rngl_leb_le in Hzi3, Hz23.
    progress unfold c_mul_is_small_prop in Hs13.
    destruct Hs13 as [Hs13| Hs13]; [ easy | ].
    destruct Hs13 as [Hs13| Hs13]; [ easy | ].
    generalize Hzi3; intros H.
    apply rngl_leb_le in H.
    rewrite H in Hs13; clear H.
    remember (0 ≤? Im z1)%L as zi1 eqn:Hzi1.
    symmetry in Hzi1.
    destruct zi1. {
      apply rngl_leb_le in Hzi1.
      remember (is_negative_real z1) as nr1 eqn:Hnr1.
      symmetry in Hnr1.
      destruct nr1. {
        remember (is_negative_real z3) as nr3 eqn:Hnr3.
        symmetry in Hnr3.
        destruct nr3. {
          apply is_negative_real_bool_prop in Hnr1, Hnr3.
          now exfalso; apply Hs13.
        }
clear - Hnr1 Hnr3 Hto Hzi13 Hos Hor Hop Hiq Hzi3 Heo Hz23 Hic H3z Hiv H1z.
move H1z after H3z.
cbn.
generalize Hnr1; intros H.
        apply is_negative_real_bool_prop in H.
        destruct H as (H1, H2).
rewrite H2.
do 2 rewrite (rngl_mul_0_l Hos), (rngl_sub_0_r Hos).
do 2 rewrite (c_modulus_mul Hic Hop Hto).
do 2 rewrite <- rngl_mul_assoc.
apply (rngl_opp_le_compat Hop Hor).
do 2 rewrite <- (rngl_mul_opp_l Hop (Re z1)).
apply (rngl_mul_le_mono_pos_l Hop Hiq Hto).
now apply (rngl_lt_0_opp Hop Hor).
do 2 rewrite (rngl_mul_comm Hic (‖ z1 ‖)).
do 2 rewrite rngl_mul_assoc.
apply (rngl_mul_le_mono_pos_r Hop Hiq Hto).
now apply c_modulus_pos.
clear Hnr1.
        cbn in Hzi13.
        rewrite H2, (rngl_mul_0_l Hos), rngl_add_0_l in Hzi13.
        apply (rngl_nlt_ge Hor) in Hzi13.
        apply (rngl_nlt_ge_iff Hto).
        intros Hrr.
        apply Hzi13; clear Hzi13.
        apply (rngl_mul_neg_pos Hop Hiq Hor); [ easy | ].
        apply rngl_le_neq.
        split; [ easy | ].
        intros Hi3z; symmetry in Hi3z.
        apply Bool.andb_false_iff in Hnr3.
        destruct Hnr3 as [Hr3z| H]; [ | now apply (rngl_eqb_neq Heo) in H ].
        apply (rngl_ltb_ge_iff Hto) in Hr3z.
        rewrite (c_modulus_when_Im_0 z3) in Hz23; [ | easy ].
        rewrite (rngl_abs_nonneg_eq Hop Hor) in Hz23; [ | easy ].
        rewrite (rngl_mul_comm Hic) in Hz23.
        destruct (rngl_eqb_dec (Re z3) 0) as [Hrz3| Hrz3]. {
          apply (rngl_eqb_eq Heo) in Hrz3.
          now apply H3z, eq_c_eq.
        }
        apply (rngl_eqb_neq Heo) in Hrz3.
        apply (rngl_mul_le_mono_pos_r Hop Hiq Hto) in Hz23; cycle 1.
        apply rngl_le_neq.
        split; [ easy | now symmetry ].
        assert (Hi2z : Im z2 = 0%L). {
          apply (rngl_le_le_squ Hop Hto) in Hz23; cycle 1.
          apply c_modulus_nonneg.
          rewrite c_squ_modulus in Hz23.
          apply (rngl_le_add_le_sub_l Hop Hor) in Hz23.
          rewrite (rngl_sub_diag Hos) in Hz23.
          rewrite <- (rngl_squ_0 Hos) in Hz23.
          apply (rngl_squ_le_abs_le Hop Hiq Hto) in Hz23.
          rewrite (rngl_abs_0 Hop) in Hz23.
          progress unfold rngl_abs in Hz23.
          remember (Im z2 ≤? 0)%L as iz2 eqn:Hiz2.
          symmetry in Hiz2.
          destruct iz2. {
            apply rngl_leb_le in Hiz2.
            apply (rngl_le_opp_0 Hop Hor) in Hz23.
            now apply (rngl_le_antisymm Hor).
          }
          now apply rngl_leb_nle in Hiz2.
        }
        rewrite c_modulus_when_Im_0 in Hrr; [ | easy ].
        rewrite c_modulus_when_Im_0 in Hrr; [ | easy ].
        rewrite (rngl_mul_comm Hic) in Hrr.
        destruct (rngl_ltb_dec 0 (Re z2)) as [Hzr2| Hzr2]. {
          apply (rngl_ltb_lt Heo) in Hzr2.
          rewrite (rngl_abs_nonneg_eq Hop Hor) in Hrr; cycle 1.
          now apply rngl_lt_le_incl.
          apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto) in Hrr; [ | easy ].
          apply (rngl_nle_gt Hor) in Hrr.
          apply Hrr; clear Hrr.
          (* lemma *)
          apply -> (rngl_abs_le Hop Hto).
          split; [ | apply (rngl_le_refl Hor) ].
          apply (rngl_le_trans Hor _ 0); [ | easy ].
          now apply (rngl_le_opp_0 Hop Hor).
        }
        apply (rngl_ltb_ge_iff Hto) in Hzr2.
        destruct (rngl_ltb_dec (Re z2) 0) as [Hr2z| Hr2z]. {
          apply (rngl_ltb_lt Heo) in Hr2z.
          rewrite (rngl_abs_nonpos_eq Hop Hto) in Hrr; [ | easy ].
          rewrite (rngl_mul_opp_l Hop) in Hrr.
          rewrite <- (rngl_mul_opp_r Hop) in Hrr.
          apply (rngl_opp_lt_compat Hop Hor) in Hrr.
          do 2 rewrite <- (rngl_mul_opp_l Hop) in Hrr.
          apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto) in Hrr; cycle 1.
          now apply (rngl_lt_0_opp Hop Hor).
          apply (rngl_nle_gt Hor) in Hrr.
          apply Hrr; clear Hrr.
          apply (rngl_le_opp_abs_diag Hop Hto).
        }
        apply (rngl_ltb_ge_iff Hto) in Hr2z.
        apply (rngl_le_antisymm Hor) in Hr2z; [ | easy ].
        rewrite Hr2z in Hrr.
        rewrite (rngl_abs_0 Hop) in Hrr.
        do 2 rewrite (rngl_mul_0_l Hos) in Hrr.
        now apply rngl_lt_irrefl in Hrr.
...
      }
      clear Hs13.
(* pfff... chais pas... faut-il que je teste nr3 ou bien que
   je décompose Hnr1 ? *)
...
(* AngleAddLeMonoL_3.v *)
Theorem angle_add_le_mono_l_sin_lb_nonneg :
  ∀ α1 α2 α3,
  (0 ≤ rngl_sin (α1 + α2))%L
  → angle_add_overflow α1 α3 = false
  → (α2 ≤ α3)%A
  → (α1 + α2 ≤ α1 + α3)%A.
Proof.
...
  now apply angle_add_le_mono_l_sin_lb_nonneg.
... ...
apply c_mul_le_mono_nonneg_l; [ | easy ].
now apply c_mul_is_small_bool_prop.
...
rngl_mul_le_mono_nonneg_l:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → rngl_has_opp T = true
      → rngl_is_ordered T = true → ∀ a b c : T, (0 ≤ a)%L → (b ≤ c)%L → (a * b ≤ a * c)%L
Search (_ * _ ≤ _ * _)%C.
...
apply c_mul_le_mono_l.
now apply angle_add_le_mono_l.
Theorem angle_add_le_mono_l :
  ∀ α1 α2 α3,
  angle_add_overflow α1 α3 = false
  → (α2 ≤ α3)%A
  → (α1 + α2 ≤ α1 + α3)%A.
Proof.
destruct_ac.
intros * Haov13 H23.
destruct (rngl_leb_dec 0 (rngl_sin (α1 + α2))) as [Hzs12| Hzs12]. {
  apply rngl_leb_le in Hzs12.
  now apply angle_add_le_mono_l_sin_lb_nonneg.
}
apply (rngl_leb_gt_iff Hto) in Hzs12.
destruct (rngl_leb_dec 0 (rngl_sin α2)) as [Hzs2| Hzs2]. {
  apply rngl_leb_le in Hzs2.
  now apply angle_add_le_mono_l_sin_lb_neg_sin_2_nonneg.
} {
  apply (rngl_leb_gt_iff Hto) in Hzs2.
  now apply angle_add_le_mono_l_sin_lb_neg_sin_2_neg.
}
Qed.
...
Theorem c_mul_nat_nb_turns_succ_l_false :
  ∀ n z,
  c_pow_nat_nb_turns (S n) z = 0
...
apply (angle_mul_nat_div_2π_succ_l_false α b) in Hb.
destruct Hb as (H1, H2).
specialize (IHb H1 _ Hab).
now apply angle_add_le_mono_l.
... ...
now apply c_arg_pow_le_mono_r.
...
remember (0 ≤? Im z3)%L as zi3 eqn:Hzi3.
symmetry in Hzi3.
destruct zi3; [ | easy ].
  clear H32.
  remember (0 ≤? Im z1)%L as zi1 eqn:Hzi1.
  symmetry in Hzi1.
  destruct zi1. {
    intros ((H1, H2), (H3, H4)).
    clear Hzi3 Hzi1.
...
  rewrite <- angle_add_overflow_equiv2.
  progress unfold angle_add_overflow2.
  progress unfold angle_ltb.
  rewrite (H1 (rngl_sin α1)).
  rewrite (rngl_leb_refl Hor).
  rewrite (H1 (rngl_sin (α1 + α3))).
  rewrite (rngl_leb_refl Hor).
  apply (rngl_ltb_ge Hor).
  rewrite H1.
  rewrite (H1 (rngl_cos _)).
  apply (rngl_le_refl Hor).
}
prog
...
generalize H12; intros Haov.
rewrite <- angle_add_overflow_equiv2 in H12 |-*.
apply (angle_add_overflow_le _ (n * α)); [ | easy ].
now apply angle_mul_le_mono_r.
Qed.
...
(* cf seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2
   in SeqAngleIsCauchy.v *)
  apply (angle_mul_nat_not_overflow_le_l _ (2 ^ i)); [ easy | ].
  apply angle_mul_nat_div_2π_pow_div.
}
rewrite <- angle_div_2_pow_succ_r_1.
apply angle_le_pow2_log2; [ easy | | ]. {
...
rewrite <- angle_mul_nat_div_2; cycle 1. {
...
Theorem seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2 :
  ∀ n i α, (seq_angle_to_div_nat α n i /₂ ≤ π /₂^Nat.log2 n)%A.
Proof.
intros.
...
  assert
    ((Re (c_nth_2_pow_root (Nat.log2 j -1) (-1)) ≤
      Re (c_nth_2_pow_root j z ^ (2 ^ j / n)))%L). {
    _admit.
  }
  eapply (rngl_le_trans Hor).
...
  destruct (rngl_ltb_dec 1 (‖z‖)%L) as [H1z| H1z]. {
...
    assert
      (∀ i,
          (Re (c_nth_2_pow_root i z' ^ i) ≤
           Re (c_nth_2_pow_root i z ^ i))%L). {
      clear i.
      intros.
      induction i; [ apply (rngl_le_refl Hor) | ].
      cbn - [ c_nth_2_pow_root ].
      apply (rngl_le_sub_le_add_l Hop Hor).
      rewrite (rngl_add_sub_assoc Hop).
      apply (rngl_le_add_le_sub_l Hop Hor).
... ...
  assert
    ((Re (c_nth_2_pow_root (Nat.log2 n - 1) (-1)) ≤
      Re (c_nth_2_pow_root i z' ^ (2 ^ i / n)))%L). {
...
    clear Hn1.
    induction n; [ easy | ].
    destruct n.
    cbn.
...
Theorem seq_angle_to_div_nat_le_straight_div_pow2_log2_pred :
  ∀ n i α,
  n ≠ 1
  → (seq_angle_to_div_nat α n i ≤ π /₂^(Nat.log2 n - 1))%A.
Proof.
intros * Hn1.
...
Theorem seq_angle_to_div_nat_div_2_le_straight_div_pow2_log2 :
  ∀ n i α, (seq_angle_to_div_nat α n i /₂ ≤ π /₂^Nat.log2 n)%A.
Proof.
intros.
progress unfold seq_angle_to_div_nat.
...
*)

End a.
