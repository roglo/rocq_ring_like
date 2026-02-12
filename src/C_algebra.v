Set Nested Proofs Allowed.

Require Import Stdlib.ZArith.ZArith.
Require Import Init.Nat.
Import List.ListNotations.

Require Import Utf8.
Require Import Core.

(* general complex whose real and imaginary parts are of type T
   that is not necessarily the real numbers *)

Class GComplex T := mk_gc {gre : T; gim : T}.

Declare Scope gc_scope.
Delimit Scope gc_scope with C.
Bind Scope gc_scope with GComplex.

Arguments mk_gc {T} gre%_L gim%_L.
Arguments gre {T} GComplex%_C.
Arguments gim {T} GComplex%_C.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

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

Definition gc_zero : GComplex T := {| gre := 0; gim := 0 |}.
Definition gc_one : GComplex T := {| gre := 1; gim := 0 |}.

Definition gc_add (ca cb : GComplex T) :=
  {| gre := gre ca + gre cb; gim := gim ca + gim cb |}.

Definition gc_mul (ca cb : GComplex T) :=
  {| gre := (gre ca * gre cb - gim ca * gim cb)%L;
     gim := (gim ca * gre cb + gre ca * gim cb)%L |}.

Definition gc_inv c :=
  let d := (gre c * gre c + gim c * gim c)%L in
  mk_gc (gre c / d) (- gim c / d)%L.

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

Notation "0" := gc_zero : gc_scope.
Notation "1" := gc_one : gc_scope.
Notation "x + y" := (gc_add x y) : gc_scope.
Notation "x * y" := (gc_mul x y) : gc_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

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
now destruct a.
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
  ∀ a : GComplex T, (1 * a)%C = a.
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
  (a * b)%C = 0%C
  → a = 0%C ∨ b = 0%C ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
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

Arguments gc_ring_like_prop_not_alg_closed {T ro rp} Hic Hop Hiv Hto.

Require Import RealLike.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Definition gc_opp (c : GComplex T) := {| gre := - gre c; gim := - gim c |}.
Definition gc_sub (ca cb : GComplex T) :=
  {| gre := gre ca - gre cb; gim := gim ca - gim cb |}.
Definition gc_div (ca cb : GComplex T) :=
  gc_mul ca (gc_inv cb).
Definition gc_squ z := (z * z)%C.
Definition gc_pow_nat (z : GComplex T) n := rngl_power z n.
Definition gc_modulus (z : GComplex T) := rl_modl (gre z) (gim z).

Definition gc_sqrt (z : GComplex T) :=
  let x := (rngl_signp (gim z) * √((gc_modulus z + gre z)/2))%L in
  let y := √((gc_modulus z - gre z)/2) in
  mk_gc x y.

End a.

Notation "- x" := (gc_opp x) : gc_scope.
Notation "x - y" := (gc_sub x y) : gc_scope.
Notation " x / y" := (gc_div x y) : gc_scope.
Notation "x +ℹ y" := (mk_gc x y) (at level 50) : gc_scope.
Notation "x ⁻¹" := (gc_inv x) : gc_scope.
Notation "z ²" := (gc_squ z) : gc_scope.
Notation "√ z" := (gc_sqrt z) : gc_scope.
Notation "‖ x ‖" := (gc_modulus x) (at level 35, x at level 30).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.

Theorem gc_modulus_0 :
  rngl_has_opp T = true →
  (rngl_is_integral_domain T || rngl_has_inv_or_pdiv T)%bool = true →
  rngl_is_totally_ordered T = true →
  (‖ 0 ‖ = 0)%L.
Proof.
intros Hop Hii Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold gc_modulus.
progress unfold rl_modl.
cbn.
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_l.
apply (rl_sqrt_0 Hop Hto Hii).
Qed.

Theorem gc_modulus_1 :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ‖ 1 ‖ = 1%L.
Proof.
intros Hop Hiq Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
progress unfold gc_modulus.
progress unfold rl_modl.
cbn.
rewrite rngl_squ_1.
rewrite (rngl_squ_0 Hos).
rewrite rngl_add_0_r.
apply (rl_sqrt_1 Hop Hiq Hto).
Qed.

Theorem gc_modulus_mul :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ z1 z2, ‖ z1 * z2 ‖ = (‖ z1 ‖ * ‖ z2 ‖)%L.
Proof.
intros Hic Hop Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold gc_modulus.
progress unfold rl_modl; cbn.
rewrite (rngl_add_comm (gim z1 * gre z2)).
rewrite <- (Brahmagupta_Fibonacci_identity Hic Hop).
apply rl_sqrt_mul. {
  apply (rngl_add_squ_nonneg Hos Hto).
} {
  apply (rngl_add_squ_nonneg Hos Hto).
}
Qed.

Theorem gc_abs_re_le_modulus :
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (rngl_abs (gre z) ≤ ‖ z ‖)%L.
Proof.
intros Hop Hiq Hto.
intros.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
progress unfold gc_modulus.
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

Theorem gre_opp : ∀ z, gre (- z) = (- gre z)%L.
Proof. easy. Qed.

Theorem gc_modulus_opp :
  rngl_has_opp T = true →
  ∀ z, (‖ - z ‖ = ‖ z ‖)%C.
Proof.
intros Hop.
intros.
progress unfold gc_modulus; cbn.
progress unfold rl_modl; cbn.
now do 2 rewrite (rngl_squ_opp Hop).
Qed.

Theorem gc_add_modulus_re :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ ‖ z ‖ + gre z)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
rewrite rngl_add_comm.
apply (rngl_le_opp_l Hop Hor).
apply (rngl_le_trans Hor _ (rngl_abs (gre z))). {
  apply (rngl_le_opp_abs_diag Hop Hto).
}
apply (gc_abs_re_le_modulus Hop Hiq Hto).
Qed.

Theorem gc_sub_modulus_re :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ ‖ z ‖ - gre z)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
apply (rngl_le_0_sub Hop Hor).
apply (rngl_le_trans Hor _ (rngl_abs (gre z))). {
  apply (rngl_le_abs_diag Hop Hor).
}
apply (gc_abs_re_le_modulus Hop Hiq Hto).
Qed.

Theorem gc_modulus_add_re_div_2_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ (‖ z ‖ + gre z) / 2)%L.
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
apply (gc_add_modulus_re Hop Hiv Hto).
Qed.

Theorem gc_modulus_sub_re_div_2_nonneg :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ z, (0 ≤ (‖ z ‖ - gre z) / 2)%L.
Proof.
intros Hop Hiv Hto.
intros.
rewrite <- (rngl_add_opp_r Hop).
rewrite <- gre_opp.
rewrite <- (gc_modulus_opp Hop).
apply (gc_modulus_add_re_div_2_nonneg Hop Hiv Hto).
Qed.

Context {Hic : rngl_mul_is_comm T = true}.
Context {Hop : rngl_has_opp T = true}.
Context {Hiv : rngl_has_inv T = true}.
Context {Hto : rngl_is_totally_ordered T = true}.

Theorem gc_inv_rngl_inv : ∀ a, gc_inv a = rngl_inv a.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold gc_inv.
progress unfold rngl_div.
rewrite Hiv.
progress unfold rngl_inv.
cbn.
progress unfold gc_opt_inv_or_pdiv.
rewrite Hic.
progress unfold gc_inv.
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

Theorem rngl_add_modl_nonneg : ∀ x y, (0 ≤ rl_modl x y + x)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rl_modl.
rewrite rngl_add_comm.
apply (rngl_le_opp_l Hop Hor).
apply (rngl_le_trans Hor _ (rngl_abs x)). {
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

Theorem rngl_squ_signp a : (rngl_signp a)² = 1%L.
Proof.
progress unfold rngl_signp.
destruct (0 ≤? a)%L.
apply rngl_squ_1.
apply (rngl_squ_opp_1 Hop).
Qed.

Theorem rngl_mul_signp_abs : ∀ a, (rngl_signp a * rngl_abs a)%L = a.
Proof.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
destruct (rngl_leb_dec 0 a) as [Hza| Hza]. {
  apply rngl_leb_le in Hza.
  rewrite rngl_signp_of_pos; [ | easy ].
  rewrite rngl_mul_1_l.
  now apply (rngl_abs_nonneg_eq Hop Hor).
} {
  apply (rngl_leb_gt_iff Hto) in Hza.
  rewrite (rngl_signp_of_neg Hor); [ | easy ].
  rewrite (rngl_mul_opp_l Hop).
  rewrite rngl_mul_1_l.
  rewrite <- (rngl_opp_involutive Hop).
  f_equal.
  apply (rngl_abs_nonpos_eq Hop Hto).
  now apply rngl_lt_le_incl.
}
Qed.

Theorem gc_squ_sqrt z : gc_squ (gc_sqrt z) = z.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  apply eq_gc_eq.
  rewrite (H1 (gre _)), (H1 (gre z)).
  rewrite (H1 (gim _)), (H1 (gim z)).
  easy.
}
destruct z as (x, y).
progress unfold gc_sqrt.
progress unfold gc_squ.
progress unfold gc_modulus.
progress unfold gc_mul.
cbn.
f_equal. {
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_mul_swap Hic (rngl_signp y)).
  rewrite fold_rngl_squ.
  rewrite rngl_squ_signp, rngl_mul_1_l.
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
  apply rngl_mul_signp_abs.
}
Qed.

Fixpoint gc_nth_2_pow_root n z :=
  match n with
  | 0 => z
  | S n' => gc_sqrt (gc_nth_2_pow_root n' z)
  end.

Definition gc_seq_to_div_nat (z : GComplex T) (n k : nat) :=
  (gc_nth_2_pow_root k z ^ (2 ^ k / n))%L.

Definition gc_eucl_dist z1 z2 := gc_modulus (z1 - z2).

Theorem gc_div_re :
  ∀ z1 z2,
  gre (z1 / z2) = ((gre z1 * gre z2 + gim z1 * gim z2) / (‖ z2 ‖)²)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold gc_div; cbn.
do 2 rewrite fold_rngl_squ.
progress unfold gc_modulus.
progress unfold rl_modl.
rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
remember ((gre z2)² + (gim z2)²)%L as m eqn:Hm.
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_mul_opp_r Hop).
rewrite (rngl_sub_opp_r Hop).
do 2 rewrite (rngl_mul_div_assoc Hiv).
rewrite <- (rngl_div_add_distr_r Hiv).
easy.
Qed.

Theorem rl_modl_squ : ∀ a b, (a² + b²)%L = (rl_modl a b)².
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold rl_modl.
symmetry.
apply rngl_squ_sqrt.
apply (rngl_add_squ_nonneg Hos Hto).
Qed.

Theorem fold_gc_modulus : ∀ z, rl_modl (gre z) (gim z) = ‖ z ‖.
Proof. easy. Qed.

Theorem gre_lt_gc_eucl_dist_lt :
  ∀ a z1 z2,
  (0 ≤ a)%L
  → z1 ≠ 0%C
  → (((‖ z1 ‖)² + (‖ z2 ‖)²) / 2 - a² / 2 < gre (z2 / z1) * (‖ z1 ‖)²)%L
  ↔ (gc_eucl_dist z1 z2 < a)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hza H1z.
  rewrite (H1 (_ - _)%L), (H1 (gre _ * _)%L).
  rewrite (H1 (gc_eucl_dist _ _)), (H1 a).
  easy.
}
intros * Hza H1z.
progress unfold gc_eucl_dist.
progress unfold gc_modulus.
progress unfold rl_modl.
symmetry.
rewrite <- (rngl_abs_nonneg_eq Hop Hor √_). 2: {
  apply rl_sqrt_nonneg.
  apply (rngl_add_squ_nonneg Hos Hto).
}
symmetry.
rewrite <- (rngl_abs_nonneg_eq Hop Hor a) at 2; [ | easy ].
rewrite fold_rl_modl.
rewrite fold_gc_modulus.
rewrite gc_div_re.
rewrite (rngl_div_mul Hiv). 2: {
  intros H.
  apply (eq_rngl_squ_0 Hos Hio) in H.
  (* lemma *)
  progress unfold gc_modulus in H.
  progress unfold rl_modl in H.
  apply (eq_rl_sqrt_0 Hos) in H. 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (eq_rngl_add_square_0 Hop Hiq Hto) in H.
  destruct z1 as (x, y).
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
  rewrite (rngl_add_add_swap (gre z1)²).
  rewrite <- rngl_add_assoc.
  rewrite <- (rngl_sub_add_distr Hos).
  do 2 rewrite <- rngl_mul_assoc.
  rewrite <- rngl_mul_add_distr_l.
  do 2 rewrite rl_modl_squ.
  do 2 rewrite fold_gc_modulus.
  apply (rngl_div_lt_mono_pos_r Hop Hiv Hto 2). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_div_sub_distr_r Hop Hiv).
  rewrite (rngl_mul_comm Hic).
  rewrite (rngl_mul_div Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  rewrite (rngl_add_comm (_ / _)).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  rewrite (rngl_mul_comm Hic (gre z1)).
  rewrite (rngl_mul_comm Hic (gim z1)).
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
  rewrite (rngl_add_add_swap (gre z1)²) in Ha.
  rewrite <- rngl_add_assoc in Ha.
  rewrite <- (rngl_sub_add_distr Hos) in Ha.
  do 2 rewrite <- rngl_mul_assoc in Ha.
  rewrite <- rngl_mul_add_distr_l in Ha.
  do 2 rewrite rl_modl_squ in Ha.
  do 2 rewrite fold_gc_modulus in Ha.
  apply (rngl_div_lt_mono_pos_r Hop Hiv Hto 2) in Ha. 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_div_sub_distr_r Hop Hiv) in Ha.
  rewrite (rngl_mul_comm Hic) in Ha.
  rewrite (rngl_mul_div Hiq) in Ha; [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Ha.
  rewrite (rngl_add_comm (_ / _)) in Ha.
  apply (rngl_lt_sub_lt_add_r Hop Hor) in Ha.
  rewrite (rngl_mul_comm Hic (gre z1)) in Ha.
  rewrite (rngl_mul_comm Hic (gim z1)) in Ha.
  easy.
}
Qed.

Theorem gc_sqrt_modulus : ∀ z, ‖ √z ‖ = √ ‖ z ‖.
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
progress unfold gc_sqrt.
progress unfold gc_modulus.
progress unfold rl_modl; cbn.
progress f_equal.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_trans Hor _ (rngl_abs (gre z))). {
    apply (rngl_le_abs_diag Hop Hor).
  }
  rewrite fold_rl_modl.
  rewrite fold_gc_modulus.
  apply (gc_abs_re_le_modulus Hop Hiq Hto).
}
rewrite fold_rl_modl.
rewrite fold_gc_modulus.
rewrite (rngl_squ_mul Hic).
rewrite rngl_squ_signp.
rewrite rngl_mul_1_l.
rewrite rngl_squ_sqrt. 2: {
  apply (rngl_div_nonneg Hop Hiv Hto). 2: {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite rngl_add_comm.
  apply (rngl_le_opp_l Hop Hor).
  apply (rngl_le_trans Hor _ (rngl_abs (gre z))). {
    rewrite <- (rngl_abs_opp Hop Hto).
    apply (rngl_le_abs_diag Hop Hor).
  }
  apply (gc_abs_re_le_modulus Hop Hiq Hto).
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

Theorem gc_modulus_nonneg : ∀ z, (0 ≤ ‖ z ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold gc_modulus.
progress unfold rl_modl.
apply rl_sqrt_nonneg.
apply (rngl_add_squ_nonneg Hos Hto).
Qed.

Theorem eq_rngl_add_squ_0 : ∀ a b, (a² + b² = 0 → a = 0 ∧ b = 0)%L.
Proof.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
apply (eq_rngl_add_square_0 Hop Hiq Hto).
Qed.

Theorem gc_pow_neq_0 :
  rngl_characteristic T ≠ 1 →
  ∀ z n, z ≠ 0%C → (z ^ n)%L ≠ 0%C.
Proof.
intros Hc1.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * Hzz.
specialize (@rngl_pow_neq_0 (GComplex T)) as H1.
specialize (H1 (gc_ring_like_op T)).
specialize (H1 (gc_ring_like_prop_not_alg_closed Hic Hop Hiv Hto)).
apply H1; [ | | easy ]. {
  progress unfold rngl_has_opp_or_psub; cbn.
  progress unfold rngl_has_opp_or_psub in Hos.
  progress unfold gc_opt_opp_or_psub.
  destruct (rngl_opt_opp_or_psub T); [ | easy ].
  now destruct s.
} {
  progress unfold rngl_has_inv in Hiv.
  progress unfold rngl_has_inv_or_pdiv; cbn.
  progress unfold gc_opt_inv_or_pdiv.
  rewrite Hic.
  destruct (rngl_opt_inv_or_pdiv T); [ | easy ].
  now destruct s.
}
Qed.

Theorem gc_add_opp_r : ∀ z1 z2, (z1 + - z2 = z1 - z2)%C.
Proof.
intros.
apply eq_gc_eq; cbn.
now do 2 rewrite (rngl_add_opp_r Hop).
Qed.

Theorem gc_sub_diag : ∀ z, (z - z = 0)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold gc_sub.
now do 2 rewrite (rngl_sub_diag Hos).
Qed.

Theorem gc_mul_0_l :
  rngl_has_opp_or_psub T = true →
  ∀ z : GComplex T, (0 * z = 0)%C.
Proof.
intros Hos *.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem gc_mul_0_r :
  rngl_has_opp_or_psub T = true →
  ∀ z : GComplex T, (z * 0 = 0)%C.
Proof.
intros Hos *.
apply eq_gc_eq; cbn.
do 2 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_0_r Hos).
rewrite rngl_add_0_l.
easy.
Qed.

Theorem gc_sqrt_1 : (√1 = 1)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  apply eq_gc_eq.
  do 2 rewrite (H1 (gre _)) ,(H1 (gim _)).
  easy.
}
progress unfold gc_sqrt; cbn.
rewrite (gc_modulus_1 Hop Hiq Hto).
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
  ∀ a b,
  (a * b ≠ 0)%L
  → rngl_signp (a * b) = (rngl_signp a * rngl_signp b)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Habz.
progress unfold rngl_signp.
remember (0 ≤? a)%L as za eqn:Hza.
remember (0 ≤? b)%L as zb eqn:Hzb.
remember (0 ≤? a * b)%L as zab eqn:Hzab.
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
  now subst a; rewrite (rngl_mul_0_l Hos) in Habz.
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
  now subst b; rewrite (rngl_mul_0_r Hos) in Habz.
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

Theorem gre_bound : ∀ z, (- ‖ z ‖ ≤ gre z ≤ ‖ z ‖)%L.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold gc_modulus.
progress unfold rl_modl.
split. {
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  rewrite <- (rngl_abs_sqrt Hop Hor). 2: {
    apply (rngl_add_squ_nonneg Hos Hto).
  }
  apply (rngl_le_trans Hor _ (rngl_abs (gre z))). {
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
  apply (rngl_le_trans Hor _ (rngl_abs (gre z))). {
    apply (rngl_le_abs_diag Hop Hor).
  }
  apply (rngl_squ_le_abs_le Hop Hiq Hto).
  rewrite rngl_squ_sqrt; [ | apply (rngl_add_squ_nonneg Hos Hto) ].
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_squ_nonneg Hos Hto).
}
Qed.

(* to be completed
Theorem gc_seq_to_div_nat_is_Cauchy :
  rngl_is_archimedean T = true →
  ∀ n a, is_Cauchy_sequence gc_eucl_dist (gc_seq_to_div_nat a n).
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
intros *.
intros ε Hε.
(*
Check gre_lt_gc_eucl_dist_lt.
...
  → (1 - a² / 2 < rngl_cos (α2 - α1))%L
  ↔ (angle_eucl_dist α1 α2 < a)%L.
...
*)
destruct (gc_eq_dec Heo a 0) as [Haz| Haz]. {
  subst a.
  exists (Nat.log2_up n).
  intros * Hp Hq.
  destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
    subst n.
    progress unfold gc_seq_to_div_nat; cbn.
    (* lemma *)
    progress unfold gc_eucl_dist.
    rewrite gc_sub_diag.
    now rewrite (gc_modulus_0 Hop Hii Hto).
  }
  apply Nat.log2_up_le_pow2 in Hp; [ | now apply Nat.neq_0_lt_0 ].
  apply Nat.log2_up_le_pow2 in Hq; [ | now apply Nat.neq_0_lt_0 ].
  progress unfold gc_seq_to_div_nat.
Theorem gc_seq_to_div_nat_0_l :
  ∀ n k, 0 < 2 ^ k / n → gc_seq_to_div_nat 0 n k = 0%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_int_dom_or_inv_pdiv Hiv) as Hii.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hkn.
  apply eq_gc_eq; cbn.
  now rewrite (H1 (gre _)), (H1 (gim _)).
}
intros * Hkn.
progress unfold gc_seq_to_div_nat.
remember (2 ^ k / n) as m eqn:Hm.
clear n Hm; rename m into n.
destruct n; [ easy | clear Hkn ].
induction k; cbn; [ apply (gc_mul_0_l Hos) | ].
cbn in IHk.
apply (gc_integral Hic Hop Hio) in IHk.
destruct IHk as [H| H]. {
  rewrite H.
  (* lemma *)
  progress unfold gc_sqrt; cbn.
  rewrite rngl_add_0_r.
  rewrite (gc_modulus_0 Hop Hii Hto).
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_div_0_l Hos Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  rewrite (rl_sqrt_0 Hop Hto Hii).
  rewrite (rngl_mul_0_r Hos).
  apply (gc_mul_0_l Hos).
}
destruct H as [H| H]. {
Theorem gc_sqrt_pow :
  ∀ n z, (gc_sqrt z ^ n)%L = gc_sqrt (z ^ n)%L.
Proof.
intros.
induction n. {
  cbn; symmetry.
  apply gc_sqrt_1.
}
cbn.
rewrite IHn.
Theorem gc_sqrt_mul : ∀ a b, (√(a * b) = √a * √b)%C.
Proof.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  apply eq_gc_eq.
  now do 2 rewrite (H1 (gre _)), (H1 (gim _)).
}
intros.
progress unfold gc_sqrt; cbn - [ gc_mul ].
progress unfold gc_mul at 6; cbn - [ gc_mul ].
progress f_equal. {
  progress unfold rngl_signp at 1.
  remember (0 ≤? gim (a * b))%L as iab eqn:Hiab.
  symmetry in Hiab.
  destruct iab. {
    apply rngl_leb_le in Hiab.
    rewrite rngl_mul_1_l.
    rewrite rngl_mul_assoc.
    rewrite (rngl_mul_mul_swap Hic (rngl_signp (gim a))).
    rewrite <- rngl_mul_assoc.
    rewrite <- rl_sqrt_mul.
    2, 3: apply (gc_modulus_add_re_div_2_nonneg Hop Hiv Hto).
    rewrite <- rl_sqrt_mul.
    2, 3: apply (gc_modulus_sub_re_div_2_nonneg Hop Hiv Hto).
    do 2 rewrite (rngl_div_mul_mul_div Hic Hiv).
    do 2 rewrite (rngl_mul_div_assoc Hiv).
    rewrite (rngl_div_div Hos Hiv).
    rewrite (rngl_div_div Hos Hiv).
    2, 3, 4, 5: apply (rngl_2_neq_0 Hos Hc1 Hto).
    rewrite fold_rngl_squ.
    rewrite (rl_sqrt_div Hop Hiv Hto _ 2²); cycle 1. {
      apply (rngl_mul_nonneg_nonneg Hos Hor).
      1, 2: apply (gc_add_modulus_re Hop Hiv Hto).
    } {
      apply (rngl_squ_pos Hos Hto Hio).
      apply (rngl_2_neq_0 Hos Hc1 Hto).
    }
    rewrite (rl_sqrt_div Hop Hiv Hto _ 2²); cycle 1. {
      apply (rngl_mul_nonneg_nonneg Hos Hor).
      1, 2: apply (gc_sub_modulus_re Hop Hiv Hto).
    } {
      apply (rngl_squ_pos Hos Hto Hio).
      apply (rngl_2_neq_0 Hos Hc1 Hto).
    }
    rewrite (rl_sqrt_squ Hop Hto).
    rewrite (rngl_abs_nonneg_eq Hop Hor); [ | apply (rngl_0_le_2 Hos Hto) ].
    rewrite (rngl_mul_div_assoc Hiv).
    rewrite <- (rngl_div_sub_distr_r Hop Hiv).
    rewrite (gc_modulus_mul Hic Hop Hto).
cbn in Hiab.
rewrite <- (rngl_mul_signp_abs (gim a)) in Hiab.
rewrite <- (rngl_mul_signp_abs (gim b)) in Hiab.
    enough (H : ‖ a ‖ = 1%L ∧ ‖ b ‖ = 1%L).
    destruct H as (Ha, Hb).
    rewrite Ha, Hb.
    rewrite rngl_mul_1_l.
    cbn.
rewrite <- (rngl_mul_signp_abs (gim a)) at 1.
rewrite <- (rngl_mul_signp_abs (gim b)) at 1.
    rewrite (rngl_mul_mul_swap Hic (rngl_signp (gim a))).
    rewrite rngl_mul_assoc.
    remember (rngl_signp (gim a) * rngl_signp (gim b))%L as sab eqn:Hsab.
    symmetry in Hsab.
    destruct (rngl_eqb_dec sab 1) as [Hs1| Hs1]. {
      apply (rngl_eqb_eq Heo) in Hs1; move Hs1 at top; subst sab.
      do 2 rewrite rngl_mul_1_l.
      rewrite (rngl_add_sub_assoc Hop).
      apply (rngl_mul_move_r Hiq); [ apply (rngl_2_neq_0 Hos Hc1 Hto) | ].
      symmetry.
      apply (rngl_add_sub_eq_l Hos).
      rewrite <- (rngl_abs_nonneg_eq Hop Hor (_ + _)). 2: {
        apply (rngl_le_0_add Hos Hor). {
          apply rl_sqrt_nonneg.
          apply (rngl_mul_nonneg_nonneg Hos Hor). {
            apply (rngl_le_0_sub Hop Hor).
            rewrite <- Ha.
            apply gre_bound.
          } {
            apply (rngl_le_0_sub Hop Hor).
            rewrite <- Hb.
            apply gre_bound.
          }
        }
...
    destruct (rngl_eqb_dec (gim a * gim b)%L 0) as [Habz| Habz]. {
      apply (rngl_eqb_eq Heo) in Habz.
cbn.
progress unfold gc_modulus; cbn.
progress unfold rl_modl.
Check Brahmagupta_Fibonacci_identity.
rewrite (rngl_add_comm (gim a * gre b)).
rewrite <- (Brahmagupta_Fibonacci_identity Hic Hop).
Theorem glop :
  ∀ a b,
  gc_modulus (a * b) =
  √ (((gre a)² + (gim a)²) * ((gre b)² + (gim b)²))%L.
Proof.
intros.
rewrite rl_sqrt_mul.
do 2 rewrite fold_rl_modl.
do 2 rewrite fold_gc_modulus.
Search (‖ (_ * _) ‖)%L.
About gc_modulus_mul.
...
progress unfold gc_modulus; cbn.
progress unfold rl_modl.
rewrite (rngl_add_comm (gim a * gre b)).
rewrite (Brahmagupta_Fibonacci_identity Hic Hop).
easy.
...
progress unfold rl_modl.
rewrite <- (Brahmagupta_Fibonacci_identity Hic Hop).
...
    rewrite <- rngl_signp_mul. 2: {
      cbn in Hiab.
...
Search (gre (_ * _)).
Search (gim (_ * _)).
... ...
Search (√ (_ * _))%C.
Search (√ (_ * _))%L.
rewrite gc_sqrt_mul.
...
  rewrite H.
  (* lemma *)
  progress unfold gc_sqrt; cbn.
  rewrite rngl_add_0_r.
  rewrite gc_modulus_0.
  rewrite (rngl_sub_diag Hos).
  rewrite (rngl_div_0_l Hos Hiq); [ | apply (rngl_2_neq_0 Hos Hc1 Hto) ].
  rewrite (rl_sqrt_0 Hop Hto Hii).
  rewrite (rngl_mul_0_r Hos).
  apply (gc_mul_0_l Hos).
...
enough (H :
  ∃ N, ∀ p q,
  N ≤ p
  → N ≤ q
  → (1 - ε² / 2 <
      gre (gc_seq_to_div_nat a n p / gc_seq_to_div_nat a n q))%L). {
  destruct H as (N, HN).
  exists N.
  intros p q Hp Hq.
(*
  apply rngl_lt_le_incl in Hε.
*)
  apply gre_lt_gc_eucl_dist_lt; [ now apply rngl_lt_le_incl | | ]. {
    progress unfold gc_seq_to_div_nat.
    apply (gc_pow_neq_0 Hc1).
    intros H.
Print gc_nth_2_pow_root.
...
    induction p; cbn in H. 2: {
      subst a.
...
specialize (@rngl_integral (GComplex T)) as H1.
specialize (H1 (gc_ring_like_op T)).
specialize (H1 (gc_ring_like_prop_not_alg_closed Hic Hop Hiv Hto)).
apply H1 in H; [ now destruct H | | ]. {
  cbn.
  progress unfold rngl_has_opp_or_psub; cbn.
  progress unfold rngl_has_opp_or_psub in Hos.
  progress unfold gc_opt_opp_or_psub.
  destruct (rngl_opt_opp_or_psub T); [ | easy ].
  now destruct s.
} {
  cbn.
  apply Bool.andb_true_iff.
  split. {
...
  induction n; cbn.
  rewrite rngl_pow_0_l.
specialize (H1 gc_ring_like_prop).
rngl_eq_mul_0_l:
  ∀ {T : Type} {ro : ring_like_op T},
    ring_like_prop T
    → rngl_has_opp_or_psub T = true
      → rngl_has_inv_or_pdiv T = true → ∀ a b : T, (a * b)%L = 0%L → b ≠ 0%L → a = 0%L
injection H; clear H; intros H1 H2.
...
apply glop.
...
Print gc_nth_2_pow_root.
Inspect 1.
Print rl_sqrt.
Theorem gc_nth_root_2_pow_root_modulus :
  ∀ n z, ‖ gc_nth_2_pow_root n z ‖ = rl_nth_root (2 ^ n) (‖ z ‖).
Proof.
intros.
induction n. {
  cbn; symmetry.
  rewrite <- (rl_nth_root_pow 1); [ symmetry; apply rngl_pow_1_r | ].
  apply gc_modulus_nonneg.
}
rewrite Nat.pow_succ_r'.
Search (rl_nth_root).
Theorem rl_nth_root_mul_l :
  ∀ m n a, rl_nth_root (m * n) a = rl_nth_root m (rl_nth_root n a).
Proof.
intros.
Search rl_nth_root.
Print rl_nth_root.
Print real_like_prop.
(* peut-être manque-t-il rl_nth_root_mul_l comme axiome ?
   alors il faudrait renommer rl_nth_root_mul : rl_nth_root_mul_r *)
...
  rewrite rl_nth_root_mul_l.
Print rl_sqrt.
  rewrite fold_rl_sqrt.
...
rewrite gc_sqrt_modulus.
Search rl_nth_root.
rewrite rl_nth_root_
rewrite IHn.
...
Print gc_nth_2_pow_root.
Print gc_sqrt.
Inspect 1.
...
rewrite rl_sqrt_mul.

remember (‖ z ‖ + gre z)%L as xx.
rewrite rngl_squ_sqrt.
rewrite rl_sqrt_squ.
...
Arguments gc_modulus {T}%type_scope {ro rp rl} z%gc_scope

rewrite fold_gc_modulus.
remember (rl_modl (gre z) (gim z)
progress f_equal.
...
  apply (HN _ _ Hq Hp).
}
...
*)

End a.
