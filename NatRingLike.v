(* ℕ is a ring-like without opposite, i.e. a semiring *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.

Instance nat_ring_like_op : ring_like_op nat :=
  {| rngl_zero := 0;
     rngl_add := Nat.add;
     rngl_mul := Nat.mul;
     rngl_opt_one := Some 1;
     rngl_opt_opp_or_subt := Some (inr Nat.sub);
     rngl_opt_inv_or_quot := Some (inr Nat.div);
     rngl_opt_is_zero_divisor := None;
     rngl_opt_eq_dec := Some Nat.eq_dec;
     rngl_opt_leb := Some Nat.leb |}.

(*
Global Existing Instance nat_ring_like_op.
*)

Theorem Nat_eq_mul_0 : ∀ n m, n * m = 0 → n = 0 ∨ m = 0.
Proof. now intros; apply Nat.eq_mul_0. Qed.

Theorem Nat_eq_mul_0' :
  ∀ a b,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
apply Nat.eq_mul_0 in Hab.
destruct Hab as [Hab| Hab]; [ now left | now right; left ].
Qed.

Theorem nat_opt_characteristic_prop :
  let ro := nat_ring_like_op in
  ∀ i, rngl_mul_nat 1 (S i) ≠ 0.
Proof. easy. Qed.

Theorem Nat_mul_div :
  let ro := nat_ring_like_op in
  ∀ a b, b ≠ 0%L → (a * b / b)%L = a.
Proof.
intros * Hbz.
now apply Nat.div_mul.
Qed.

Theorem Nat_not_le :
  ∀ a b : nat, (a <=? b) ≠ true → a ≠ b ∧ (b <=? a) = true.
Proof.
intros * Hab.
apply Bool.not_true_iff_false in Hab.
apply Nat.leb_gt in Hab.
split. {
  now intros H; subst b; apply Nat.lt_irrefl in Hab.
}
apply Nat.leb_le.
now apply Nat.lt_le_incl.
Qed.

Theorem Nat_opt_le_dec :
  ∀ a b : nat, {(a <=? b) = true} + {(a <=? b) ≠ true}.
Proof.
intros.
apply Bool.bool_dec.
Qed.

Theorem Nat_le_antisymm :
  ∀ a b : nat, (a <=? b) = true → (b <=? a) = true → a = b.
Proof.
intros * Hab Hba.
apply Nat.leb_le in Hab, Hba.
now apply Nat.le_antisymm.
Qed.

Theorem Nat_le_trans :
  ∀ a b c : nat, (a <=? b) = true → (b <=? c) = true → (a <=? c) = true.
Proof.
intros * Hab Hbc.
apply Nat.leb_le in Hab, Hbc.
apply Nat.leb_le.
now apply (Nat.le_trans _ b).
Qed.

Theorem Nat_add_le_compat :
  ∀ a b c d : nat,
  (a <=? b) = true → (c <=? d) = true → (a + c <=? b + d) = true.
Proof.
intros * Hab Hcd.
apply Nat.leb_le in Hab, Hcd.
apply Nat.leb_le.
now apply Nat.add_le_mono.
Qed.

Theorem nat_rngl_mul_nat :
  let ro := nat_ring_like_op in
  ∀ a b, rngl_mul_nat a b = a * b.
Proof.
intros.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
cbn.
rewrite Nat.mul_comm.
induction b; [ easy | cbn ].
now rewrite IHb.
Qed.

Theorem nat_archimedean :
  let ro := nat_ring_like_op in
  ∀ a b : nat, (0 < a)%L → ∃ n : nat, (b < rngl_mul_nat a n)%L.
Proof.
intros * Ha *.
exists (S b).
rewrite nat_rngl_mul_nat.
apply Nat.leb_gt in Ha; cbn in Ha.
apply Nat.leb_gt; cbn.
destruct a; [ easy | cbn ].
apply Nat.lt_succ_r.
apply Nat.le_add_r.
Qed.

Theorem Nat_mul_le_compat_nonneg :
  ∀ a b c d : nat, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L.
Proof.
intros * (Hza, Hac) (Hzb, Hbd).
apply Nat.leb_le in Hza, Hac, Hzb, Hbd.
apply Nat.leb_le.
now apply Nat.mul_le_mono_nonneg.
Qed.

Theorem Nat_mul_le_compat_nonpos :
  ∀ a b c d : nat, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L.
Proof.
intros * (Hza, Hac) (Hzb, Hbd).
apply Nat.leb_le in Hza, Hac, Hzb, Hbd.
apply Nat.le_0_r in Hac, Hbd.
now subst a b.
Qed.

Definition nat_ring_like_ord :=
  {| rngl_ord_le_dec := Nat_opt_le_dec;
     rngl_ord_le_refl := Nat.leb_refl;
     rngl_ord_le_antisymm := Nat_le_antisymm;
     rngl_ord_le_trans := Nat_le_trans;
     rngl_ord_add_le_compat := Nat_add_le_compat;
     rngl_ord_mul_le_compat_nonneg := Nat_mul_le_compat_nonneg;
     rngl_ord_mul_le_compat_nonpos := Nat_mul_le_compat_nonpos;
     rngl_ord_not_le := Nat_not_le |}.

Canonical Structure nat_ring_like_prop : ring_like_prop nat :=
  {| rngl_mul_is_comm := true;
     rngl_is_archimedean := true;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := Nat.add_comm;
     rngl_add_assoc := Nat.add_assoc;
     rngl_add_0_l := Nat.add_0_l;
     rngl_mul_assoc := Nat.mul_assoc;
     rngl_opt_mul_1_l := Nat.mul_1_l;
     rngl_mul_add_distr_l := Nat.mul_add_distr_l;
     rngl_opt_mul_comm := Nat.mul_comm;
     rngl_opt_mul_1_r := NA;
     rngl_opt_mul_add_distr_r := NA;
     rngl_opt_add_opp_diag_l := NA;
     rngl_opt_add_sub := Nat.add_sub;
     rngl_opt_sub_add_distr := Nat.sub_add_distr;
     rngl_opt_sub_0_l := Nat.sub_0_l;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := Nat_mul_div;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_integral := Nat_eq_mul_0';
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := nat_opt_characteristic_prop;
     rngl_opt_ord := nat_ring_like_ord;
     rngl_opt_archimedean := nat_archimedean |}.

(*
Global Existing Instance nat_ring_like_prop.
*)

(*
Print nat_ring_like_op.
Existing Instance nat_ring_like_op.
Compute (7 - 3)%L.
Compute (7 - 3)%nat.
Compute (15 / 3)%L.
Compute (15 / 3)%nat.
*)
