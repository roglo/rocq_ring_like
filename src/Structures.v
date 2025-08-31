(** * Structures

Definitions of structures of the ring-like library.

There are three structures:
- ring_like_op : holds constants and functions
- ring_like_ord : holds properties of ordered rings-likes
- ring_like_prop : holds properties of rings-likes

See the module [[RingLike.Core]] for the general description
of the ring-like library and some informations about these
structures.

In general, it is not necessary to import the present module. The normal
usage is to do:
<<
    Require Import RingLike.Core.
>>
which imports the present module and some other ones.
 *)

From Stdlib Require Import Utf8 Arith.

Class ring_like_op T :=
  { rngl_zero : T;
    rngl_add : T → T → T;
    rngl_mul : T → T → T;
    rngl_opt_one : option T;
    rngl_opt_opp_or_subt : option (sum (T → T) (T → T → T));
    rngl_opt_inv_or_quot : option (sum (T → T) (T → T → T));
    rngl_opt_is_zero_divisor : option (T → Prop);
    rngl_opt_eq_dec : option (∀ a b : T, {a = b} + {a ≠ b});
    rngl_opt_leb : option (T → T → bool) }.

Arguments rngl_opt_one T {ring_like_op}.
Arguments rngl_opt_opp_or_subt T {ring_like_op}.
Arguments rngl_opt_inv_or_quot T {ring_like_op}.
Arguments rngl_opt_is_zero_divisor T {ring_like_op}.
Arguments rngl_opt_eq_dec T {ring_like_op}.

Declare Scope ring_like_scope.
Delimit Scope ring_like_scope with L.

Notation "'∃ₜ' x .. y , P" := (sig (fun x => .. (sig (fun y => P)) ..))
  (at level 200, x binder, right associativity) : type_scope.

Definition bool_of_option {T} (x : option T) :=
  match x with
  | Some _ => true
  | None => false
  end.

Definition rngl_one {T} {ro : ring_like_op T} :=
  match rngl_opt_one T with
  | Some a => a
  | None => rngl_zero
  end.

Definition rngl_has_1 T {ro : ring_like_op T} :=
  bool_of_option (rngl_opt_one T).

Definition rngl_has_opp_or_subt T {R : ring_like_op T} :=
  bool_of_option (rngl_opt_opp_or_subt T).

Definition rngl_has_inv_or_quot T {R : ring_like_op T} :=
  bool_of_option (rngl_opt_inv_or_quot T).

Definition rngl_is_ordered T {R : ring_like_op T} :=
  bool_of_option rngl_opt_leb.

Definition rngl_has_eq_dec T {R : ring_like_op T} :=
  bool_of_option (rngl_opt_eq_dec T).

Definition rngl_has_inv_and_1_or_quot T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot T with
  | Some (inl _) => rngl_has_1 T
  | Some (inr _) => true
  | None => false
  end.

Definition rngl_has_opp T {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt T with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_subt T {R : ring_like_op T} :=
  match rngl_opt_opp_or_subt T with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_has_inv T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot T with
  | Some (inl _) => true
  | _ => false
  end.

Definition rngl_has_quot T {R : ring_like_op T} :=
  match rngl_opt_inv_or_quot T with
  | Some (inr _) => true
  | _ => false
  end.

Definition rngl_is_integral_domain T {ro : ring_like_op T} :=
  match rngl_opt_is_zero_divisor T with
  | Some _ => false
  | None => true
  end.

Definition rngl_is_zero_divisor {T} {ro : ring_like_op T} a :=
  match rngl_opt_is_zero_divisor T with
  | Some f => f a
  | None => False
  end.

Definition rngl_opp {T} {ro : ring_like_op T} a :=
  match rngl_opt_opp_or_subt T with
  | Some (inl rngl_opp) => rngl_opp a
  | _ => rngl_zero
  end.

Definition rngl_subt {T} {ro : ring_like_op T} a b :=
  match rngl_opt_opp_or_subt T with
  | Some (inr rngl_subt) => rngl_subt a b
  | _ => rngl_zero
  end.

Definition rngl_inv {T} {ro : ring_like_op T} a :=
  match rngl_opt_inv_or_quot T with
  | Some (inl rngl_inv) => rngl_inv a
  | _ => rngl_zero
  end.

Definition rngl_quot {T} {ro : ring_like_op T} a b :=
  match rngl_opt_inv_or_quot T with
  | Some (inr rngl_quot) => rngl_quot a b
  | _ => rngl_zero
  end.

Definition rngl_sub {T} {ro : ring_like_op T} a b :=
  if rngl_has_opp T then rngl_add a (rngl_opp b)
  else if rngl_has_subt T then rngl_subt a b
  else rngl_zero.

Definition rngl_div {T} {ro : ring_like_op T} a b :=
  if rngl_has_inv T then rngl_mul a (rngl_inv b)
  else if rngl_has_quot T then rngl_quot a b
  else rngl_zero.

Definition rngl_le {T} {ro : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => rngl_leb a b = true
  | None => False
  end.

Definition rngl_lt {T} {ro : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => rngl_leb b a = false
  | None => False
  end.

Definition rngl_eval_polyn {T} {ro : ring_like_op T} l (x : T) :=
  List.fold_right (λ a acc, rngl_add (rngl_mul acc x) a) rngl_zero l.

Definition mul_nat {T} (zero : T) (add : T → T → T) a n :=
  List.fold_right add zero (List.repeat a n).

Definition rngl_mul_nat {T} {ro : ring_like_op T} :=
  mul_nat rngl_zero rngl_add.

Definition rngl_squ {T} {ro : ring_like_op T} a := rngl_mul a a.

Fixpoint rngl_power {T} {ro : ring_like_op T} a n :=
  match n with
  | O => rngl_one
  | S m => rngl_mul a (rngl_power a m)
  end.

Definition rngl_of_nat {T} {ro : ring_like_op T} a := rngl_mul_nat rngl_one a.

Definition rngl_eqb {T} {ro : ring_like_op T} a b :=
  match rngl_opt_eq_dec T with
  | Some rngl_eq_dec =>
      match rngl_eq_dec a b with left _ => true | right _ => false end
  | None => false
  end.

Definition rngl_leb {T} {ro : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => rngl_leb a b
  | None => false
  end.

Definition rngl_ltb {T} {ro : ring_like_op T} a b :=
  match rngl_opt_leb with
  | Some rngl_leb => negb (rngl_leb b a)
  | None => false
  end.

Arguments rngl_add {T ro} (a b)%_L : rename.
Arguments rngl_sub {T ro} (a b)%_L.
Arguments rngl_mul {T ro} (a b)%_L : rename.
Arguments rngl_div {T ro} (a b)%_L.
Arguments rngl_opp {T ro} a%_L.
Arguments rngl_inv {T ro} a%_L.
Arguments rngl_squ {T ro} a%_L.
Arguments rngl_power {T ro} a%_L n%_nat.
Arguments rngl_le {T ro} (a b)%_L.
Arguments rngl_lt {T ro} (a b)%_L.
Arguments rngl_eqb {T ro} (a b)%_L.
Arguments rngl_leb {T ro} (a b)%_L.
Arguments rngl_ltb {T ro} (a b)%_L.

Arguments rngl_subt {T ro} (a b)%_L.
Arguments rngl_quot {T ro} (a b)%_L.

Notation "0" := rngl_zero : ring_like_scope.
Notation "1" := rngl_one : ring_like_scope.
Notation "2" := (rngl_add 1 1) : ring_like_scope.
Notation "3" := (rngl_add 2 1) : ring_like_scope.
Notation "4" := (rngl_add 3 1) : ring_like_scope.
Notation "a + b" := (rngl_add a b) : ring_like_scope.
Notation "a - b" := (rngl_sub a b) : ring_like_scope.
Notation "a * b" := (rngl_mul a b) : ring_like_scope.
Notation "a / b" := (rngl_div a b) : ring_like_scope.
Notation "- a" := (rngl_opp a) : ring_like_scope.
Notation "- 1" := (rngl_opp rngl_one) : ring_like_scope.
Notation "- 2" := (rngl_opp (rngl_add rngl_one rngl_one)) : ring_like_scope.
Notation "a '⁻¹'" := (rngl_inv a) (at level 1, format "a ⁻¹").
Notation "a '²'" := (rngl_squ a) (at level 1, format "a ²").
Notation "a ^ b" := (rngl_power a b) : ring_like_scope.

Notation "a ≤ b" := (rngl_le a b) : ring_like_scope.
Notation "a < b" := (rngl_lt a b) : ring_like_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a < b < c" := (a < b ∧ b < c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c)%L (at level 70, b at next level) :
  ring_like_scope.
Notation "a ≤ b ≤ c ≤ d" :=
  (a ≤ b ∧ b ≤ c ∧ c ≤ d)%L (at level 70, b at next level, c at next level) :
  ring_like_scope.
Notation "a ≤ b < c ≤ d" :=
  (a ≤ b ∧ b < c ∧ c ≤ d)%L (at level 70, b at next level, c at next level) :
  ring_like_scope.

Notation "a =? b" := (rngl_eqb a b) (at level 70) : ring_like_scope.
Notation "a ≠? b" := (negb (rngl_eqb a b)) (at level 70) : ring_like_scope.
Notation "a ≤? b" := (rngl_leb a b) (at level 70) : ring_like_scope.
Notation "a <? b" := (rngl_ltb a b) (at level 70) : ring_like_scope.

Notation "l .[ i ]" := (List.nth i l 0%L) (at level 1, format "l .[ i ]").

Inductive not_applicable := NA.

Class ring_like_ord T {ro : ring_like_op T} :=
  { rngl_ord_le_dec : ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L;
    rngl_ord_le_refl : ∀ a, (a ≤ a)%L;
    rngl_ord_le_antisymm : ∀ a b, (a ≤ b → b ≤ a → a = b)%L;
    rngl_ord_le_trans : ∀ a b c, (a ≤ b → b ≤ c → a ≤ c)%L;
    rngl_ord_add_le_mono_l :
      if rngl_has_opp_or_subt T then ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%L
      else not_applicable;
    rngl_ord_mul_le_compat_nonneg :
      if (rngl_has_1 T && rngl_has_inv_or_quot T)%bool then
        ∀ a b c d, (0 ≤ a ≤ c)%L → (0 ≤ b ≤ d)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_ord_mul_le_compat_nonpos :
      if (rngl_has_1 T && rngl_has_inv_or_quot T)%bool then
        ∀ a b c d, (c ≤ a ≤ 0)%L → (d ≤ b ≤ 0)%L → (a * b ≤ c * d)%L
      else not_applicable;
    rngl_ord_not_le : ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L }.

Class ring_like_prop T {ro : ring_like_op T} :=
  { rngl_mul_is_comm : bool;
    rngl_is_archimedean : bool;
    rngl_is_alg_closed : bool;
    rngl_characteristic : nat;
    rngl_add_comm : ∀ a b : T, (a + b = b + a)%L;
    rngl_add_assoc : ∀ a b c : T, (a + (b + c) = (a + b) + c)%L;
    rngl_add_0_l : ∀ a : T, (0 + a)%L = a;
    rngl_mul_assoc : ∀ a b c : T, (a * (b * c) = (a * b) * c)%L;
    (* when has 1 *)
    rngl_opt_mul_1_l :
      if rngl_has_1 T then ∀ a : T, (rngl_one * a)%L = a else not_applicable;
    rngl_mul_add_distr_l : ∀ a b c : T, (a * (b + c) = a * b + a * c)%L;
    (* when multiplication is commutative *)
    rngl_opt_mul_comm :
      if rngl_mul_is_comm then ∀ a b, (a * b = b * a)%L else not_applicable;
    (* when multiplication is not commutative *)
    rngl_opt_mul_1_r :
      if rngl_mul_is_comm then not_applicable
      else if rngl_has_1 T then ∀ a, (a * 1 = a)%L
      else not_applicable;
    rngl_opt_mul_add_distr_r :
      if rngl_mul_is_comm then not_applicable else
       ∀ a b c, ((a + b) * c = a * c + b * c)%L;
    (* when has opposite *)
    rngl_opt_add_opp_diag_l :
      if rngl_has_opp T then ∀ a : T, (- a + a = 0)%L else not_applicable;
    (* when has subtraction (subt) *)
    rngl_opt_add_sub :
      if rngl_has_subt T then ∀ a b, (a + b - b)%L = a
      else not_applicable;
    rngl_opt_sub_add_distr :
      if rngl_has_subt T then ∀ a b c, (a - (b + c) = a - b - c)%L
      else not_applicable;
    rngl_opt_sub_0_l :
      if rngl_has_subt T then ∀ a, (0 - a = 0)%L
      else not_applicable;
    (* when has inverse *)
    rngl_opt_mul_inv_diag_l :
      if (rngl_has_inv T && rngl_has_1 T)%bool then
        ∀ a : T, a ≠ 0%L → (a⁻¹ * a = 1)%L
      else not_applicable;
    rngl_opt_mul_inv_diag_r :
      if (rngl_has_inv T && rngl_has_1 T && negb rngl_mul_is_comm)%bool then
        ∀ a : T, a ≠ 0%L → (a * a⁻¹ = 1)%L
      else not_applicable;
    (* when has division (quot) *)
    rngl_opt_mul_div :
      if rngl_has_quot T then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
      else not_applicable;
    rngl_opt_mul_quot_r :
      (* actually there is no algebra having at the same time
         - no inverse (has_inv = false)
         - a primitive division (has_quot = true)
         - a non commutative multiplication (mul_comm = false);
         this axiom is therefore useless *)
      if (rngl_has_quot T && negb rngl_mul_is_comm)%bool then
        ∀ a b, b ≠ 0%L → (b * a / b)%L = a
      else not_applicable;
    (* zero divisors *)
    rngl_opt_integral :
      ∀ a b, (a * b = 0)%L
      → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b;
    (* when algebraically closed *)
    rngl_opt_alg_closed :
      if rngl_is_alg_closed then
        ∀ l : list T, 1 < length l → List.last l 0%L ≠ 0%L →
        ∃ x, rngl_eval_polyn l x = 0%L
      else not_applicable;
    (* characteristic *)
    rngl_opt_characteristic_prop :
      if rngl_has_1 T then
        if Nat.eqb (rngl_characteristic) 0 then
          ∀ i, rngl_of_nat (S i) ≠ 0%L
        else
          (∀ i, 0 < i < rngl_characteristic → rngl_of_nat i ≠ 0%L) ∧
          rngl_of_nat rngl_characteristic = 0%L
      else
        not_applicable;
    (* when ordered *)
    rngl_opt_ord :
      if rngl_is_ordered T then ring_like_ord T
      else not_applicable;
    (* archimedean *)
    rngl_opt_archimedean :
      if (rngl_is_archimedean && rngl_is_ordered T)%bool then
        ∀ a b, (0 < a)%L → ∃ₜ n, (b < rngl_mul_nat a n)%L
      else not_applicable }.

Definition rngl_abs {T} {ro : ring_like_op T} a :=
  if (a ≤? 0)%L then (- a)%L else a.
Definition rngl_min {T} {ro : ring_like_op T} (a b : T) :=
  if (a ≤? b)%L then a else b.
Definition rngl_max {T} {ro : ring_like_op T} (a b : T) :=
  if (a ≤? b)%L then b else a.

Definition rngl_min3 {T} {ro : ring_like_op T} a b c :=
  rngl_min (rngl_min a b) c.

Definition rngl_has_eq_dec_or_order T {ro : ring_like_op T} :=
  (rngl_has_eq_dec T || rngl_is_ordered T)%bool.

Arguments rngl_mul_is_comm T {ro ring_like_prop}.
Arguments rngl_characteristic T {ro ring_like_prop}.
Arguments rngl_is_archimedean T {ro ring_like_prop}.
Arguments rngl_abs {T ro} a%_L.

Notation "∣ x ∣" := (rngl_abs x) (at level 35, x at level 30).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_has_opp_or_subt_iff :
  rngl_has_opp_or_subt T = true
  ↔ rngl_has_opp T = true ∨ rngl_has_subt T = true.
Proof.
unfold rngl_has_opp_or_subt, bool_of_option.
unfold rngl_has_opp, rngl_has_subt.
destruct rngl_opt_opp_or_subt as [opp_subt| ]. 2: {
  split; [ now left | ].
  now intros [|].
}
split; [ intros _ | easy ].
now destruct opp_subt; [ left | right ].
Qed.

Theorem rngl_has_inv_or_quot_iff :
  rngl_has_inv_or_quot T = true
  ↔ rngl_has_inv T = true ∨ rngl_has_quot T = true.
Proof.
unfold rngl_has_inv_or_quot, bool_of_option.
unfold rngl_has_inv, rngl_has_quot.
destruct rngl_opt_inv_or_quot as [inv_quot| ]. 2: {
  split; [ now left | ].
  now intros [|].
}
split; [ intros _ | easy ].
now destruct inv_quot; [ left | right ].
Qed.

Theorem rngl_has_inv_and_1_or_quot_iff :
  rngl_has_inv_and_1_or_quot T = true
  ↔ rngl_has_inv T = true ∧ rngl_has_1 T = true ∨ rngl_has_quot T = true.
Proof.
progress unfold rngl_has_inv_and_1_or_quot, bool_of_option.
progress unfold rngl_has_inv, rngl_has_quot.
destruct rngl_opt_inv_or_quot as [inv_quot| ]. 2: {
  split; [ now left | ].
  now intros [|].
}
split; [ | now intros H; destruct H, inv_quot ].
now destruct inv_quot; [ left | right ].
Qed.

Theorem rngl_has_opp_has_opp_or_subt :
  rngl_has_opp T = true → rngl_has_opp_or_subt T = true.
Proof.
intros Hop.
now apply rngl_has_opp_or_subt_iff; left.
Qed.

Theorem rngl_has_inv_has_inv_or_quot :
  rngl_has_inv T = true → rngl_has_inv_or_quot T = true.
Proof.
intros * Hop.
now apply rngl_has_inv_or_quot_iff; left.
Qed.

Theorem rngl_has_inv_and_1_has_inv_and_1_or_quot :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  rngl_has_inv_and_1_or_quot T = true.
Proof.
intros * Hon Hiv.
apply rngl_has_inv_and_1_or_quot_iff.
now rewrite Hiv, Hon; left.
Qed.

Theorem rngl_int_dom_or_inv_1_quo_and_eq_dec :
  rngl_has_inv_and_1_or_quot T = true →
  rngl_has_eq_dec T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T && rngl_has_eq_dec T)%bool = true.
Proof.
intros * Hi1 Hed.
apply Bool.orb_true_iff; right.
now rewrite Hi1, Hed.
Qed.

Theorem rngl_int_dom_or_inv_1_quo :
  rngl_has_inv T = true →
  rngl_has_1 T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_and_1_or_quot T)%bool = true.
Proof.
intros * Hiv Hon.
apply Bool.orb_true_iff; right.
apply rngl_has_inv_and_1_or_quot_iff; left.
now rewrite Hiv, Hon.
Qed.

Theorem rngl_has_1_has_inv_or_quot_has_inv_and_1_or_quot :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  rngl_has_inv_and_1_or_quot T = true.
Proof.
intros Hon Hiq.
apply rngl_has_inv_and_1_or_quot_iff.
rewrite Hon.
apply rngl_has_inv_or_quot_iff in Hiq.
destruct Hiq as [H| H]; rewrite H; [ now left | now right ].
Qed.

Theorem rngl_int_dom_or_inv_1_or_quot_r :
  rngl_has_1 T = true →
  rngl_has_inv_or_quot T = true →
  (rngl_is_integral_domain T || rngl_has_inv_and_1_or_quot T)%bool = true.
Proof.
intros Hon Hiq.
apply Bool.orb_true_iff; right.
now apply rngl_has_1_has_inv_or_quot_has_inv_and_1_or_quot.
Qed.

Theorem rngl_has_subt_has_no_opp :
  rngl_has_subt T = true
  → rngl_has_opp T = false.
Proof.
intros * Hsu.
unfold rngl_has_subt in Hsu.
unfold rngl_has_opp.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_opp_has_no_subt :
  rngl_has_opp T = true
  → rngl_has_subt T = false.
Proof.
intros * Hop.
unfold rngl_has_opp in Hop.
unfold rngl_has_subt.
destruct rngl_opt_opp_or_subt as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_quot_has_no_inv :
  rngl_has_quot T = true
  → rngl_has_inv T = false.
Proof.
intros * Hqu.
progress unfold rngl_has_quot in Hqu.
progress unfold rngl_has_inv.
destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem rngl_has_inv_has_no_quot :
  rngl_has_inv T = true
  → rngl_has_quot T = false.
Proof.
intros * Hiv.
progress unfold rngl_has_inv in Hiv.
progress unfold rngl_has_quot.
destruct rngl_opt_inv_or_quot as [iq| ]; [ | easy ].
now destruct iq.
Qed.

Theorem rngl_has_eq_dec_or_is_ordered_l :
  rngl_has_eq_dec T = true
  → rngl_has_eq_dec_or_order T = true.
Proof.
intros Hor.
progress unfold rngl_has_eq_dec_or_order.
rewrite Hor.
apply Bool.orb_true_l.
Qed.

Theorem rngl_has_eq_dec_or_is_ordered_r :
  rngl_is_ordered T = true
  → rngl_has_eq_dec_or_order T = true.
Proof.
intros Hor.
progress unfold rngl_has_eq_dec_or_order.
rewrite Hor.
apply Bool.orb_true_r.
Qed.

Theorem rngl_integral_or_inv_1_quot_eq_dec_order :
  rngl_has_1 T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true.
Proof.
intros Hon Hiv Hor.
apply Bool.orb_true_iff; right.
rewrite (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv); cbn.
apply (rngl_has_eq_dec_or_is_ordered_r Hor).
Qed.

Theorem fold_rngl_squ : ∀ a : T, (a * a)%L = rngl_squ a.
Proof. easy. Qed.

Theorem rngl_eqb_eq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a =? b)%L = true ↔ a = b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_eqb_neq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a =? b)%L = false ↔ a ≠ b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_neqb_neq :
  rngl_has_eq_dec T = true →
  ∀ a b : T, (a ≠? b)%L = true ↔ a ≠ b.
Proof.
intros Hed *.
progress unfold rngl_has_eq_dec in Hed.
progress unfold rngl_eqb.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
clear Hed.
now destruct (rngl_eq_dec a b).
Qed.

Theorem rngl_eqb_refl :
  rngl_has_eq_dec T = true →
  ∀ a, (a =? a)%L = true.
Proof.
intros Heqb *.
now apply (rngl_eqb_eq Heqb).
Qed.

Theorem rngl_eqb_sym :
  rngl_has_eq_dec T = true →
  ∀ a b, ((a =? b) = (b =? a))%L.
Proof.
intros Hed *.
remember (a =? b)%L as ab eqn:Hab.
remember (b =? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab. {
  destruct ba; [ easy | ].
  apply (rngl_eqb_eq Hed) in Hab.
  apply (rngl_eqb_neq Hed) in Hba.
  now symmetry in Hab.
} {
  destruct ba; [ | easy ].
  apply (rngl_eqb_neq Hed) in Hab.
  apply (rngl_eqb_eq Hed) in Hba.
  now symmetry in Hba.
}
Qed.

End a.

Arguments rngl_add_assoc {T ro rp} (a b c)%_L : rename.
Arguments rngl_add_comm {T ro ring_like_prop} (a b)%_L.
