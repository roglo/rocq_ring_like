(** Upper bound property and
    intermediate values theorem *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Require Import Init.Nat.

Require Import Utf8 Core Misc.

Class excl_midd := { em_prop : ∀ P, P + notT P }.

Definition forall_or_exists_not {T} (P : T → Prop) :=
  {∀ x, P x} + {∃ x, ¬ P x}.

Theorem rl_forall_or_exists_not {em : excl_midd} {T} :
  ∀ (P : T → Prop), forall_or_exists_not P.
Proof.
intros.
specialize (em_prop (∃ x, ¬ P x)) as H2.
destruct H2 as [H2| H2]; [ now right | left ].
intros.
specialize (em_prop (P x)) as H3.
destruct H3 as [H3| H3]; [ easy | ].
exfalso; apply H2.
now exists x.
Qed.

Theorem rl_not_forall_exists {em : excl_midd} {T} :
  ∀ (P : T → Prop), ¬ (∀ x, ¬ P x) → ∃ x, P x.
Proof.
intros * Ha.
specialize (em_prop (∃ x, P x)) as H2.
destruct H2 as [H2| H2]; [ easy | ].
exfalso; apply Ha; clear Ha.
intros x Hx.
apply H2.
now exists x.
Qed.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {em : excl_midd}.

(* is upper bound or lower bound.

   E.g. for upper bound :

     Given a set P (a predicate defining a subtype, i.e. a subset),
     which is ordered, "c" is an upper bound if ∀ x ∈ P, x ≤ c.

     An upper bound may or may not belong to P *)

Definition is_bound (le : T → T → Prop) (P : T → Type) c :=
  rl_forall_or_exists_not (λ x : T, P x → le x c).

Arguments is_bound le P c%_L.

Definition is_upper_bound := is_bound (λ a b, (a ≤ b)%L).
Definition is_lower_bound := is_bound (λ a b, (b ≤ a)%L).

Definition is_extremum le (Q : T → Type) c :=
  bool_of_sumbool (is_bound le Q c) = true ∧
  ∀ c', if is_bound le Q c' then le c c' else True.

Definition is_supremum := is_extremum (λ a b, (a ≤ b)%L).
Definition is_infimum := is_extremum (λ a b, (b ≤ a)%L).

Arguments is_extremum le Q c%_L.
Arguments is_supremum Q c%_L.
Arguments is_infimum Q c%_L.

(* AnBn below to be defined with "bisection", perhaps? *)
Fixpoint bisection (P : T → bool) lb ub n :=
  match n with
  | 0 => lb
  | S n' =>
      let x := ((lb + ub) / 2)%L in
      if P x then bisection P x ub n'
      else bisection P lb x n'
  end.

(* hypothesis: bn is an upper bound of P, an is not *)
(* a1 ∈ P, but the following "an" may or may not ∈ P *)
Fixpoint AnBn (P : T → Type) (an bn : T) n :=
  match n with
  | 0 => (an, bn)
  | S n' =>
      let a := ((an + bn) / 2)%L in
      if is_upper_bound P a then AnBn P an a n'
      else AnBn P a bn n'
  end.

Theorem rngl_middle_in_middle :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤ b → a ≤ (a + b) / 2 ≤ b)%L.
Proof.
intros Hop Hiv Hto * Hab.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite (H1 ((a + b) / 2)%L), (H1 a), (H1 b).
  split; apply (rngl_le_refl Hor).
}
specialize (rngl_0_lt_2 Hos Hc1 Hto) as Hz2.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
split. {
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hto) with (c := 2%L); [ easy | ].
  rewrite (rngl_div_mul Hiv); [ | easy ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  apply (rngl_add_le_mono Hos Hor); [ apply (rngl_le_refl Hor) | easy ].
} {
  apply (rngl_mul_le_mono_pos_r Hop Hiq Hto) with (c := 2%L); [ easy | ].
  rewrite (rngl_div_mul Hiv); [ | easy ].
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  apply (rngl_add_le_mono Hos Hor); [ easy | apply (rngl_le_refl Hor) ].
}
Qed.

Theorem AnBn_interval :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤ b)%L →
  ∀ P n an bn,
  AnBn P a b n = (an, bn)
  → (a ≤ an ≤ bn ≤ b)%L ∧
    bn = (an + (b - a) / 2 ^ n)%L.
Proof.
intros Hop Hiv Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
assert (Hiq : rngl_has_inv_or_pdiv T = true). {
  now apply rngl_has_inv_or_pdiv_iff; left.
}
assert (Hi1 : rngl_has_inv_or_pdiv T = true). {
  now apply rngl_has_inv_or_pdiv_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hab * Hanbn.
  rewrite (H1 a), (H1 b), (H1 an), (H1 bn).
  split. {
    split; [ apply (rngl_le_refl Hor) | ].
    split; apply (rngl_le_refl Hor).
  }
  rewrite rngl_add_0_l, (rngl_sub_0_r Hos).
  symmetry; apply H1.
}
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H2z.
intros * Hab * Hanbn.
revert a b Hab Hanbn.
induction n; intros. {
  cbn in Hanbn.
  injection Hanbn; intros; clear Hanbn; subst an bn.
  split. {
    split; [ apply (rngl_le_refl Hor) | ].
    split; [ easy | apply (rngl_le_refl Hor) ].
  }
  cbn; rewrite (rngl_div_1_r Hiq); [ | now left ].
  rewrite rngl_add_comm; symmetry.
  apply (rngl_sub_add Hop).
}
rewrite <- Nat.add_1_r.
rewrite (rngl_pow_add_r).
cbn in Hanbn |-*.
destruct (is_upper_bound P _) as [H1| H1]. {
  specialize (IHn a ((a + b) / 2))%L.
  assert (H : (a ≤ (a + b) / 2)%L). {
    now apply (rngl_middle_in_middle Hop Hiv Hto).
  }
  specialize (IHn H Hanbn); clear H.
  destruct  IHn as (Haabb, Hbnan).
  split. {
    split; [ easy | ].
    split; [ easy | ].
    eapply (rngl_le_trans Hor); [ apply Haabb | ].
    now apply (rngl_middle_in_middle Hop Hiv Hto).
  }
  rewrite Hbnan at 1.
  f_equal.
  rewrite <- (rngl_div_div Hos Hiv); cycle 1. {
    rewrite rngl_mul_1_r.
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  } {
    now apply (rngl_pow_neq_0 Hos Hiq).
  }
  f_equal.
  rewrite rngl_mul_1_r.
  apply (rngl_middle_sub_l Hop Hiv Hto).
} {
  specialize (IHn ((a + b) / 2) b)%L.
  assert (H : ((a + b) / 2 ≤ b)%L). {
    now apply (rngl_middle_in_middle Hop Hiv Hto).
  }
  specialize (IHn H Hanbn); clear H.
  destruct  IHn as (Haabb, Hbnan).
  split. {
    split; [ | easy ].
    eapply (rngl_le_trans Hor); [ | apply Haabb ].
    now apply (rngl_middle_in_middle Hop Hiv Hto).
  }
  rewrite Hbnan at 1.
  f_equal.
  rewrite <- (rngl_div_div Hos Hiv); cycle 1. {
    rewrite rngl_mul_1_r.
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  } {
    now apply (rngl_pow_neq_0 Hos Hiq).
  }
  f_equal.
  rewrite rngl_mul_1_r.
  apply (rngl_middle_sub_r Hop Hiv Hto).
}
Qed.

Theorem AnBn_le :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤ b)%L →
  ∀ P p q ap bp aq bq,
  p ≤ q
  → AnBn P a b p = (ap, bp)
  → AnBn P a b q = (aq, bq)
  → (ap ≤ aq ∧ bq ≤ bp)%L.
Proof.
intros Hop Hiv Hto * Hab * Hpq Hp Hq.
revert a b q Hab Hpq Hp Hq.
induction p; intros; cbn. {
  cbn in Hp.
  injection Hp; clear Hp; intros; subst ap bp.
  specialize (AnBn_interval Hop Hiv Hto) as H1.
  now specialize (H1 a b Hab P q aq bq Hq).
}
cbn in Hp.
destruct q; [ easy | cbn in Hq ].
apply Nat.succ_le_mono in Hpq.
destruct (is_upper_bound _ _) as [H1| H1]. {
  eapply IHp; [ | apply Hpq | apply Hp | apply Hq ].
  now apply (rngl_middle_in_middle Hop Hiv Hto).
} {
  eapply IHp; [ | apply Hpq | apply Hp | apply Hq ].
  now apply (rngl_middle_in_middle Hop Hiv Hto).
}
Qed.

Theorem rngl_abs_AnBn_sub_AnBn_le :
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤ b)%L →
  ∀ P p q, p ≤ q →
  ∀ ap bp aq bq,
  AnBn P a b p = (ap, bp)
  → AnBn P a b q = (aq, bq)
  → (rngl_abs (ap - aq) ≤ (b - a) / 2 ^ p)%L ∧
    (rngl_abs (bp - bq) ≤ (b - a) / 2 ^ p)%L.
Proof.
intros Hop Hiv Hto * Hab * Hpq * Ha Hb.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
assert (Hiq : rngl_has_inv_or_pdiv T = true). {
  now apply rngl_has_inv_or_pdiv_iff; left.
}
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H.
  do 2 rewrite (H (rngl_abs _))%L.
  rewrite (H ((b - a) / 2 ^ p)%L).
  split; apply (rngl_le_refl Hor).
}
assert (H2i : ∀ i, (2 ^ i)%L ≠ 0%L). {
  intros.
  apply (rngl_pow_neq_0 Hos Hiq).
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
specialize (AnBn_interval Hop Hiv Hto) as Habi.
rewrite (rngl_abs_nonpos_eq Hop Hto). 2: {
  apply (rngl_le_sub_0 Hop Hor).
  apply (AnBn_le Hop Hiv Hto a b Hab P p q ap bp aq bq Hpq Ha Hb).
}
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_le_0_sub Hop Hor).
  apply (AnBn_le Hop Hiv Hto a b Hab P p q ap bp aq bq Hpq Ha Hb).
}
rewrite (rngl_opp_sub_distr Hop).
revert a b q Hab Hpq Ha Hb.
induction p; intros. {
  cbn.
  rewrite (rngl_div_1_r Hiq); [ | now left ].
  cbn in Ha.
  injection Ha; clear Ha; intros; subst ap bp.
  split. {
    apply (rngl_sub_le_mono_r Hop Hor).
    specialize (Habi a b Hab P q aq bq Hb) as H1.
    destruct H1 as ((H1 & H2 & H3), _).
    now apply (rngl_le_trans Hor _ bq).
  } {
    apply (rngl_sub_le_mono_l Hop Hor).
    specialize (Habi a b Hab P q aq bq Hb) as H1.
    destruct H1 as ((H1 & H2 & H3), _).
    now apply (rngl_le_trans Hor _ aq).
  }
}
rewrite <- Nat.add_1_r.
rewrite (rngl_pow_add_r); cbn.
destruct q; [ easy | cbn ].
apply Nat.succ_le_mono in Hpq.
cbn in Ha, Hb.
destruct (is_upper_bound _ _) as [H1| H1]. {
  specialize (IHp a ((a + b) / 2)%L q).
  assert (H : (a ≤ (a + b) / 2)%L). {
    now apply (rngl_middle_in_middle Hop Hiv Hto).
  }
  specialize (IHp H Hpq Ha Hb); clear H.
  rewrite (rngl_middle_sub_l Hop Hiv Hto) in IHp.
  rewrite rngl_mul_1_r.
  rewrite <- (rngl_div_div Hos Hiv); [ easy | | apply H2i ].
  apply (rngl_2_neq_0 Hos Hc1 Hto).
} {
  specialize (IHp ((a + b) / 2)%L b q).
  assert (H : ((a + b) / 2 ≤ b)%L). {
    now apply (rngl_middle_in_middle Hop Hiv Hto).
  }
  specialize (IHp H Hpq Ha Hb); clear H.
  rewrite (rngl_middle_sub_r Hop Hiv Hto) in IHp.
  rewrite rngl_mul_1_r.
  rewrite <- (rngl_div_div Hos Hiv); [ easy | | apply H2i ].
  apply (rngl_2_neq_0 Hos Hc1 Hto).
}
Qed.

Context {Hop : rngl_has_opp T = true}.
Context {Hto : rngl_is_totally_ordered T = true}.
Let Hor := rngl_is_totally_ordered_is_ordered Hto.

Definition rngl_distance :=
  {| d_dist := rngl_dist; d_prop := rngl_dist_is_dist Hop Hto |}.

Theorem An_Bn_are_Cauchy_sequences :
  rngl_has_inv T = true →
  rngl_is_archimedean T = true →
  ∀ P a b, (a ≤ b)%L →
  is_Cauchy_sequence rngl_dist (λ n : nat, fst (AnBn P a b n)) ∧
  is_Cauchy_sequence rngl_dist (λ n : nat, snd (AnBn P a b n)).
Proof.
intros Hiv Har * Hab.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  progress unfold is_Cauchy_sequence.
  split. {
    intros * Hε.
    rewrite H1 in Hε.
    now apply rngl_lt_irrefl in Hε.
  } {
    intros * Hε.
    rewrite H1 in Hε.
    now apply rngl_lt_irrefl in Hε.
  }
}
set (u := λ n : nat, fst (AnBn P a b n)).
set (v := λ n : nat, snd (AnBn P a b n)).
specialize (int_part Hop Hc1 Hto Har) as H1.
split. {
  intros ε Hε.
  (* The size of the interval after N iterations is (b-a)/2^N; it
     must be less than ε; it implies that N must be greater
     than log2((b-a)/ε) where log2 is the log in base 2. Taking
     N = log2 ((b-a)/ε) + 1 should work. *)
  specialize (H1 ((b - a) / ε + 1))%L.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in H1. 2: {
    apply (rngl_le_0_add Hos Hto). 2: {
      apply (rngl_0_le_1 Hos Hto).
    }
    apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
    now apply (rngl_le_0_sub Hop Hor).
  }
  destruct H1 as (M & HM1 & HM2).
  rewrite rngl_of_nat_add in HM2.
  cbn in HM2.
  rewrite rngl_add_0_r in HM2.
  apply (rngl_add_lt_mono_r Hos Hor) in HM2.
  exists (S (Nat.log2_up M)).
  intros * Hp Hq.
  assert (H2i : ∀ i, (2 ^ i)%L ≠ 0%L). {
    intros.
    apply (rngl_pow_neq_0 Hos Hiq).
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  (* TODO: a lemma *)
  assert (H1 : (rngl_abs (u p - u q) ≤ (b - a) / 2 ^ min p q)%L). {
    clear Hp Hq.
    progress unfold u.
    specialize (AnBn_interval Hop Hiv Hto) as Habi.
    specialize (rngl_abs_AnBn_sub_AnBn_le Hop Hiv Hto) as H1.
    specialize (H1 a b Hab P).
    destruct (le_dec p q) as [Hpq| Hpq]. {
      rewrite Nat.min_l; [ | easy ].
      specialize (H1 p q Hpq).
      apply (H1 _ _ _ _ (surjective_pairing _) (surjective_pairing _)).
    } {
      apply Nat.nle_gt, Nat.lt_le_incl in Hpq.
      rewrite Nat.min_r; [ | easy ].
      rewrite <- (rngl_abs_opp Hop Hto).
      rewrite (rngl_opp_sub_distr Hop).
      specialize (H1 q p Hpq).
      apply (H1 _ _ _ _ (surjective_pairing _) (surjective_pairing _)).
    }
  }
  eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
  apply (rngl_lt_div_l Hop Hiv Hto). {
    apply (rngl_pow_pos_pos Hop Hiv Hto).
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto ε) in HM2; [ | easy ].
  rewrite (rngl_div_mul Hiv) in HM2. 2: {
    intros H; rewrite H in Hε.
    now apply rngl_lt_irrefl in Hε.
  }
  rewrite (rngl_mul_nat_comm Hos) in HM2.
  apply (rngl_le_lt_trans Hor _ (ε * rngl_of_nat M)). {
    now apply rngl_lt_le_incl.
  }
  apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto); [ easy | ].
  replace 2%L with (rngl_of_nat 2) by now cbn; rewrite rngl_add_0_r.
  rewrite <- (rngl_of_nat_pow Hos).
  apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
  apply Nat.log2_up_le_pow2; [ easy | cbn ].
  apply Nat.min_glb. {
    eapply Nat.le_trans; [ | apply Hp ].
    apply Nat.log2_up_succ_le.
  } {
    eapply Nat.le_trans; [ | apply Hq ].
    apply Nat.log2_up_succ_le.
  }
} {
  intros ε Hε.
  (* The size of the interval after N iterations is (b-a)/2^N; it
     must be less than ε; it implies that N must be greater
     than log2((b-a)/ε) where log2 is the log in base 2. Taking
     N = log2 ((b-a)/ε) + 1 should work. *)
  specialize (H1 ((b - a) / ε + 1))%L.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in H1. 2: {
    apply (rngl_le_0_add Hos Hto). 2: {
      apply (rngl_0_le_1 Hos Hto).
    }
    apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
    now apply (rngl_le_0_sub Hop Hor).
  }
  destruct H1 as (M & HM1 & HM2).
  rewrite rngl_of_nat_add in HM2.
  cbn in HM2.
  rewrite rngl_add_0_r in HM2.
  apply (rngl_add_lt_mono_r Hos Hor) in HM2.
  exists (S (Nat.log2_up M)).
  intros * Hp Hq.
  assert (H2i : ∀ i, (2 ^ i)%L ≠ 0%L). {
    intros.
    apply (rngl_pow_neq_0 Hos Hiq).
    apply (rngl_2_neq_0 Hos Hc1 Hto).
  }
  (* TODO: a lemma *)
  assert (H1 : (rngl_abs (v p - v q) ≤ (b - a) / 2 ^ min p q)%L). {
    clear Hp Hq.
    unfold v.
    specialize (AnBn_interval Hop Hiv Hto) as Habi.
    specialize (rngl_abs_AnBn_sub_AnBn_le Hop Hiv Hto) as H1.
    specialize (H1 a b Hab P).
    destruct (le_dec p q) as [Hpq| Hpq]. {
      rewrite Nat.min_l; [ | easy ].
      specialize (H1 p q Hpq).
      apply (H1 _ _ _ _ (surjective_pairing _) (surjective_pairing _)).
    } {
      apply Nat.nle_gt, Nat.lt_le_incl in Hpq.
      rewrite Nat.min_r; [ | easy ].
      rewrite <- (rngl_abs_opp Hop Hto).
      rewrite (rngl_opp_sub_distr Hop).
      specialize (H1 q p Hpq).
      apply (H1 _ _ _ _ (surjective_pairing _) (surjective_pairing _)).
    }
  }
  eapply (rngl_le_lt_trans Hor); [ apply H1 | ].
  apply (rngl_lt_div_l Hop Hiv Hto). {
    apply (rngl_pow_pos_pos Hop Hiv Hto).
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  apply (rngl_mul_lt_mono_pos_r Hop Hiq Hto) with (a := ε) in HM2; [ | easy ].
  rewrite (rngl_div_mul Hiv) in HM2. 2: {
    intros H; rewrite H in Hε.
    now apply rngl_lt_irrefl in Hε.
  }
  rewrite (rngl_mul_nat_comm Hos) in HM2.
  apply (rngl_le_lt_trans Hor _ (ε * rngl_of_nat M)). {
    now apply rngl_lt_le_incl.
  }
  apply (rngl_mul_lt_mono_pos_l Hop Hiq Hto); [ easy | ].
  replace 2%L with (rngl_of_nat 2) by now cbn; rewrite rngl_add_0_r.
  rewrite <- (rngl_of_nat_pow Hos).
  apply (rngl_of_nat_inj_lt Hos Hc1 Hto).
  apply Nat.log2_up_le_pow2; [ easy | cbn ].
  apply Nat.min_glb. {
    eapply Nat.le_trans; [ | apply Hp ].
    apply Nat.log2_up_succ_le.
  } {
    eapply Nat.le_trans; [ | apply Hq ].
    apply Nat.log2_up_succ_le.
  }
}
Qed.

Theorem rngl_abs_An_Bn_le :
  rngl_has_inv T = true →
  ∀ a b, (a ≤ b)%L →
  ∀ P n an bn,
  AnBn P a b n = (an, bn)
  → (rngl_abs (an - bn) ≤ (b - a) / 2 ^ n)%L.
Proof.
intros Hiv * Hab * Habn.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H.
  rewrite (H (rngl_abs _))%L.
  rewrite H.
  apply (rngl_le_refl Hor).
}
specialize (AnBn_interval Hop Hiv Hto) as H1.
specialize (H1 a b Hab P n _ _ (surjective_pairing _)).
rewrite Habn in H1; cbn in H1.
destruct H1 as (H1, H2).
rewrite H2.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_diag Hos).
rewrite <- (rngl_abs_opp Hop Hto).
rewrite (rngl_opp_sub_distr Hop).
rewrite (rngl_sub_0_r Hos).
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply (rngl_div_nonneg Hop Hiv Hto). {
    now apply (rngl_le_0_sub Hop Hor).
  } {
    apply (rngl_pow_pos_pos Hop Hiv Hto).
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
}
apply (rngl_le_refl Hor).
Qed.

Theorem limit_opp :
  ∀ u lim,
  is_limit_when_seq_tends_to_inf rngl_dist u lim
  → is_limit_when_seq_tends_to_inf rngl_dist (λ n, (- u n)%L) (- lim)%L.
Proof.
intros * Hu.
intros ε Hε.
destruct (Hu ε Hε) as (N, HN).
exists N.
intros n Hn.
cbn.
progress unfold rngl_dist.
rewrite <- (rngl_opp_add_distr Hop).
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_abs_opp Hop Hto).
now apply HN.
Qed.

Theorem gen_limit_ext_in :
  ∀ {A} (da : A → A → T) u v lim,
  (∀ n, u n = v n)
  → is_limit_when_seq_tends_to_inf da u lim
  → is_limit_when_seq_tends_to_inf da v lim.
Proof.
intros * Huv Hu ε Hε.
destruct (Hu ε Hε) as (N, HN).
exists N.
intros n Hn.
rewrite <- Huv.
now apply HN.
Qed.

Theorem limit_between_An_and_Bn :
  rngl_has_inv T = true →
  ∀ a b lim P,
  (a ≤ b)%L
  → is_limit_when_seq_tends_to_inf rngl_dist (λ n, fst (AnBn P a b n)) lim
  → is_limit_when_seq_tends_to_inf rngl_dist (λ n, snd (AnBn P a b n)) lim
  → ∀ n an bn, AnBn P a b n = (an, bn) → (an ≤ lim ≤ bn)%L.
Proof.
intros Hiv.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hab Hal Hbl * Habn.
  rewrite (H1 an), (H1 lim), (H1 bn).
  split; apply (rngl_le_refl Hor).
}
intros * Hab Hal Hbl * Habn.
split. {
  apply (rngl_nlt_ge_iff Hto).
  intros H5.
  specialize (Hal ((an - lim) / 2)%L) as H7.
  assert (H : (0 < (an - lim) / 2)%L). {
    apply (rngl_div_pos Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    now apply (rngl_lt_0_sub Hop Hor).
  }
  specialize (H7 H); clear H.
  destruct H7 as (M, HM).
  specialize (HM (max M n)).
  assert (H : M ≤ max M n) by apply Nat.le_max_l.
  specialize (HM H); clear H.
  assert (H : n ≤ max M n) by apply Nat.le_max_r.
  specialize (AnBn_le Hop Hiv Hto a b Hab P) as H6.
  specialize (H6 n (max M n) _ _ _ _ H Habn (surjective_pairing _)).
  destruct H6 as (H6, H7).
  cbn in HM.
  progress unfold rngl_dist in HM.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in HM. 2: {
    apply (rngl_le_0_sub Hop Hor).
    eapply (rngl_le_trans Hor); [ | apply H6 ].
    now apply rngl_lt_le_incl.
  }
  apply (rngl_nlt_ge Hor) in HM.
  apply HM; clear HM.
  apply (rngl_le_div_l Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  rewrite (rngl_add_sub_assoc Hop).
  apply (rngl_sub_le_mono_r Hop Hor).
  rewrite <- (rngl_add_sub_swap Hop).
  rewrite <- (rngl_add_sub_assoc Hop).
  eapply (rngl_le_trans Hor); [ apply H6 | ].
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_le_0_sub Hop Hor).
  eapply (rngl_le_trans Hor); [ | apply H6 ].
  now apply rngl_lt_le_incl.
} {
  apply (rngl_nlt_ge_iff Hto).
  intros H5.
  specialize (Hbl ((lim - bn) / 2)%L) as H7.
  assert (H : (0 < (lim - bn) / 2)%L). {
    apply (rngl_div_pos Hop Hiv Hto). 2: {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    now apply (rngl_lt_0_sub Hop Hor).
  }
  specialize (H7 H); clear H.
  destruct H7 as (M, HM).
  specialize (HM (max M n)).
  assert (H : M ≤ max M n) by apply Nat.le_max_l.
  specialize (HM H); clear H.
  assert (H : n ≤ max M n) by apply Nat.le_max_r.
  specialize (AnBn_le Hop Hiv Hto a b Hab P) as H6.
  specialize (H6 n (max M n) _ _ _ _ H Habn (surjective_pairing _)).
  destruct H6 as (H6, H7).
  cbn in HM.
  progress unfold rngl_dist in HM.
  rewrite (rngl_abs_nonpos_eq Hop Hto) in HM. 2: {
    apply (rngl_le_sub_0 Hop Hor).
    eapply (rngl_le_trans Hor); [ apply H7 | ].
    now apply rngl_lt_le_incl.
  }
  rewrite (rngl_opp_sub_distr Hop) in HM.
  apply (rngl_nlt_ge Hor) in HM.
  apply HM; clear HM.
  apply (rngl_le_div_l Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite rngl_mul_add_distr_l.
  rewrite rngl_mul_1_r.
  rewrite <- (rngl_sub_sub_distr Hop).
  apply (rngl_sub_le_mono_l Hop Hor).
  set (bm := snd (AnBn P a b (max M n))) in *.
  apply (rngl_le_sub_le_add_l Hop Hor).
  apply (rngl_le_trans Hor _ bn); [ easy | ].
  apply (rngl_le_add_l Hos Hor).
  apply (rngl_le_0_sub Hop Hor).
  apply (rngl_le_trans Hor _ bn); [ easy | ].
  now apply rngl_lt_le_incl.
}
Qed.

Theorem AnBn_exists_P :
  ∀ (P : _ → Prop) a b x,
  (∀ x : T, P x → (x ≤ b)%L)
  → (a ≤ x)%L
  → P x
  → ∀ n an bn,
  AnBn P a b n = (an, bn)
  → ∃ y, (an ≤ y ≤ bn)%L ∧ P y.
Proof.
intros * Hs Hab Hx * Habn.
revert a b x Hs Hab Hx an bn Habn.
induction n; intros; cbn in Habn. {
  injection Habn; clear Habn; intros; subst an bn.
  exists x.
  split; [ | easy ].
  split; [ easy | ].
  now apply Hs.
}
destruct (is_upper_bound _ _) as [H1| H1]. {
  apply (IHn a ((a + b) / 2)%L x H1 Hab Hx _ _ Habn).
}
destruct (rngl_leb_dec ((a + b) / 2) x) as [Habx| Habx]. {
  apply rngl_leb_le in Habx.
  apply (IHn ((a + b) / 2)%L b x Hs Habx Hx _ _ Habn).
}
destruct H1 as (z & Hz).
apply (IHn ((a + b) / 2)%L b z); [ easy | | | easy ]. {
  apply (rngl_nlt_ge_iff Hto).
  intros H3.
  apply Hz; clear Hz.
  intros H4.
  now apply rngl_lt_le_incl.
} {
  specialize (em_prop (P z)) as H3.
  destruct H3 as [H3| H3]; [ easy | ].
  exfalso.
  apply Hz.
  now intros H.
}
Qed.

Theorem in_AnBn :
  ∀ (P : _ → Prop) a b,
  P a
  → (∀ x, P x → (x ≤ b)%L)
  → ∀ n an bn,
  AnBn P a b n = (an, bn)
  → ∃ y : T, (an ≤ y ≤ bn)%L ∧ P y.
Proof.
intros * Ha Hs * Habn.
specialize (AnBn_exists_P P) as H1.
specialize (H1 a b a).
now specialize (H1 Hs (rngl_le_refl Hor _) Ha _ _ _ Habn).
Qed.

Theorem AnBn_not_P :
  ∀ (P : _ → Prop) a b n an bn,
  (∀ x : T, P x → (x ≤ b)%L)
  → AnBn P a b n = (an, bn)
  → ∀ y, (bn < y → ¬ P y)%L.
Proof.
intros * Hs Habn y Hby.
revert a b Hs Habn.
induction n; intros; cbn in Habn. {
  injection Habn; clear Habn; intros; subst an bn.
  intros H.
  apply Hs in H.
  now apply (rngl_nlt_ge Hor) in H.
}
destruct (is_upper_bound _ _) as [H1| H1]. {
  apply (IHn a ((a + b) / 2)%L H1 Habn).
} {
  apply (IHn ((a + b) / 2)%L b Hs Habn).
}
Qed.

Theorem after_AnBn :
  ∀ (P : _ → Prop) a b,
  P a
  → (∀ x : T, P x → (x ≤ b)%L)
  → ∀ n an bn,
  AnBn P a b n = (an, bn)
  → ∀ y, (bn < y)%L
  → ¬ P y.
Proof.
intros * Ha Hs * Habn * Hby.
specialize (AnBn_not_P P) as H1.
now apply (H1 a b n an bn Hs Habn).
Qed.

Theorem intermediate_value_prop_1 :
  rngl_has_inv T = true →
  ∀ f,
  is_continuous rngl_le rngl_dist rngl_dist f →
  ∀ a b c u,
  (a < b)%L
  → (f a < u)%L
  → (∀ x, (a ≤ x ≤ b)%L ∧ (f x < u)%L → (x ≤ c)%L)
  → c ≠ a.
Proof.
intros Hiv * Hfc * Hab Hfab Hub1.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite (H1 a), (H1 b) in Hab.
  now apply rngl_lt_irrefl in Hab.
}
specialize (Hfc a).
destruct Hfc as (Hfcl, Hfcr).
specialize (Hfcr (u - f a)%L) as H2.
assert (H : (0 < u - f a)%L) by now apply (rngl_lt_0_sub Hop Hor).
specialize (H2 H); clear H.
destruct H2 as (η & Hη & H2).
assert (Hfu : ∀ x, (a ≤ x < rngl_min (a + η) b → f x < u)%L). {
  intros x Hx.
  assert (H : (rngl_abs (x - a) < η)%L). {
    rewrite (rngl_abs_nonneg_eq Hop Hor) by now apply (rngl_le_0_sub Hop Hor).
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    eapply (rngl_lt_le_trans Hor); [ apply Hx | ].
    apply (rngl_le_min_l Hto).
  }
  destruct Hx as (Hax, Hx).
  specialize (H2 x Hax H); clear H.
  destruct (rngl_leb_dec (f x) (f a)) as [Hfxa| Hfxa]. {
    apply rngl_leb_le in Hfxa.
    cbn in H2.
    progress unfold rngl_dist in H2.
    rewrite (rngl_abs_nonpos_eq Hop Hto) in H2. 2: {
      now apply (rngl_le_sub_0 Hop Hor).
    }
    now apply (rngl_le_lt_trans Hor _ (f a)).
  }
  apply (rngl_leb_gt_iff Hto) in Hfxa.
  cbn in H2.
  progress unfold rngl_dist in H2.
  rewrite (rngl_abs_nonneg_eq Hop Hor) in H2. 2: {
     apply (rngl_le_0_sub Hop Hor).
     now apply rngl_lt_le_incl.
  }
  now apply (rngl_sub_lt_mono_r Hop Hor) in H2.
}
intros H; subst c.
assert (Haηb : (a < (a + rngl_min (a + η) b) / 2 ≤ b)%L). {
  split. {
    apply (rngl_lt_div_r Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite (rngl_mul_2_r).
    apply (rngl_add_lt_mono_l Hos Hor).
    apply (rngl_min_glb_lt); [ | easy ].
    now apply (rngl_lt_add_r Hos Hor).
  } {
    apply (rngl_le_div_l Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite (rngl_mul_2_r).
    apply (rngl_add_le_mono Hos Hor). {
      now apply rngl_lt_le_incl.
    }
    apply (rngl_le_min_r Hor).
  }
}
set (P := λ x : T, (a ≤ x ≤ b)%L ∧ (f x < u)%L).
assert (H : P ((a + rngl_min (a + η) b) / 2)%L). {
  progress unfold P.
  split. {
    split; [ | easy ].
    now apply rngl_lt_le_incl.
  }
  apply Hfu.
  split; [ now apply rngl_lt_le_incl | ].
  apply (rngl_lt_div_l Hop Hiv Hto). {
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  rewrite (rngl_mul_2_r).
  apply (rngl_add_lt_mono_r Hos Hor).
  apply (rngl_min_glb_lt); [ | easy ].
  now apply (rngl_lt_add_r Hos Hor).
}
apply Hub1 in H.
now apply (rngl_nlt_ge Hor) in H.
Qed.

Theorem intermediate_value_prop_2 :
  rngl_has_inv T = true →
  ∀ f, is_continuous rngl_le rngl_dist rngl_dist f →
  ∀ a b c u,
  (a < b)%L
  → (u < f b)%L
  → (∀ c',
       if is_upper_bound (λ x : T, (a ≤ x ≤ b)%L ∧ (f x < u)%L) c' then
         (c ≤ c')%L
       else True)
  → c ≠ b.
Proof.
intros Hiv * Hfc * Hab Hub Hc.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite (H1 a), (H1 b) in Hab.
  now apply rngl_lt_irrefl in Hab.
}
specialize (Hfc b).
destruct Hfc as (Hfcl, Hfcr).
specialize (Hfcl (f b - u)%L) as H2.
assert (H : (0 < f b - u)%L) by now apply (rngl_lt_0_sub Hop Hor).
specialize (H2 H); clear H.
destruct H2 as (η & Hη & H2).
assert (Hfu : ∀ x, (rngl_max a (b - η) < x ≤ b → u < f x)%L). {
  intros x Hx.
  assert (H : (rngl_abs (x - b) < η)%L). {
    rewrite (rngl_abs_nonpos_eq Hop Hto) by now apply (rngl_le_sub_0 Hop Hor).
    rewrite (rngl_opp_sub_distr Hop).
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    rewrite rngl_add_comm.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    eapply (rngl_le_lt_trans Hor); [ | apply Hx ].
    apply (rngl_le_max_r Hto).
  }
  destruct Hx as (Hx, Hxb).
  specialize (H2 x Hxb H); clear H.
  destruct (rngl_leb_dec (f x) (f b)) as [Hfxb| Hfxb]. {
    apply rngl_leb_le in Hfxb.
    cbn in H2.
    progress unfold rngl_dist in H2.
    rewrite (rngl_abs_nonpos_eq Hop Hto) in H2. 2: {
      now apply (rngl_le_sub_0 Hop Hor).
    }
    rewrite (rngl_opp_sub_distr Hop) in H2.
    now apply (rngl_sub_lt_mono_l Hop Hor) in H2.
  }
  apply (rngl_leb_gt_iff Hto) in Hfxb.
  now apply (rngl_lt_trans Hor _ (f b)).
}
intros H.
subst c.
set (x := ((rngl_max a (b - η) + b) / 2)%L) in *.
specialize (Hc x) as H3.
set (P := λ x : T, (a ≤ x ≤ b)%L ∧ (f x < u)%L) in H3.
destruct (is_upper_bound P x) as [Hux| Hux]. 2: {
  clear H3.
  destruct Hux as (y, Hy).
  apply Hy; clear Hy.
  intros Hpy.
  progress unfold P in Hpy.
  destruct Hpy as (Hayb, Hfy).
  apply (rngl_nlt_ge_iff Hto); intros Hxy.
  specialize (Hfu y) as H3.
  assert (H : (rngl_max a (b - η) < y ≤ b)%L). {
    split; [ | easy ].
    apply (rngl_le_lt_trans Hor _ x); [ | easy ].
    progress unfold x.
    apply (rngl_le_div_r Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    rewrite (rngl_mul_2_r).
    apply (rngl_add_le_mono_l Hos Hor).
    apply rngl_max_lub; [ now apply rngl_lt_le_incl| ].
    apply (rngl_le_sub_l Hop Hto).
    now apply rngl_lt_le_incl.
  }
  specialize (H3 H).
  now apply (rngl_lt_asymm Hor) in Hfy.
}
apply (rngl_nlt_ge Hor) in H3; apply H3; clear H3.
progress unfold x.
apply (rngl_lt_div_l Hop Hiv Hto). {
  apply (rngl_0_lt_2 Hos Hc1 Hto).
}
rewrite (rngl_mul_2_r).
apply (rngl_add_lt_mono_r Hos Hor).
apply rngl_max_lub_lt; [ easy | ].
apply (rngl_lt_sub_lt_add_l Hop Hor).
now apply (rngl_lt_add_l Hos Hor).
Qed.

Theorem rngl_not_le_le : ∀ a b, ¬ (a ≤ b)%L → (b ≤ a)%L.
Proof.
intros * Hab.
apply (rngl_nle_gt_iff Hto) in Hab.
now apply rngl_lt_le_incl.
Qed.

Theorem exists_supremum :
  rngl_has_inv T = true →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ (P : T → Prop) a b,
  P a
  → (∀ x, P x → (x ≤ b)%L)
  → ∃ c, is_supremum P c ∧ (c ≤ b)%L ∧
    is_limit_when_seq_tends_to_inf rngl_dist (λ n, fst (AnBn P a b n)) c ∧
    is_limit_when_seq_tends_to_inf rngl_dist (λ n, snd (AnBn P a b n)) c.
Proof.
intros Hiv Har Hco.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H.
  intros * Ha Hs.
  exists 0%L.
  rewrite (H b).
  split. {
    progress unfold is_supremum.
    progress unfold is_extremum.
    destruct (is_bound _ P 0%L) as [H1| H1]. {
      split; [ easy | ].
      intros.
      rewrite (H c').
      destruct (is_bound _ P 0%L); [ | easy ].
      apply (rngl_le_refl Hor).
    } {
      exfalso.
      destruct H1 as (x, Hx); apply Hx.
      intros Hpx.
      rewrite (H x).
      apply (rngl_le_refl Hor).
    }
  }
  split; [ apply (rngl_le_refl Hor) | ].
  rewrite (H a).
  split. {
    intros ε Hε.
    rewrite H in Hε.
    now apply rngl_lt_irrefl in Hε.
  } {
    intros ε Hε.
    rewrite H in Hε.
    now apply rngl_lt_irrefl in Hε.
  }
}
intros * Ha Hs.
(* Proof in
   https://en.wikipedia.org/wiki/Least-upper-bound_property#
     Proof_using_Cauchy_sequences *)
set (u := λ n, fst (AnBn P a b n)).
set (v := λ n, snd (AnBn P a b n)).
specialize (An_Bn_are_Cauchy_sequences Hiv Har P) as H1.
assert (Hab : (a ≤ b)%L) by now apply Hs.
specialize (H1 a b Hab).
progress fold u in H1.
progress fold v in H1.
destruct H1 as (Hcsu, Hcsv).
specialize (Hco _ Hcsu) as Hac.
specialize (Hco _ Hcsv) as Hbc.
destruct Hac as (lima, Hal).
destruct Hbc as (limb, Hbl).
move limb before lima.
assert
  (Hl : (is_limit_when_seq_tends_to_inf rngl_dist (λ n, (u n - v n)) 0)%L). {
  intros ε Hε.
  progress unfold u.
  progress unfold v.
  specialize (int_part Hop Hc1 Hto Har) as H1.
  specialize (H1 ((b - a) / ε)%L).
  destruct H1 as (N, HN).
  rewrite (rngl_abs_nonneg_eq Hop Hor) in HN. 2: {
    apply (rngl_div_nonneg Hop Hiv Hto); [ | easy ].
    now apply (rngl_le_0_sub Hop Hor).
  }
  exists (N + 1).
  intros n Hn.
  cbn.
  progress unfold rngl_dist.
  rewrite (rngl_sub_0_r Hos).
  eapply (rngl_le_lt_trans Hor). {
    apply (rngl_abs_An_Bn_le Hiv _ _ Hab P n).
    apply surjective_pairing.
  }
  apply (rngl_lt_div_l Hop Hiv Hto). {
    apply (rngl_pow_pos_pos Hop Hiv Hto).
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  replace 2%L with (rngl_of_nat 2) by now cbn; rewrite rngl_add_0_r.
  rewrite <- (rngl_of_nat_pow Hos).
  rewrite <- (rngl_mul_nat_comm Hos).
  apply (rngl_lt_div_l Hop Hiv Hto); [ easy | ].
  eapply (rngl_lt_le_trans Hor); [ apply HN | ].
  apply (rngl_of_nat_inj_le Hos Hc1 Hto).
  eapply Nat.le_trans; [ apply Hn | ].
  apply Nat.log2_up_le_pow2; [ flia Hn | ].
  now apply Nat.log2_up_le_lin.
}
assert (Hlab : lima = limb). {
  generalize Hbl; intros Hblv.
  apply limit_opp in Hbl.
  specialize (limit_add Hop Hiv Hto (rngl_dist_is_dist Hop Hto)) as H1.
  specialize (H1 (rngl_dist_add_add_le Hop Hto)).
  specialize (H1 _ _ _ _ Hal Hbl).
  rewrite (rngl_add_opp_r Hop) in H1.
  eapply gen_limit_ext_in in H1. 2: {
    now intros; rewrite (rngl_add_opp_r Hop).
  }
  apply (rngl_sub_move_0_r Hop).
  eapply (limit_unique Hop Hiv Hto (rngl_dist_is_dist Hop Hto)).
  apply H1.
  apply Hl.
}
subst limb; rename lima into lim.
exists lim.
move lim before b.
clear Hl.
progress unfold is_supremum.
progress unfold is_extremum.
destruct (is_bound _ P lim) as [H1| H1]. {
  split. {
    split; [ easy | ].
    intros c.
    move c before b.
    destruct (is_bound _ P c) as [H2| H2]; [ | easy ].
    apply (rngl_nlt_ge_iff Hto).
    intros Hc.
    specialize (limit_between_An_and_Bn Hiv a b lim P) as Hl.
    specialize (Hl Hab Hal Hbl).
    specialize (AnBn_interval Hop Hiv Hto a b Hab P) as Hi.
    specialize (in_AnBn P a b Ha Hs) as Hin.
    (* if (b - a) / 2 ^ n < lim - c, then c < an < lim,
       we have a y between an and bn with P y, but
       therefore greater than c, what contredicts H2 *)
    (* (b - a) / 2 ^ n < lim - c, if
       (b - a) < (lim - c) * 2 ^ n, if
       (b - a) / (lim - c) < 2 ^ n, if
       (b - a) / (lim - c) < n *)
    set (x := ((b - a) / (lim - c))%L).
    destruct (int_part Hop Hc1 Hto Har x) as (n & Hnx & Hxn1).
    destruct (Hin n _ _ (surjective_pairing _)) as (y & Hny & Hy).
    assert (Hcy : (c < y)%L). {
      eapply (rngl_lt_le_trans Hor); [ | apply Hny ].
      specialize (Hl n _ _ (surjective_pairing _)) as H3.
      destruct (Hi n _ _ (surjective_pairing _)) as (Hanb, H4).
      set (an := fst (AnBn P a b n)) in *.
      set (bn := snd (AnBn P a b n)) in *.
      symmetry in H4.
      apply (rngl_add_sub_eq_r Hos) in H4.
      rewrite <- H4.
      apply (rngl_lt_add_lt_sub_l Hop Hor).
      rewrite rngl_add_comm.
      apply (rngl_lt_add_lt_sub_l Hop Hor).
      apply (rngl_lt_le_trans Hor _ (lim - c)). 2: {
        now apply (rngl_sub_le_mono_r Hop Hor).
      }
      apply (rngl_lt_div_l Hop Hiv Hto). {
        apply (rngl_pow_pos_pos Hop Hiv Hto).
        apply (rngl_0_lt_2 Hos Hc1 Hto).
      }
      replace 2%L with (rngl_of_nat 2) by now cbn; rewrite rngl_add_0_r.
      rewrite <- (rngl_mul_nat_pow_comm Hos).
      apply (rngl_lt_div_l Hop Hiv Hto). {
        now apply (rngl_lt_0_sub Hop Hor).
      }
      progress fold x.
      rewrite <- (rngl_abs_nonneg_eq Hop Hor x). 2: {
        progress unfold x.
        apply (rngl_div_nonneg Hop Hiv Hto). {
          now apply (rngl_le_0_sub Hop Hor).
        } {
          now apply (rngl_lt_0_sub Hop Hor).
        }
      }
      rewrite <- (rngl_of_nat_pow Hos).
      eapply (rngl_lt_le_trans Hor); [ apply Hxn1 | ].
      apply (rngl_of_nat_inj_le Hos Hc1 Hto).
      rewrite Nat.add_1_r.
      apply Nat.le_succ_l.
      now apply Nat.pow_gt_lin_r.
    }
    apply H2 in Hy.
    now apply (rngl_nlt_ge Hor) in Hy.
  } {
    specialize (limit_between_An_and_Bn Hiv a b lim P) as Hl.
    specialize (Hl Hab Hal Hbl).
    now specialize (Hl 0 _ _ (surjective_pairing _)).
  }
} {
  exfalso.
  destruct H1 as (c, Hc).
  apply Hc; clear Hc.
  intros Hc.
  apply (rngl_nlt_ge_iff Hto).
  intros Hlc.
  specialize (limit_between_An_and_Bn Hiv a b lim P) as Hl.
  specialize (Hl Hab Hal Hbl).
  specialize (AnBn_interval Hop Hiv Hto a b Hab P) as Hi.
  specialize (in_AnBn P a b Ha Hs) as Hin.
  specialize (after_AnBn P a b Ha Hs) as Han.
  (* faut que je trouve un n tel que bn < c,
     (qui contradira Hc avec Han),
     c'est-à-dire an + (b - a) / 2 ^ n < c
     qui marche si lim + (b - a) / 2 ^ n < c
     c'est-à-dire (b - a) / 2 ^ n < c - lim,
     c'est-à-dire (b - a) / (c - lim) < 2 ^ n
     ça marche si (b - a) / (c - lim) < n *)
  set (x := ((b - a) / (c - lim))%L).
  destruct (int_part Hop Hc1 Hto Har x) as (n & Hnx & Hxn1).
  remember (AnBn P a b n) as abn eqn:Habn; symmetry in Habn.
  destruct abn as (an, bn).
  specialize (Han n _ _ Habn c) as H1.
  apply H1; [ clear H1 | easy ].
  destruct (Hi n _ _ Habn) as (Haabb & Hbn).
  rewrite Hbn.
  apply (rngl_le_lt_trans Hor _ (lim + (b - a) / 2 ^ n)%L). {
    apply (rngl_add_le_mono Hos Hor); [ | apply (rngl_le_refl Hor) ].
    apply (Hl n _ _ Habn).
  }
  apply (rngl_lt_add_lt_sub_l Hop Hor).
  apply (rngl_lt_div_l Hop Hiv Hto). {
    apply (rngl_pow_pos_pos Hop Hiv Hto).
    apply (rngl_0_lt_2 Hos Hc1 Hto).
  }
  replace 2%L with (rngl_of_nat 2) by now cbn; rewrite rngl_add_0_r.
  rewrite <- (rngl_mul_nat_pow_comm Hos).
  apply (rngl_lt_div_l Hop Hiv Hto). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  progress fold x.
  replace (rngl_of_nat 2) with 2%L by now cbn; rewrite rngl_add_0_r.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor x). 2: {
    progress unfold x.
    apply (rngl_div_nonneg Hop Hiv Hto). {
      now apply (rngl_le_0_sub Hop Hor).
    } {
      now apply (rngl_lt_0_sub Hop Hor).
    }
  }
  replace 2%L with (rngl_of_nat 2) by now cbn; rewrite rngl_add_0_r.
  rewrite <- (rngl_of_nat_pow Hos).
  eapply (rngl_lt_le_trans Hor); [ apply Hxn1 | ].
  apply (rngl_of_nat_inj_le Hos Hc1 Hto).
  rewrite Nat.add_1_r.
  apply Nat.le_succ_l.
  now apply Nat.pow_gt_lin_r.
}
Qed.

(* https://en.wikipedia.org/wiki/Intermediate_value_theorem#Proof *)
Theorem intermediate_value_le :
  rngl_has_inv T = true →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ f, is_continuous rngl_le rngl_dist rngl_dist f
  → ∀ a b u, (a ≤ b)%L
  → (f a ≤ u ≤ f b)%L
  → ∃ c : T, (a ≤ c ≤ b)%L ∧ f c = u.
Proof.
intros Hiv Har Hco * Hfc * Hab Hfab.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  exists a.
  rewrite (H1 (f a)), (H1 a), (H1 b), (H1 u).
  split; [ split; apply (rngl_le_refl Hor) | easy ].
}
destruct (rngl_eqb_dec (f a) u) as [Hau| Hau]. {
  apply (rngl_eqb_eq Heo) in Hau.
  exists a.
  split; [ | easy ].
  split; [ apply (rngl_le_refl Hor) | easy ].
}
destruct (rngl_eqb_dec (f b) u) as [Hbu| Hbu]. {
  apply (rngl_eqb_eq Heo) in Hbu.
  exists b.
  split; [ | easy ].
  split; [ easy | apply (rngl_le_refl Hor) ].
}
apply (rngl_eqb_neq Heo) in Hau, Hbu.
assert (H : (f a < u < f b)%L). {
  apply not_eq_sym in Hbu.
  now split; apply rngl_le_neq.
}
clear Hfab Hau Hbu; rename H into Hfab.
assert (H : (a < b)%L). {
  apply rngl_le_neq.
  split; [ easy | ].
  intros H; subst b.
  destruct Hfab as (Hfau, Hfua).
  apply (rngl_lt_trans Hor u) in Hfau; [ | easy ].
  now apply rngl_lt_irrefl in Hfau.
}
move H before Hab; clear Hab; rename H into Hab.
set (P := λ x : T, (a ≤ x ≤ b)%L ∧ (f x < u)%L).
set (s := { x | P x }).
assert (Ha : P a). {
  unfold P; cbn.
  split; [ | easy ].
  split; [ apply (rngl_le_refl Hor) | now apply rngl_lt_le_incl ].
}
assert (Hs : ∀ x : s, (proj1_sig x < b)%L). {
  intros.
  destruct x as (x & (Hax & Hxb) & Hx); cbn.
  destruct Hfab as (Hfau & Hufb).
  apply (rngl_lt_eq_cases Hor) in Hxb.
  destruct Hxb as [Hxb| Hxb]; [ easy | subst x ].
  move Hufb at bottom.
  now apply (rngl_lt_asymm Hor) in Hx.
}
(* "Since S is non-empty and bounded above by b, by completeness, the
    supremum c = sup S exists" *)
specialize (exists_supremum Hiv Har Hco P) as H1.
specialize (H1 a b Ha).
assert (H : (∀ x, P x → (x ≤ b)%L)) by now intros y ((Hay & Hyb) & Hy).
specialize (H1 H); clear H.
destruct H1 as (c & Hc & H1 & Hlima & Hlimb).
progress unfold is_supremum in Hc.
progress unfold is_extremum in Hc.
remember (is_bound _ _ _) as Hub1 eqn:Hub2; symmetry in Hub2.
destruct Hub1 as [Hub1| ]; [ | easy ].
progress unfold is_bound in Hub2.
destruct (rl_forall_or_exists_not _) as [Hub3| ]; [ | easy ].
clear Hub2 Hub3.
enough (H : ∃ d, _) by apply H.
exists c.
split. {
  split; [ now apply Hub1 | easy ].
}
(* continuity of f to prove that *)
assert (Hac : c ≠ a). {
  now apply (intermediate_value_prop_1 Hiv f Hfc a b c u).
}
assert (Hbc : c ≠ b). {
  now apply (intermediate_value_prop_2 Hiv f Hfc a b c u).
}
specialize (Hfc c) as Hcc.
destruct Hcc as (Hccl, Hccr).
set (η2 := rngl_min (c - a) (b - c)).
assert (Hzη2 : (0 < η2)%L). {
  progress unfold η2.
  apply not_eq_sym in Hac.
  apply rngl_min_glb_lt. {
    apply (rngl_lt_0_sub Hop Hor).
    apply rngl_le_neq; split; [ | easy ].
    now apply Hub1.
  } {
    apply (rngl_lt_0_sub Hop Hor).
    now apply rngl_le_neq.
  }
}
assert
  (H2 : ∀ ε, (0 < ε)%L → ∃ η, (0 < η ≤ η2)%L ∧
    (∀ x, (rngl_abs (x - c) < η)%L → (rngl_abs (f x - f c) < ε)%L) ∧
    (∃ a', (c - η < a' ≤ c)%L ∧ P a') ∧
    (∃ a'', (c ≤ a'' < c + η)%L ∧ ¬ P a'')). {
  intros ε Hε.
  destruct (Hccl ε Hε) as (η1 & Hzη1 & Hη1).
  destruct (Hccr ε Hε) as (η3 & Hzη3 & Hη3).
  exists (rngl_min3 η1 η2 η3).
  assert (H12 : (0 < rngl_min3 η1 η2 η3)%L). {
    apply rngl_min_glb_lt; [ | easy ].
    now apply rngl_min_glb_lt.
  }
  split. {
    split; [ easy | ].
    progress unfold rngl_min3.
    eapply (rngl_le_trans Hor).
    apply (rngl_le_min_l Hto).
    apply (rngl_le_min_r Hor).
  }
  split. {
    intros x Hx.
    destruct (rngl_leb_dec x c) as [Hxc| Hxc]. {
      apply rngl_leb_le in Hxc.
      apply (Hη1 _ Hxc).
      eapply (rngl_lt_le_trans Hor); [ apply Hx | ].
      progress unfold rngl_min3.
      eapply (rngl_le_trans Hor).
      apply (rngl_le_min_l Hto).
      apply (rngl_le_min_l Hto).
    } {
      apply (rngl_leb_gt_iff Hto) in Hxc.
      apply rngl_lt_le_incl in Hxc.
      apply (Hη3 _ Hxc).
      eapply (rngl_lt_le_trans Hor); [ apply Hx | ].
      progress unfold rngl_min3.
      apply (rngl_le_min_r Hor).
    }
  }
  split. {
    apply rl_not_forall_exists.
    intros Hx.
    assert (Hx' : ∀ x, ((c - rngl_min3 η1 η2 η3 < x ≤ c)%L) → ¬ P x). {
      intros y Hy.
      specialize (Hx y) as H2.
      now intros Hpy; apply H2; clear H2.
    }
    clear Hx; rename Hx' into Hx.
    set (x := ((c - rngl_min3 η1 η2 η3 / 2)%L)).
    destruct Hc as (_, Hc).
    specialize (Hc x) as H2.
    destruct (is_bound _ P x) as [Hpx| Hpx]. 2: {
      destruct Hpx as (y & Hy); clear H2.
      apply Hy; clear Hy; intros Hpy.
      apply (rngl_nlt_ge_iff Hto); intros Hxy.
      destruct (rngl_leb_dec y c) as [Hyc| Hyc]. {
        apply rngl_leb_le in Hyc.
        specialize (Hx y) as H2; apply H2; [ | easy ]; clear H2.
        split; [ | easy ].
        eapply (rngl_le_lt_trans Hor _ x); [ | easy ].
        progress unfold x.
        apply (rngl_sub_le_mono_l Hop Hor).
        apply (rngl_le_div_l Hop Hiv Hto). {
          apply (rngl_0_lt_2 Hos Hc1 Hto).
        }
        rewrite (rngl_mul_2_r).
        apply (rngl_le_add_l Hos Hor).
        now apply rngl_lt_le_incl.
      } {
        apply rngl_leb_nle in Hyc.
        now apply Hyc, Hub1.
      }
    }
    apply (rngl_nlt_ge Hor) in H2; apply H2; clear H2.
    progress unfold x.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    apply (rngl_lt_add_l Hos Hor).
    apply (rngl_lt_div_r Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    now rewrite (rngl_mul_0_l Hos).
  } {
    apply rl_not_forall_exists.
    intros Hx.
    assert (Hx' : ∀ x, (c ≤ x < c + rngl_min3 η1 η2 η3)%L → P x). {
      intros y Hy.
      specialize (Hx y) as H2.
      specialize (em_prop (P y)) as H3.
      destruct H3 as [H3| H3]; [ easy | ].
      exfalso; apply H2.
      split; [ | easy ].
      now exfalso; apply H2.
    }
    clear Hx; rename Hx' into Hx.
    set (x := ((c + rngl_min3 η1 η2 η3 / 2)%L)).
    destruct Hc as (_, Hc).
    specialize (Hc x) as H2.
    destruct (is_bound _ P x) as [Hpx| Hpx]. 2: {
      destruct Hpx as (y & Hy); clear H2.
      apply Hy; clear Hy; intros Hpy.
      apply (rngl_le_trans Hor _ c); [ now apply Hub1 | ].
      progress unfold x.
      apply (rngl_le_add_r Hos Hor).
      apply (rngl_le_div_r Hop Hiv Hto). {
        apply (rngl_0_lt_2 Hos Hc1 Hto).
      }
      rewrite (rngl_mul_0_l Hos).
      now apply rngl_lt_le_incl.
    }
    assert (H : ∀ y, _ → _) by apply Hpx.
    move H before Hpx; clear Hpx; rename H into Hpx.
    specialize (Hx x) as H3.
    assert (H : (c ≤ x < c + rngl_min3 η1 η2 η3)%L). {
      split; [ easy | ].
      progress unfold x.
      apply (rngl_add_lt_mono_l Hos Hor).
      apply (rngl_lt_div_l Hop Hiv Hto). {
        apply (rngl_0_lt_2 Hos Hc1 Hto).
      }
      rewrite (rngl_mul_2_r).
      now apply (rngl_lt_add_l Hos Hor).
    }
    specialize (H3 H); clear H.
    apply Hub1 in H3.
    apply (rngl_nlt_ge Hor) in H3.
    apply H3; clear H3.
    progress unfold x.
    apply (rngl_lt_add_r Hos Hor).
    apply (rngl_lt_div_r Hop Hiv Hto). {
      apply (rngl_0_lt_2 Hos Hc1 Hto).
    }
    now rewrite (rngl_mul_0_l Hos).
  }
}
assert (H3 : ∀ ε, (0 < ε → u - ε < f c < u + ε)%L). {
  intros ε Hε.
  specialize (H2 ε Hε).
  destruct H2 as (η & Hzη & Hη & (a' & Ha' & Hpa') & (a'' & Ha'' & Hpa'')).
  progress unfold P in Hpa'; cbn in Hpa'.
  split. 2: {
    apply (rngl_le_lt_trans Hor _ (f a' + ε)). 2: {
      now apply (rngl_add_lt_mono_r Hos Hor).
    }
    specialize (Hη a') as H2.
    rewrite (rngl_abs_nonpos_eq Hop Hto) in H2. 2: {
      now apply (rngl_le_sub_0 Hop Hor).
    }
    rewrite (rngl_opp_sub_distr Hop) in H2.
    apply (rngl_le_sub_le_add_l Hop Hor).
    apply (rngl_le_trans Hor _ (rngl_abs (f a' - f c))). {
      rewrite <- (rngl_abs_opp Hop Hto).
      rewrite (rngl_opp_sub_distr Hop).
      apply (rngl_le_abs_diag Hop Hto).
    }
    apply rngl_lt_le_incl, H2.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    rewrite rngl_add_comm.
    now apply (rngl_lt_sub_lt_add_l Hop Hor).
  } {
    apply (rngl_le_lt_trans Hor _ (f a'' - ε)). {
      apply (rngl_sub_le_mono_r Hop Hor).
      apply (rngl_nlt_ge_iff Hto).
      intros H.
      apply Hpa''.
      progress unfold P.
      split; [ | easy ].
      split. {
        apply (rngl_le_trans Hor _ c); [ | easy ].
        now apply Hub1.
      } {
        apply (rngl_le_trans Hor _ (c + η2)). {
          apply (rngl_le_trans Hor _ (c + η)). {
            now apply rngl_lt_le_incl.
          }
          now apply (rngl_add_le_mono_l Hos Hor).
        }
        rewrite rngl_add_comm.
        apply (rngl_le_add_le_sub_r Hop Hor).
        progress unfold η2.
        apply (rngl_le_min_r Hor).
      }
    }
    specialize (Hη a'') as H2.
    rewrite (rngl_abs_nonneg_eq Hop Hor) in H2. 2: {
      now apply (rngl_le_0_sub Hop Hor).
    }
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    rewrite rngl_add_comm.
    apply (rngl_lt_sub_lt_add_l Hop Hor).
    apply (rngl_le_lt_trans Hor _ (rngl_abs (f a'' - f c))). {
      apply (rngl_le_abs_diag Hop Hto).
    }
    apply H2.
    now apply (rngl_lt_sub_lt_add_l Hop Hor).
  }
}
apply (rngl_le_antisymm Hor); apply (rngl_nlt_ge_iff Hto); intros Hu. {
  specialize (H3 (f c - u)%L).
  assert (H : (0 < f c - u)%L). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  destruct (H3 H) as (H4, H5); clear H.
  rewrite (rngl_add_sub_assoc Hop) in H5.
  rewrite rngl_add_comm, (rngl_add_sub Hos) in H5.
  revert H5; apply rngl_lt_irrefl.
} {
  specialize (H3 (u - f c)%L).
  assert (H : (0 < u - f c)%L). {
    now apply (rngl_lt_0_sub Hop Hor).
  }
  destruct (H3 H) as (H4, H5); clear H.
  rewrite (rngl_sub_sub_distr Hop) in H4.
  rewrite (rngl_sub_diag Hos), rngl_add_0_l in H4.
  revert H4; apply rngl_lt_irrefl.
}
Qed.

Theorem supremum_opp :
  ∀ (P Q : _ → Prop) c,
  (∀ x, P x ↔ Q (- x)%L)
  → is_supremum P c
  → is_infimum Q (- c).
Proof.
intros * Hpq Hp.
progress unfold is_supremum in Hp.
progress unfold is_infimum.
progress unfold is_extremum in Hp.
progress unfold is_extremum.
destruct (is_bound _ P c) as [Hpc| Hpc]; [ | easy ].
destruct (is_bound _ _ (- c)) as [Hqc| Hqc]. {
  split; [ easy | ].
  intros c'.
  destruct (is_bound _ _ c') as [Hqc'| Hqc']; [ | easy ].
  destruct Hp as (_, Hp).
  specialize (Hp (- c')%L) as H1.
  destruct (is_bound _ P (- c')) as [Hpoc'| Hpoc']. {
    apply (rngl_opp_le_compat Hop Hor).
    now rewrite (rngl_opp_involutive Hop).
  }
  exfalso.
  destruct Hpoc' as (x, Hx).
  apply Hx; clear Hx.
  intros Hpx.
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  apply Hqc'.
  now apply Hpq.
}
destruct Hqc as (x, Hx).
exfalso.
apply Hx; clear Hx.
intros Hqx.
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_involutive Hop).
apply Hpc.
apply Hpq.
now rewrite (rngl_opp_involutive Hop).
Qed.

(* *)

Theorem upper_bound_property :
  rngl_has_inv T = true →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ (P : T → Prop) a b,
  P a
  → (∀ x, P x → (x ≤ b)%L)
  → ∃ c, is_supremum P c ∧ (c ≤ b)%L.
Proof.
intros Hiv Har Hco * Ha Hs.
destruct (exists_supremum Hiv Har Hco P a b Ha Hs) as (c & Hc).
now exists c.
Qed.

Theorem lower_bound_property :
  rngl_has_inv T = true →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ (P : T → Prop) a b,
  P b
  → (∀ x, P x → (a ≤ x)%L)
  → ∃ c, is_infimum P c ∧ (a ≤ c)%L.
Proof.
intros Hiv Har Hco * Ha Hs.
specialize (exists_supremum Hiv Har Hco (λ x, P (- x)%L)) as H1.
specialize (H1 (- b) (- a))%L.
cbn in H1.
rewrite (rngl_opp_involutive Hop) in H1.
specialize (H1 Ha).
assert (H : ∀ x, P (- x)%L → (x ≤ - a)%L).  {
  intros x Hx.
  apply (rngl_le_opp_r Hop Hto).
  rewrite rngl_add_comm.
  apply (rngl_le_opp_r Hop Hto).
  now apply Hs.
}
specialize (H1 H); clear H.
destruct H1 as (c & Hc & Hca).
exists (- c)%L.
apply (supremum_opp _ P) in Hc; [ | easy ].
split; [ easy | ].
apply (rngl_opp_le_compat Hop Hor).
now rewrite (rngl_opp_involutive Hop).
Qed.

Theorem intermediate_value :
  rngl_has_inv T = true →
  rngl_is_archimedean T = true →
  is_complete T rngl_dist →
  ∀ f, is_continuous rngl_le rngl_dist rngl_dist f
  → ∀ a b u, (a ≤ b)%L
  → (rngl_min (f a) (f b) ≤ u ≤ rngl_max (f a) (f b))%L
  → ∃ c, (a ≤ c ≤ b)%L ∧ f c = u.
Proof.
intros Hiv Har Hco.
intros * Hfc * Hab Hfab.
progress unfold rngl_min in Hfab.
progress unfold rngl_max in Hfab.
remember (f a ≤? f b)%L as ab eqn:Hlab; symmetry in Hlab.
specialize (intermediate_value_le Hiv Har Hco) as H1.
destruct ab; [ now apply (H1 _ Hfc) | ].
specialize (H1 (λ x, (- f x))%L).
cbn in H1.
assert
  (H : is_continuous rngl_le rngl_dist rngl_dist (λ x, (- f x))%L). {
  intros x.
  specialize (Hfc x).
  destruct Hfc as (Hfcl, Hfcr).
  split. {
    intros ε Hε.
    destruct (Hfcl ε Hε) as (η & Hzη & Hη).
    destruct (Hfcr ε Hε) as (η' & Hzη' & Hη').
    exists (rngl_min η η').
    split; [ now apply rngl_min_glb_lt | ].
    intros y _ Hy.
    cbn.
    progress unfold rngl_dist.
    rewrite <- (rngl_abs_opp Hop Hto).
    rewrite (rngl_opp_sub_distr Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite rngl_add_comm.
    rewrite (rngl_add_opp_r Hop).
    destruct (rngl_leb_dec x y) as [Hxy| Hxy]. {
      apply rngl_leb_le in Hxy.
      apply (Hη' y Hxy).
      eapply (rngl_lt_le_trans Hor); [ apply Hy | ].
      apply (rngl_le_min_r Hor).
    } {
      apply (rngl_leb_gt_iff Hto) in Hxy.
      apply rngl_lt_le_incl in Hxy.
      apply (Hη y Hxy).
      eapply (rngl_lt_le_trans Hor); [ apply Hy | ].
      apply (rngl_le_min_l Hto).
    }
  } {
    intros ε Hε.
    destruct (Hfcl ε Hε) as (η & Hzη & Hη).
    destruct (Hfcr ε Hε) as (η' & Hzη' & Hη').
    exists (rngl_min η η').
    split; [ now apply rngl_min_glb_lt | ].
    intros y _ Hy.
    cbn.
    progress unfold rngl_dist.
    rewrite <- (rngl_abs_opp Hop Hto).
    rewrite (rngl_opp_sub_distr Hop).
    rewrite (rngl_sub_opp_r Hop).
    rewrite rngl_add_comm.
    rewrite (rngl_add_opp_r Hop).
    destruct (rngl_leb_dec x y) as [Hxy| Hxy]. {
      apply rngl_leb_le in Hxy.
      apply (Hη' y Hxy).
      eapply (rngl_lt_le_trans Hor); [ apply Hy | ].
      apply (rngl_le_min_r Hor).
    } {
      apply (rngl_leb_gt_iff Hto) in Hxy.
      apply rngl_lt_le_incl in Hxy.
      apply (Hη y Hxy).
      eapply (rngl_lt_le_trans Hor); [ apply Hy | ].
      apply (rngl_le_min_l Hto).
    }
  }
}
specialize (H1 H a b (- u)%L Hab); clear H.
assert (H : (- f a ≤ - u ≤ - f b)%L). {
  now split; apply -> (rngl_opp_le_compat Hop Hor).
}
specialize (H1 H); clear H.
destruct H1 as (c & Hacb & Hc).
exists c.
split; [ easy | ].
now apply (rngl_opp_inj Hop) in Hc.
Qed.

End a.

Arguments is_infimum {T ro em} Q c%_L.
Arguments is_lower_bound {T ro em} P c%_L.
Arguments upper_bound_property {T ro rp} _ Hop Hto Hiv Har Hco P (a b)%_L.
