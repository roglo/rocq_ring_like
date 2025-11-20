(** * Order

Theorems about order relation of the ring-like library.

Generally applied in ordered ring-like structures which can be
recognizable by
<<
  rngl_is_ordered T = true
>>
but sometimes work even without this hypothesis.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

In general, it is not necessary to import this module. The normal
usage is to do:
<<
    Require Import RingLike.Core.
>>
which imports the present module and some other ones.
 *)

Require Import Stdlib.Arith.Arith.
Require Import Utf8.
Require Import Structures.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Definition rngl_eqb_dec a b := sumbool_of_bool (a =? b)%L.
Definition rngl_leb_dec a b := sumbool_of_bool (a ≤? b)%L.
Definition rngl_ltb_dec a b := sumbool_of_bool (a <? b)%L.

Theorem rngl_is_totally_ordered_is_ordered :
  rngl_is_totally_ordered T = true → rngl_is_ordered T = true.
Proof.
intros Hto.
progress unfold rngl_is_totally_ordered in Hto.
progress unfold rngl_is_ordered.
now destruct rngl_opt_leb as [(leb, tot)| ].
Qed.

Theorem rngl_leb_neg_ltb :
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤? b = negb (b <? a))%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr; move rr before rp.
intros.
specialize rngl_ord_le_antisymm as H1.
specialize (rngl_ord_total_prop) as H2.
rewrite Hto in H2.
clear Hto.
progress unfold rngl_ltb.
progress unfold rngl_leb.
progress unfold rngl_is_ordered in Hor.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
destruct rngl_opt_leb as [(leb, tot)| ]; [ | easy ].
symmetry.
remember (leb a b) as ab eqn:Hab.
remember (leb b a) as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab. {
  destruct ba; [ cbn | easy ].
  rewrite (H1 a b Hab Hba).
  rewrite (rngl_eqb_refl Heo).
  apply Bool.negb_involutive.
}
destruct ba. {
  cbn.
  rewrite Bool.negb_involutive.
  apply Bool.not_true_iff_false.
  intros H.
  apply (rngl_eqb_eq Heo) in H; subst b.
  congruence.
}
exfalso.
specialize (H2 a b).
destruct H2; congruence.
Qed.

Theorem rngl_ltb_neg_leb :
  rngl_is_totally_ordered T = true →
  ∀ a b, (a <? b = negb (b ≤? a))%L.
Proof.
intros Hto *.
rewrite (rngl_leb_neg_ltb Hto).
symmetry; apply Bool.negb_involutive.
Qed.

Theorem rngl_leb_le :
  ∀ a b, (a ≤? b)%L = true ↔ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
now split; intros Hab; destruct rngl_opt_leb as [(leb, tot)| ].
Qed.

Theorem rngl_ltb_lt :
  rngl_has_eq_dec_or_order T = true →
  ∀ a b, (a <? b)%L = true ↔ (a < b)%L.
Proof.
intros Heo *.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  apply Bool.andb_true_iff in Hab.
  destruct Hab as (H1, H2).
  apply rngl_leb_le in H1.
  now apply (rngl_neqb_neq Heo) in H2.
} {
  apply Bool.andb_true_iff.
  split.
  now apply rngl_leb_le.
  now apply (rngl_neqb_neq Heo).
}
Qed.

Theorem rngl_leb_nle :
  ∀ a b, (a ≤? b)%L = false ↔ ¬ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
split; intros Hab. {
  apply Bool.not_true_iff_false in Hab.
  now destruct rngl_opt_leb as [(leb, tot)| ].
} {
  apply Bool.not_true_iff_false.
  now destruct rngl_opt_leb as [(leb, tot)| ].
}
Qed.

Theorem rngl_ltb_nlt :
  rngl_has_eq_dec_or_order T = true →
  ∀ a b, (a <? b)%L = false ↔ ¬ (a < b)%L.
Proof.
intros Heo *.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  intros (H1, H2).
  apply rngl_leb_le in H1.
  apply (rngl_neqb_neq Heo) in H2.
  now rewrite H1, H2 in Hab.
} {
  apply Bool.andb_false_iff.
  remember (a ≤? b)%L as ab eqn:H1.
  symmetry in H1.
  destruct ab; [ right | now left ].
  apply Bool.not_true_iff_false.
  intros H2.
  apply rngl_leb_le in H1.
  apply (rngl_neqb_neq Heo) in H2.
  now apply Hab.
}
Qed.

Theorem rngl_le_refl :
  rngl_is_ordered T = true →
  ∀ a, (a ≤ a)%L.
Proof.
intros Hor *.
specialize (rngl_opt_ord T) as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_leb_refl :
  rngl_is_ordered T = true →
  ∀ a, (a ≤? a)%L = true.
Proof.
intros Hor *.
apply rngl_leb_le.
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_le_antisymm :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ b → b ≤ a → a = b)%L.
Proof.
intros Hor *.
specialize (rngl_opt_ord T) as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_neq : ∀ a b, (a < b ↔ a ≤ b ∧ a ≠ b)%L.
Proof. easy. Qed.

Theorem rngl_lt_le_incl : ∀ a b, (a < b → a ≤ b)%L.
Proof.
intros * Hab.
now apply rngl_le_neq.
Qed.

Theorem rngl_lt_asymm :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → ¬ b < a)%L.
Proof.
intros Hor * Hab Hba.
apply rngl_le_neq in Hab, Hba.
destruct Hab as (Hab, Hnab).
destruct Hba as (Hba, _).
now apply Hnab, (rngl_le_antisymm Hor).
Qed.

Theorem rngl_nle_gt :
  rngl_is_ordered T = true →
  ∀ a b, (b < a → ¬ (a ≤ b))%L.
Proof.
intros Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr; move rr after rp.
intros * Hab H1.
destruct Hab as (H2, H3).
apply H3; clear H3.
now apply rngl_ord_le_antisymm.
Qed.

(********)

Theorem rngl_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros Hor *.
specialize (rngl_opt_ord T) as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply rngl_le_neq.
split. {
  apply rngl_lt_le_incl in Hab, Hbc.
  now apply (rngl_le_trans Hor _ b).
} {
  intros H; subst c.
  now apply (rngl_lt_asymm Hor a b).
}
Qed.

Theorem rngl_lt_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b ≤ c)%L → (a < c)%L.
Proof.
intros Hor.
intros * Hab Hbc.
apply rngl_le_neq.
split. {
  apply (rngl_le_trans Hor _ b); [ | easy ].
  now apply rngl_lt_le_incl.
} {
  intros H; subst c.
  now apply (rngl_nle_gt Hor) in Hab.
}
Qed.

Theorem rngl_le_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply rngl_le_neq.
split. {
  apply (rngl_le_trans Hor _ b); [ easy | ].
  now apply rngl_lt_le_incl.
} {
  intros H; subst c.
  now apply (rngl_nle_gt Hor) in Hbc.
}
Qed.

Theorem rngl_le_iff_leb_eq :
  ∀ a b c d,
  (a ≤ b ↔ c ≤ d)%L
  → ((a ≤? b) = (c ≤? d))%L.
Proof.
intros * Habcd.
remember (a ≤? b)%L as ab eqn:Hab.
remember (c ≤? d)%L as cd eqn:Hcd.
symmetry in Hab, Hcd.
destruct ab. {
  destruct cd; [ easy | ].
  apply rngl_leb_le in Hab.
  apply rngl_leb_nle in Hcd.
  exfalso; apply Hcd.
  apply Habcd, Hab.
} {
  destruct cd; [ | easy ].
  apply rngl_leb_nle in Hab.
  apply rngl_leb_le in Hcd.
  exfalso; apply Hab.
  apply Habcd, Hcd.
}
Qed.

Theorem rngl_lt_eq_cases :
  rngl_is_ordered T = true →
  ∀ a b : T, (a ≤ b)%L ↔ (a < b)%L ∨ a = b.
Proof.
intros Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
progress unfold rngl_lt.
split; intros Hab. {
  destruct (rngl_eqb_dec a b) as [H1| H1]. {
    apply (rngl_eqb_eq Heo) in H1.
    now right.
  }
  apply (rngl_eqb_neq Heo) in H1.
  now left.
} {
  destruct Hab as [(H1, H2)| Hab]; [ easy | ].
  subst b.
  apply (rngl_le_refl Hor).
}
Qed.

Theorem rngl_lt_irrefl : ∀ a : T, ¬ (a < a)%L.
Proof.
intros a Ha.
now destruct Ha as (H1, H2).
Qed.

Theorem rngl_not_le :
  rngl_is_totally_ordered T = true →
  ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hab.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr; move rr after rp.
specialize rngl_ord_total_prop as H.
rewrite Hto in H.
destruct (H a b) as [H2| H2]; [ easy | ].
split; [ | easy ].
now intros H3; subst a.
Qed.

Theorem rngl_nle_gt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, (¬ (a ≤ b) ↔ b < a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
split; intros Hab. {
  apply (rngl_not_le Hto) in Hab.
  apply rngl_le_neq.
  split; [ easy | ].
  now apply not_eq_sym.
} {
  intros H1.
  apply rngl_le_neq in Hab.
  destruct Hab as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_nlt_ge :
  rngl_is_ordered T = true →
  ∀ a b, (b ≤ a → ¬ (a < b))%L.
Proof.
intros Hor * Hab H1.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr; move rr before rp.
destruct H1 as (H1, H2).
apply H2; clear H2.
now apply rngl_ord_le_antisymm.
Qed.

Theorem rngl_nlt_ge_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, (¬ (a < b) ↔ b ≤ a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
split; intros Hab. {
  apply rngl_leb_le.
  destruct (rngl_leb_dec b a) as [H1| H1]; [ easy | ].
  exfalso; apply Hab; clear Hab.
  apply rngl_leb_nle in H1.
  now apply (rngl_nle_gt_iff Hto).
} {
  intros H1.
  apply rngl_le_neq in H1.
  destruct H1 as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_leb_gt :
  rngl_is_ordered T = true →
  ∀ a b, (b < a → ¬ (a ≤ b))%L.
Proof.
intros Hor * Hab H1.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr; move rr before rp.
destruct Hab as (Hab, H); apply H; clear H.
now apply rngl_ord_le_antisymm.
Qed.

Theorem rngl_leb_gt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, ((a ≤? b) = false ↔ b < a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
split; intros Hab. {
  apply rngl_leb_nle in Hab.
  apply (rngl_not_le Hto) in Hab.
  apply rngl_le_neq.
  split; [ easy | ].
  now apply not_eq_sym.
} {
  apply rngl_leb_nle.
  intros H1.
  now apply (rngl_nle_gt Hor) in Hab.
}
Qed.

Theorem rngl_ltb_ge :
  rngl_is_ordered T = true →
  ∀ a b, (b ≤ a → (a <? b) = false)%L.
Proof.
intros Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros * Hba.
apply (rngl_ltb_nlt Heo).
intros Hab.
destruct Hab as (Hab & H).
apply H; clear H.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr; move rr before rp.
now apply rngl_ord_le_antisymm.
Qed.

Theorem rngl_ltb_ge_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, ((a <? b) = false ↔ b ≤ a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
split; intros Hab. {
  apply (rngl_ltb_nlt Heo) in Hab.
  now apply (rngl_nlt_ge_iff Hto) in Hab.
} {
  apply (rngl_ltb_nlt Heo).
  intros H1.
  now apply (rngl_nlt_ge Hor) in Hab.
}
Qed.

Theorem rngl_eq_le_incl :
  rngl_is_ordered T = true →
  ∀ a b, a = b → (a ≤ b)%L.
Proof.
intros Hor * Hab.
subst.
apply (rngl_le_refl Hor).
Qed.

(* min & max *)

Theorem rngl_min_id :
  rngl_is_ordered T = true →
  ∀ a, rngl_min a a = a.
Proof.
intros Hor *.
progress unfold rngl_min.
now rewrite (rngl_leb_refl Hor).
Qed.

Theorem rngl_max_id :
  rngl_is_ordered T = true →
  ∀ a, rngl_max a a = a.
Proof.
intros Hor *.
progress unfold rngl_max.
now rewrite (rngl_leb_refl Hor).
Qed.

Theorem rngl_min_comm :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_min a b = rngl_min b a.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
destruct ab. {
  destruct ba; [ | easy ].
  apply rngl_leb_le in Hab, Hba.
  now apply (rngl_le_antisymm Hor).
} {
  destruct ba; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hab, Hba.
  now apply (rngl_lt_asymm Hor) in Hba.
}
Qed.

Theorem rngl_max_comm :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_max a b = rngl_max b a.
Proof.
intros Hto *.
specialize (rngl_min_comm Hto a b) as H1.
progress unfold rngl_min in H1.
progress unfold rngl_max.
now destruct (a ≤? b)%L, (b ≤? a)%L.
Qed.

Theorem rngl_min_assoc :
  rngl_is_totally_ordered T = true →
  ∀ a b c,
  rngl_min a (rngl_min b c) = rngl_min (rngl_min a b) c.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Hab, Hbc.
destruct ab. {
  destruct bc; [ | easy ].
  rewrite Hab.
  apply rngl_leb_le in Hab, Hbc.
  apply (rngl_le_trans Hor a) in Hbc; [ | easy ].
  apply rngl_leb_le in Hbc.
  now rewrite Hbc.
}
rewrite Hbc.
destruct bc; [ now rewrite Hab | ].
apply (rngl_leb_gt_iff Hto) in Hab, Hbc.
apply rngl_lt_le_incl in Hbc.
apply (rngl_le_lt_trans Hor c) in Hab; [ | easy ].
apply (rngl_leb_gt_iff Hto) in Hab.
now rewrite Hab.
Qed.

Theorem rngl_max_assoc :
  rngl_is_totally_ordered T = true →
  ∀ a b c,
  rngl_max a (rngl_max b c) = rngl_max (rngl_max a b) c.
Proof.
intros Hto *.
specialize (rngl_min_assoc Hto a b c) as H1.
progress unfold rngl_min in H1.
progress unfold rngl_max.
remember (a ≤? b)%L as ab eqn:Hab.
remember (a ≤? c)%L as ac eqn:Hac.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Hab, Hac, Hbc.
destruct ab. {
  destruct bc; [ | now rewrite Hab, Hbc ].
  rewrite Hab, Hac in H1.
  rewrite Hbc, Hac.
  now destruct ac.
}
destruct bc; [ easy | ].
rewrite Hbc, Hac in H1.
rewrite Hab, Hac.
now destruct ac.
Qed.

Theorem rngl_min_l_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_min a b = a ↔ (a ≤ b)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
split; intros H1. {
  destruct ab; [ now apply rngl_leb_le in Hab | ].
  destruct ba; [ subst b; apply (rngl_le_refl Hor) | ].
  apply (rngl_leb_gt_iff Hto) in Hab, Hba.
  apply rngl_lt_le_incl in Hba.
  now apply (rngl_nlt_ge Hor) in Hba.
} {
  destruct ab; [ easy | ].
  apply rngl_leb_le in H1.
  now rewrite Hab in H1.
}
Qed.

Theorem rngl_min_r_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_min a b = b ↔ (b ≤ a)%L.
Proof.
intros Hto *.
rewrite (rngl_min_comm Hto).
apply (rngl_min_l_iff Hto).
Qed.

Theorem rngl_max_l_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_max a b = a ↔ (b ≤ a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
specialize (rngl_min_l_iff Hto a b) as H1.
progress unfold rngl_min in H1.
progress unfold rngl_max.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  apply rngl_leb_le in Hab.
  split; [ now intros; subst b | ].
  intros Hba.
  apply (rngl_le_antisymm Hor _ _ Hba Hab).
} {
  apply (rngl_leb_gt_iff Hto) in Hab.
  apply rngl_lt_le_incl in Hab.
  easy.
}
Qed.

Theorem rngl_max_r_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_max a b = b ↔ (a ≤ b)%L.
Proof.
intros Hto *.
rewrite (rngl_max_comm Hto).
apply (rngl_max_l_iff Hto).
Qed.

Theorem rngl_min_glb_lt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b c, (c < rngl_min a b ↔ c < a ∧ c < b)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab; [ | now destruct ab ].
destruct ab. {
  apply rngl_leb_le in Hab.
  split; [ easy | ].
  now apply (rngl_lt_le_trans Hor _ a).
}
apply (rngl_leb_gt_iff Hto) in Hab.
split; [ | easy ].
now apply (rngl_lt_trans Hor _ b).
Qed.

Theorem rngl_min_le_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b c, (rngl_min a b ≤ c ↔ a ≤ c ∨ b ≤ c)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab. {
  now destruct ab; [ left | right ].
}
destruct ab. {
  destruct Hcab as [Hac| Hbc]; [ easy | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_trans Hor _ b).
}
destruct Hcab as [Hac| Hbc]; [ | easy ].
apply (rngl_leb_gt_iff Hto) in Hab.
apply (rngl_le_trans Hor _ a); [ | easy ].
now apply rngl_lt_le_incl in Hab.
Qed.

Theorem rngl_min_lt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b c, (rngl_min a b < c ↔ a < c ∨ b < c)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab. {
  now destruct ab; [ left | right ].
}
destruct ab. {
  destruct Hcab as [Hac| Hbc]; [ easy | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_lt_trans Hor _ b).
}
destruct Hcab as [Hac| Hbc]; [ | easy ].
apply (rngl_leb_gt_iff Hto) in Hab.
now apply (rngl_lt_trans Hor _ a).
Qed.

Theorem rngl_max_lt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b c, (a < rngl_max b c ↔ a < b ∨ a < c)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_max.
remember (b ≤? c)%L as bc eqn:Hbc.
symmetry in Hbc.
destruct bc. {
  split; intros Ha; [ now right | ].
  destruct Ha as [Ha| Ha]; [ | easy ].
  apply rngl_leb_le in Hbc.
  now apply (rngl_lt_le_trans Hor _ b).
} {
  split; intros Ha; [ now left | ].
  destruct Ha as [Ha| Ha]; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hbc.
  now apply (rngl_lt_trans Hor _ c).
}
Qed.

Theorem rngl_le_min_l :
  rngl_is_totally_ordered T = true →
  ∀ a b, (rngl_min a b ≤ a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt_iff Hto) in Hc.
now apply rngl_lt_le_incl.
Qed.

Theorem rngl_le_min_r :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_min_le_compat_l :
  rngl_is_totally_ordered T = true →
  ∀ a b c, (b ≤ c → rngl_min a b ≤ rngl_min a c)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros * Hbc.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (a ≤? c)%L as ac eqn:Hac.
symmetry in Hab, Hac.
destruct ab. {
  destruct ac; [ apply (rngl_le_refl Hor) | ].
  apply rngl_leb_le in Hab.
  now apply (rngl_le_trans Hor _ b).
} {
  destruct ac; [ | easy ].
  apply (rngl_leb_gt_iff Hto) in Hab.
  now apply rngl_lt_le_incl in Hab.
}
Qed.

Theorem rngl_le_max_l :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
now apply rngl_leb_le in Hc.
Qed.

Theorem rngl_le_max_r :
  rngl_is_totally_ordered T = true →
  ∀ a b, (b ≤ rngl_max a b)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt_iff Hto) in Hc.
now apply rngl_lt_le_incl.
Qed.

Theorem rngl_min_glb :
  ∀ a b c, (a ≤ b → a ≤ c → a ≤ rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_min_glb_lt :
  ∀ a b c, (a < b → a < c → a < rngl_min b c)%L.
Proof.
intros * Hab Hac.
progress unfold rngl_min.
now destruct (b ≤? c)%L.
Qed.

Theorem rngl_max_lub :
  ∀ a b c, (a ≤ c → b ≤ c → rngl_max a b ≤ c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

Theorem rngl_max_lub_lt :
  ∀ a b c, (a < c → b < c → rngl_max a b < c)%L.
Proof.
intros * Hac Hbc.
progress unfold rngl_max.
now destruct (a ≤? b)%L.
Qed.

(* comparison *)

Definition rngl_compare a b :=
  if (a =? b)%L then Eq
  else if (a ≤? b)%L then Lt else Gt.

Theorem rngl_compare_eq_iff :
  rngl_has_eq_dec_or_order T = true →
  ∀ a b, rngl_compare a b = Eq ↔ a = b.
Proof.
intros Heo *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  split; [ | easy ].
  now apply (rngl_eqb_eq Heo) in Hab.
} {
  destruct (a ≤? b)%L. {
    split; [ easy | ].
    now apply (rngl_eqb_neq Heo) in Hab.
  } {
    split; [ easy | ].
    now apply (rngl_eqb_neq Heo) in Hab.
  }
}
Qed.

Theorem rngl_compare_lt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_compare a b = Lt ↔ (a < b)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Heo) in Hab.
  subst b.
  now apply rngl_lt_irrefl in H.
} {
  apply (rngl_eqb_neq Heo) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ | easy ].
    intros _.
    now apply rngl_le_neq.
  } {
    split; [ easy | ].
    apply (rngl_leb_gt_iff Hto) in Halb.
    intros H.
    now apply (rngl_lt_asymm Hor) in H.
  }
}
Qed.

Theorem rngl_compare_gt_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_compare a b = Gt ↔ (b < a)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
intros.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Heo) in Hab.
  subst b.
  now apply rngl_lt_irrefl in H.
} {
  apply (rngl_eqb_neq Heo) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ easy | ].
    intros H.
    now apply (rngl_nle_gt Hor) in H.
  } {
    now apply (rngl_leb_gt_iff Hto) in Halb.
  }
}
Qed.

Theorem rngl_compare_le_iff :
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_compare a b ≠ Gt ↔ (a ≤ b)%L.
Proof.
intros Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
split; intros H. {
  apply (rngl_nlt_ge_iff Hto).
  now intros H1; apply (rngl_compare_gt_iff Hto) in H1.
} {
  apply (rngl_nlt_ge Hor) in H.
  intros H1.
  now apply (rngl_compare_gt_iff Hto) in H1.
}
Qed.

Theorem rngl_compare_refl :
  rngl_has_eq_dec_or_order T = true →
  ∀ a, rngl_compare a a = Eq.
Proof.
intros Heo *.
now apply (rngl_compare_eq_iff Heo).
Qed.

End a.

Notation "x ?= y" := (rngl_compare x y) : ring_like_scope.

Arguments rngl_eqb_dec {T ro} (a b)%_L.
Arguments rngl_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_le_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_leb_dec {T ro} (a b)%_L.
Arguments rngl_lt_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_ltb_dec {T ro} (a b)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_max {T ro} (a b)%_L.
