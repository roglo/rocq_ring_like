From Stdlib Require Import Utf8 Arith.
Require Import RingLike_structures.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_leb_le :
  ∀ a b, (a ≤? b)%L = true ↔ (a ≤ b)%L.
Proof.
intros.
progress unfold rngl_leb.
progress unfold rngl_le.
now split; intros Hab; destruct rngl_opt_leb.
Qed.

Theorem rngl_ltb_lt :
  ∀ a b, (a <? b)%L = true ↔ (a < b)%L.
Proof.
intros.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  destruct rngl_opt_leb; [ | easy ].
  now apply Bool.negb_true_iff.
} {
  destruct rngl_opt_leb; [ | easy ].
  now apply Bool.negb_true_iff.
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
  now destruct rngl_opt_leb.
} {
  apply Bool.not_true_iff_false.
  now destruct rngl_opt_leb.
}
Qed.

Theorem rngl_ltb_nlt :
  ∀ a b, (a <? b)%L = false ↔ ¬ (a < b)%L.
Proof.
intros.
progress unfold rngl_ltb.
progress unfold rngl_lt.
split; intros Hab. {
  destruct rngl_opt_leb; [ | easy ].
  apply Bool.negb_false_iff in Hab.
  apply Bool.not_false_iff_true.
  easy.
} {
  destruct rngl_opt_leb; [ | easy ].
  apply Bool.negb_false_iff.
  apply Bool.not_false_iff_true in Hab.
  easy.
}
Qed.

Theorem rngl_le_dec :
  rngl_is_ordered T = true →
  ∀ a b : T, ({a ≤ b} + {¬ a ≤ b})%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_refl :
  rngl_is_ordered T = true →
  ∀ a, (a ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
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
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b ≤ c)%L → (a ≤ c)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
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

Theorem rngl_lt_iff :
  rngl_is_ordered T = true → ∀ a b, (a < b ↔ a ≤ b ∧ a ≠ b)%L.
Proof.
intros * Hor a b.
progress unfold rngl_lt.
progress unfold rngl_le.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_not_le as H1.
specialize (rngl_le_antisymm Hor) as H2.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
split. {
  intros Hab.
  specialize (H1 b a) as H3.
  rewrite Hab in H3.
  assert (H : false ≠ true) by easy.
  specialize (H3 H); clear H.
  split; [ easy | ].
  destruct H3; congruence.
} {
  intros (H3, H4).
  remember (rngl_leb b a) as x eqn:Hx; symmetry in Hx.
  destruct x; [ | easy ].
  now specialize (H2 _ _ H3 Hx).
}
Qed.

Theorem rngl_lt_eq_cases :
  rngl_is_ordered T = true → ∀ a b : T, (a ≤ b)%L ↔ (a < b)%L ∨ a = b.
Proof.
intros Hor *.
progress unfold rngl_lt.
progress unfold rngl_le.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_not_le as H1.
specialize (rngl_le_antisymm Hor) as H2.
specialize (rngl_le_refl Hor) as H3.
progress unfold rngl_le in H1.
progress unfold rngl_le in H2.
progress unfold rngl_le in H3.
destruct rngl_opt_leb as [rngl_leb| ]; [ | easy ].
split. {
  intros H.
  remember (rngl_leb b a) as ba eqn:Hba; symmetry in Hba.
  destruct ba; [ | now left ].
  now specialize (H2 _ _ H Hba); right.
} {
  intros H.
  destruct H as [H4| H4]; [ now apply H1; rewrite H4 | ].
  subst b; apply H3.
}
Qed.

Theorem rngl_lt_dec :
  rngl_is_ordered T = true →
  ∀ a b : T, ({a < b} + {¬ a < b})%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_le_dec as H1.
destruct (H1 b a) as [H2| H2]; [ right | left ]. {
  intros H3.
  apply (rngl_lt_iff Hor) in H3.
  destruct H3 as (H3, H4).
  now apply (rngl_le_antisymm Hor) in H2.
} {
  specialize rngl_ord_not_le as H3.
  apply H3 in H2.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  destruct H2 as (H2, _).
  now apply not_eq_sym.
}
Qed.

Theorem rngl_lt_irrefl :
  rngl_is_ordered T = true → ∀ a : T, ¬ (a < a)%L.
Proof.
intros * Hor a Ha.
unfold rngl_lt in Ha.
specialize (rngl_le_refl Hor a) as H1.
unfold rngl_le in H1.
destruct rngl_opt_leb; congruence.
Qed.

Theorem rngl_lt_asymm :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → ¬ b < a)%L.
Proof.
intros Hor * Hab Hba.
apply (rngl_lt_iff Hor) in Hab, Hba.
destruct Hab as (Hab, Hnab).
destruct Hba as (Hba, _).
now apply Hnab, (rngl_le_antisymm Hor).
Qed.

Theorem rngl_not_le :
  rngl_is_ordered T = true →
  ∀ a b, (¬ a ≤ b → a ≠ b ∧ b ≤ a)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as rr.
rewrite Hor in rr.
move rr after rp.
specialize rngl_ord_not_le as H.
apply H.
Qed.

Theorem rngl_lt_le_incl :
  rngl_is_ordered T = true →
  ∀ a b, (a < b → a ≤ b)%L.
Proof.
intros Hor * Hab.
now apply (rngl_lt_iff Hor) in Hab.
Qed.

Theorem rngl_nle_gt :
  ∀ a b, (b < a → ¬ (a ≤ b))%L.
Proof.
intros * Hab H1.
progress unfold rngl_lt in Hab.
progress unfold rngl_le in H1.
destruct rngl_opt_leb as [leb| ]; [ congruence | easy ].
Qed.

Theorem rngl_nle_gt_iff :
  rngl_is_ordered T = true →
  ∀ a b, (¬ (a ≤ b) ↔ b < a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply (rngl_not_le Hor) in Hab.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
} {
  intros H1.
  apply (rngl_lt_iff Hor) in Hab.
  destruct Hab as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_nlt_ge :
  ∀ a b, (b ≤ a → ¬ (a < b))%L.
Proof.
intros * Hab H1.
progress unfold rngl_le in Hab.
progress unfold rngl_lt in H1.
destruct rngl_opt_leb as [leb| ]; [ congruence | easy ].
Qed.

Theorem rngl_nlt_ge_iff :
  rngl_is_ordered T = true →
  ∀ a b, (¬ (a < b) ↔ b ≤ a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  destruct (rngl_le_dec Hor b a) as [H1| H1]; [ easy | ].
  exfalso; apply Hab.
  now apply (rngl_nle_gt_iff Hor).
} {
  intros H1.
  apply (rngl_lt_iff Hor) in H1.
  destruct H1 as (H2, H3).
  now apply H3, (rngl_le_antisymm Hor).
}
Qed.

Theorem rngl_lt_le_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b ≤ c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_le_trans Hor _ b); [ | easy ].
  now apply (rngl_lt_le_incl Hor).
} {
  intros H; subst c.
  now apply rngl_nle_gt in Hab.
}
Qed.

Theorem rngl_le_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a ≤ b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_lt_iff Hor).
split. {
  apply (rngl_le_trans Hor _ b); [ easy | ].
  now apply (rngl_lt_le_incl Hor).
} {
  intros H; subst c.
  now apply rngl_nle_gt in Hbc.
}
Qed.

Theorem rngl_lt_trans :
  rngl_is_ordered T = true →
   ∀ a b c : T, (a < b)%L → (b < c)%L → (a < c)%L.
Proof.
intros Hor * Hab Hbc.
apply (rngl_le_lt_trans Hor _ b); [ | easy ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_leb_gt :
  rngl_is_ordered T = true →
  ∀ a b, ((a ≤? b) = false ↔ b < a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply rngl_leb_nle in Hab.
  apply (rngl_not_le Hor) in Hab.
  apply (rngl_lt_iff Hor).
  split; [ easy | ].
  now apply not_eq_sym.
} {
  apply rngl_leb_nle.
  intros H1.
  now apply rngl_nle_gt in Hab.
}
Qed.

Theorem rngl_ltb_ge :
  ∀ a b, (b ≤ a → (a <? b) = false)%L.
Proof.
intros * Hab.
progress unfold rngl_le in Hab.
progress unfold rngl_ltb.
remember rngl_opt_leb as ol eqn:Hol.
symmetry in Hol.
destruct ol as [leb| ]; [ | easy ].
now apply Bool.negb_false_iff in Hab.
Qed.

Theorem rngl_ltb_ge_iff :
  rngl_is_ordered T = true →
  ∀ a b, ((a <? b) = false ↔ b ≤ a)%L.
Proof.
intros Hor *.
split; intros Hab. {
  apply rngl_ltb_nlt in Hab.
  now apply (rngl_nlt_ge_iff Hor) in Hab.
} {
  apply rngl_ltb_nlt.
  intros H1.
  now apply rngl_nlt_ge in Hab.
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
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = rngl_min b a.
Proof.
intros Hor *.
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
  apply (rngl_leb_gt Hor) in Hab, Hba.
  now apply (rngl_lt_asymm Hor) in Hba.
}
Qed.

Theorem rngl_max_comm :
  rngl_is_ordered T = true →
  ∀ a b, rngl_max a b = rngl_max b a.
Proof.
intros Hor *.
specialize (rngl_min_comm Hor a b) as H1.
progress unfold rngl_min in H1.
progress unfold rngl_max.
now destruct (a ≤? b)%L, (b ≤? a)%L.
Qed.

Theorem rngl_min_assoc :
  rngl_is_ordered T = true →
  ∀ a b c,
  rngl_min a (rngl_min b c) = rngl_min (rngl_min a b) c.
Proof.
intros Hor *.
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
apply (rngl_leb_gt Hor) in Hab, Hbc.
apply (rngl_lt_le_incl Hor) in Hbc.
apply (rngl_le_lt_trans Hor c) in Hab; [ | easy ].
apply (rngl_leb_gt Hor) in Hab.
now rewrite Hab.
Qed.

Theorem rngl_max_assoc :
  rngl_is_ordered T = true →
  ∀ a b c,
  rngl_max a (rngl_max b c) = rngl_max (rngl_max a b) c.
Proof.
intros Hor *.
specialize (rngl_min_assoc Hor a b c) as H1.
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
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = a ↔ (a ≤ b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
remember (b ≤? a)%L as ba eqn:Hba.
symmetry in Hab, Hba.
split; intros H1. {
  destruct ab; [ now apply rngl_leb_le in Hab | ].
  destruct ba; [ subst b; apply (rngl_le_refl Hor) | ].
  apply (rngl_leb_gt Hor) in Hab, Hba.
  apply (rngl_lt_le_incl Hor) in Hba.
  now apply rngl_nlt_ge in Hba.
} {
  destruct ab; [ easy | ].
  apply rngl_leb_le in H1.
  now rewrite Hab in H1.
}
Qed.

Theorem rngl_min_r_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_min a b = b ↔ (b ≤ a)%L.
Proof.
intros Hor *.
rewrite (rngl_min_comm Hor).
apply (rngl_min_l_iff Hor).
Qed.

Theorem rngl_max_l_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_max a b = a ↔ (b ≤ a)%L.
Proof.
intros Hor *.
specialize (rngl_min_l_iff Hor a b) as H1.
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
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_lt_le_incl Hor) in Hab.
  easy.
}
Qed.

Theorem rngl_max_r_iff :
  rngl_is_ordered T = true →
  ∀ a b, rngl_max a b = b ↔ (a ≤ b)%L.
Proof.
intros Hor *.
rewrite (rngl_max_comm Hor).
apply (rngl_max_l_iff Hor).
Qed.

Theorem rngl_min_glb_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (c < rngl_min a b ↔ c < a ∧ c < b)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
split; intros Hcab; [ | now destruct ab ].
destruct ab. {
  apply rngl_leb_le in Hab.
  split; [ easy | ].
  now apply (rngl_lt_le_trans Hor _ a).
}
apply (rngl_leb_gt Hor) in Hab.
split; [ | easy ].
now apply (rngl_lt_trans Hor _ b).
Qed.

Theorem rngl_min_le_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (rngl_min a b ≤ c ↔ a ≤ c ∨ b ≤ c)%L.
Proof.
intros Hor *.
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
apply (rngl_leb_gt Hor) in Hab.
apply (rngl_le_trans Hor _ a); [ | easy ].
now apply (rngl_lt_le_incl Hor) in Hab.
Qed.

Theorem rngl_min_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (rngl_min a b < c ↔ a < c ∨ b < c)%L.
Proof.
intros Hor *.
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
apply (rngl_leb_gt Hor) in Hab.
now apply (rngl_lt_trans Hor _ a).
Qed.

Theorem rngl_max_lt_iff :
  rngl_is_ordered T = true →
  ∀ a b c, (a < rngl_max b c ↔ a < b ∨ a < c)%L.
Proof.
intros Hor.
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
  apply (rngl_leb_gt Hor) in Hbc.
  now apply (rngl_lt_trans Hor _ c).
}
Qed.

Theorem rngl_le_min_l :
  rngl_is_ordered T = true →
  ∀ a b, (rngl_min a b ≤ a)%L.
Proof.
intros Hor *.
progress unfold rngl_min.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
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
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c → rngl_min a b ≤ rngl_min a c)%L.
Proof.
intros Hor * Hbc.
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
  apply (rngl_leb_gt Hor) in Hab.
  now apply (rngl_lt_le_incl Hor) in Hab.
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
  rngl_is_ordered T = true →
  ∀ a b, (b ≤ rngl_max a b)%L.
Proof.
intros Hor *.
progress unfold rngl_max.
remember (a ≤? b)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ apply (rngl_le_refl Hor) | ].
apply (rngl_leb_gt Hor) in Hc.
now apply (rngl_lt_le_incl Hor).
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

(* equality *)

Theorem rngl_eq_dec :
  rngl_has_eq_dec_or_order T = true →
  ∀ a b : T, {a = b} + {a ≠ b}.
Proof.
intros Heo *.
progress unfold rngl_has_eq_dec_or_order in Heo.
remember (rngl_has_eq_dec T) as ed eqn:Hed.
symmetry in Hed.
destruct ed. {
  progress unfold rngl_has_eq_dec in Hed.
  destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
  apply rngl_eq_dec.
}
cbn in Heo.
rename Heo into Hor.
destruct (rngl_le_dec Hor a b) as [Hab| Hab]. {
  destruct (rngl_le_dec Hor b a) as [Hba| Hba]. {
    left.
    now apply (rngl_le_antisymm Hor).
  }
  apply (rngl_nle_gt_iff Hor) in Hba.
  right.
  intros H; subst b.
  now apply (rngl_lt_irrefl Hor) in Hba.
}
apply (rngl_nle_gt_iff Hor) in Hab.
right.
intros H; subst b.
now apply (rngl_lt_irrefl Hor) in Hab.
Qed.

(* comparison *)

Definition rngl_compare a b :=
  if (a =? b)%L then Eq
  else if (a ≤? b)%L then Lt else Gt.

Theorem rngl_compare_eq_iff :
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Eq ↔ a = b.
Proof.
intros Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
symmetry in Hab.
destruct ab. {
  split; [ | easy ].
  now apply (rngl_eqb_eq Hed) in Hab.
} {
  destruct (a ≤? b)%L. {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  } {
    split; [ easy | ].
    now apply (rngl_eqb_neq Hed) in Hab.
  }
}
Qed.

Theorem rngl_compare_lt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Lt ↔ (a < b)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ | easy ].
    intros _.
    now apply (rngl_lt_iff Hor).
  } {
    split; [ easy | ].
    apply (rngl_leb_gt Hor) in Halb.
    intros H.
    now apply (rngl_lt_asymm Hor) in H.
  }
}
Qed.

Theorem rngl_compare_gt_iff :
  rngl_is_ordered T = true →
  rngl_has_eq_dec T = true →
  ∀ a b, rngl_compare a b = Gt ↔ (b < a)%L.
Proof.
intros Hor Hed *.
progress unfold rngl_compare.
remember (a =? b)%L as ab eqn:Hab.
remember (a ≤? b)%L as alb eqn:Halb.
symmetry in Hab, Halb.
destruct ab. {
  split; [ easy | intros H ].
  apply (rngl_eqb_eq Hed) in Hab.
  subst b.
  now apply (rngl_lt_irrefl Hor) in H.
} {
  apply (rngl_eqb_neq Hed) in Hab.
  destruct alb. {
    apply rngl_leb_le in Halb.
    split; [ easy | ].
    intros H.
    now apply rngl_nle_gt in H.
  } {
    now apply (rngl_leb_gt Hor) in Halb.
  }
}
Qed.

Theorem rngl_compare_refl :
  rngl_has_eq_dec T = true →
  ∀ a, rngl_compare a a = Eq.
Proof.
intros Hed *.
now apply (rngl_compare_eq_iff Hed).
Qed.

Notation "x ?= y" := (rngl_compare x y) : ring_like_scope.

End a.

Arguments rngl_eq_dec {T ro rp} Heo (a b)%_L.

Arguments rngl_le_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_le_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_le_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_trans {T ro rp} Hor (a b c)%_L.
Arguments rngl_lt_dec {T ro rp} Hor (a b)%_L.
Arguments rngl_min {T ro} (a b)%_L.
Arguments rngl_max {T ro} (a b)%_L.
