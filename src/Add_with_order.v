(** * Add_with_order

Theorems about addition, when order relation exists.

A ring-like has an order when the variable [rngl_is_ordered]
is [true].

See the module [[RingLike.Core]] for the general description
of the ring-like library.

In general, it is not necessary to import the present module. The
normal usage is to do:
<<
    Require Import RingLike.Core.
>>
which imports the present module and some other ones.
 *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.
Require Import Structures.
Require Import Order.
Require Import Add.

Class rngl_order_compatibility {T} {ro : ring_like_op T}
  (l1 l2 : T → T → Prop) :=
  { roc_dual_1 : ∀ a b, l1 a b ↔ ¬ l2 b a;
    roc_dual_2 : ∀ a b, l2 a b ↔ ¬ l1 b a;
    roc_of_lt : ∀ a b, (a < b)%L → l1 a b;
    roc_to_le : ∀ a b, l1 a b → (a ≤ b)%L;
    roc_mono_l : ∀ a b c, (a ≤ b)%L → l1 b c → l1 a c;
    roc_mono_r : ∀ a b c, l1 a b → (b ≤ c)%L → l1 a c;
    roc_add_ord_compat : ∀ a b c, l1 b c → (l1 (a + b) (a + c))%L }.

Arguments roc_add_ord_compat {T ro l1 l2} {rngl_order_compatibility}
  (a b c)%_L.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_order_compatibility_comm :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ l1 l2, rngl_order_compatibility l1 l2 → rngl_order_compatibility l2 l1.
Proof.
intros Hop Hor.
intros * H12.
split; [ apply roc_dual_2 | apply roc_dual_1 | | | | | ]. {
  intros * Hab.
  apply roc_dual_2.
  intros H.
  apply rngl_nle_gt in Hab.
  apply Hab; clear Hab.
  now apply roc_to_le.
} {
  intros * Hab.
  apply roc_dual_2 in Hab.
  apply (rngl_nlt_ge_iff Hor).
  intros H; apply Hab; clear Hab.
  now apply roc_of_lt.
} {
  intros * Hab Hbc.
  apply roc_dual_2 in Hbc; apply roc_dual_2.
  intros Hcb; apply Hbc; clear Hbc.
  now apply (roc_mono_r _ a).
} {
  intros * Hab Hbc.
  apply roc_dual_2 in Hab; apply roc_dual_2.
  intros Hca; apply Hab; clear Hab.
  now apply (roc_mono_l _ c).
}
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros * Hbc.
apply roc_dual_2 in Hbc; apply roc_dual_2.
intros H; apply Hbc; clear Hbc.
apply (roc_add_ord_compat (-a)) in H.
do 2 rewrite (rngl_add_opp_l Hop) in H.
do 2 rewrite (rngl_add_comm a) in H.
do 2 rewrite (rngl_add_sub Hos) in H.
easy.
Qed.

Theorem rngl_add_le_compat :
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L.
Proof.
intros Hor *.
specialize rngl_opt_ord as H.
rewrite Hor in H.
apply H.
Qed.

Theorem rngl_add_lt_mono :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T,
  (a < b → c + a < c + b)%L.
Proof.
intros Hos Hor * Hab.
apply (rngl_le_neq Hor) in Hab.
destruct Hab as (Hab, Haeb).
apply (rngl_le_neq Hor).
split. {
  apply (rngl_add_le_compat Hor); [ | easy ].
  apply (rngl_le_refl Hor).
} {
  intros H; apply Haeb; clear Haeb.
  now apply (rngl_add_cancel_l Hos) in H.
}
Qed.

(** *** rngl_order_compatibility works for pair (≤, <) *)

Theorem rngl_le_lt_comp :
  rngl_is_ordered T = true →
  rngl_order_compatibility rngl_le rngl_lt.
Proof.
intros Hor.
split. {
  intros.
  apply iff_sym, (rngl_nlt_ge_iff Hor).
} {
  intros.
  apply iff_sym, (rngl_nle_gt_iff Hor).
} {
  apply (rngl_lt_le_incl Hor).
} {
  easy.
} {
  intros.
  now apply (rngl_le_trans Hor _ b).
} {
  intros.
  now apply (rngl_le_trans Hor _ b).
} {
  intros.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | easy ].
}
Qed.

(** *** rngl_order_compatibility works for pair (<, ≤) *)

Theorem rngl_lt_le_comp :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  rngl_order_compatibility rngl_lt rngl_le.
Proof.
intros Hos Hor.
split. {
  intros.
  apply iff_sym, (rngl_nle_gt_iff Hor).
} {
  intros.
  apply iff_sym, (rngl_nlt_ge_iff Hor).
} {
  easy.
} {
  apply (rngl_lt_le_incl Hor).
} {
  intros.
  now apply (rngl_le_lt_trans Hor _ b).
} {
  intros.
  now apply (rngl_lt_le_trans Hor _ b).
} {
  intros.
  now apply (rngl_add_lt_mono Hos Hor).
}
Qed.

(** *** generic theorems: work for pair (≤, <) and for pair (<, ≤) *)

Theorem rngl_add_le_or_lt_compat_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → l1 c d → l1 (a + c) (b + d))%L.
Proof.
intros Hroc Hor * Hab Hbc.
apply (roc_mono_l _ (b + c))%L. {
  apply (rngl_add_le_compat Hor); [ easy | apply (rngl_le_refl Hor) ].
} {
  now apply roc_add_ord_compat.
}
Qed.

Theorem rngl_add_le_or_lt_compat_r {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_is_ordered T = true →
  ∀ a b c d, (l1 a b → c ≤ d → l1 (a + c) (b + d))%L.
Proof.
intros Hroc Hor * Hab Hbc.
rewrite (rngl_add_comm a), (rngl_add_comm b).
now apply (rngl_add_le_or_lt_compat_l Hroc Hor).
Qed.

Theorem rngl_add_le_or_lt_mono_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, l1 b c ↔ (l1 (a + b) (a + c))%L.
Proof.
intros Hroc Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; [ apply roc_add_ord_compat | ].
intros Hab.
apply (roc_add_ord_compat (-a) (a + b) (a + c)) in Hab.
do 2 rewrite (rngl_add_opp_l Hop) in Hab.
do 2 rewrite (rngl_add_comm a) in Hab.
do 2 rewrite (rngl_add_sub Hos) in Hab.
easy.
Qed.

Theorem rngl_add_le_or_lt_mono_r {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, l1 a b ↔ (l1 (a + c) (b + c))%L.
Proof.
intros Hroc Hop Hor *.
do 2 rewrite (rngl_add_comm _ c).
apply (rngl_add_le_or_lt_mono_l Hroc Hop Hor).
Qed.

Theorem rngl_le_or_lt_0_sub {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  (∀ a b, (l1 0 (b - a))%L ↔ l1 a b).
Proof.
intros Hroc Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros Hab. {
  apply (roc_add_ord_compat a) in Hab.
  rewrite rngl_add_0_r, rngl_add_comm in Hab.
  now rewrite (rngl_sub_add Hop) in Hab.
} {
  apply (roc_add_ord_compat (- a)) in Hab.
  do 2 rewrite (rngl_add_opp_l Hop) in Hab.
  now rewrite (rngl_sub_diag Hos) in Hab.
}
Qed.

Theorem rngl_le_or_lt_sub_0 {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, ((l1 (a - b) 0) ↔ l1 a b)%L.
Proof.
intros Hroc Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros Hab. {
  apply roc_dual_1 in Hab; apply roc_dual_1.
  intros Hba; apply Hab; clear Hab.
  apply (rngl_order_compatibility_comm Hop Hor) in Hroc.
  now apply (rngl_le_or_lt_0_sub Hroc Hop Hor).
}
apply (roc_add_ord_compat (-b))%L in Hab.
do 2 rewrite (rngl_add_opp_l Hop) in Hab.
now rewrite (rngl_sub_diag Hos) in Hab.
Qed.

Theorem rngl_opp_le_or_lt_compat {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, l1 a b ↔ (l1 (- b) (- a))%L.
Proof.
intros Hroc Hop Hor *.
split; intros Hxy. {
  apply (rngl_le_or_lt_0_sub Hroc Hop Hor).
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_comm, (rngl_add_opp_r Hop).
  now apply (rngl_le_or_lt_0_sub Hroc Hop Hor).
} {
  apply (rngl_le_or_lt_0_sub Hroc Hop Hor).
  progress unfold rngl_sub.
  rewrite Hop.
  rewrite rngl_add_comm.
  rewrite <- (rngl_opp_involutive Hop b).
  rewrite (rngl_add_opp_r Hop).
  now apply (rngl_le_or_lt_0_sub Hroc Hop Hor).
}
Qed.

Theorem rngl_le_or_lt_0_opp {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (l1 0 (- a) ↔ l1 a 0)%L.
Proof.
intros Hroc Hop Hor.
split; intros Ha. {
  apply (rngl_opp_le_or_lt_compat Hroc Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_or_lt_compat Hroc Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_le_or_lt_opp_0 {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (l1 (- a) 0 ↔ l1 0 a)%L.
Proof.
intros Hroc Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_le_or_lt_compat Hroc Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_or_lt_compat Hroc Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_sub_le_or_lt_mono_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (l1 a b ↔ l1 (c - b) (c - a))%L.
Proof.
intros Hroc Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
split; intros Hab. {
  progress unfold rngl_sub.
  rewrite Hop.
  apply roc_add_ord_compat.
  now apply -> (rngl_opp_le_or_lt_compat Hroc Hop Hor).
} {
  apply (roc_add_ord_compat (-c)) in Hab.
  do 2 rewrite (rngl_add_opp_l Hop) in Hab.
  do 2 rewrite (rngl_sub_sub_swap Hop _ _ c) in Hab.
  rewrite (rngl_sub_diag Hos) in Hab.
  do 2 rewrite (rngl_sub_0_l Hop) in Hab.
  now apply (rngl_opp_le_or_lt_compat Hroc Hop Hor).
}
Qed.

Theorem rngl_sub_le_or_lt_mono_r {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (l1 a b ↔ l1 (a - c) (b - c))%L.
Proof.
intros Hroc Hop Hor *.
progress unfold rngl_sub.
rewrite Hop.
apply (rngl_add_le_or_lt_mono_r Hroc Hop Hor).
Qed.

Theorem rngl_le_or_lt_add_sub_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (l1 (a + b) c ↔ l1 b (c - a))%L.
Proof.
intros Hroc Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
specialize (rngl_add_le_or_lt_compat_l Hroc Hor) as H1.
split; intros H2. {
  apply (H1 (-a) (-a))%L in H2; [ | apply (rngl_le_refl Hor) ].
  do 2 rewrite (rngl_add_opp_l Hop) in H2.
  rewrite rngl_add_comm in H2.
  now rewrite (rngl_add_sub Hos) in H2.
} {
  apply (H1 a a)%L in H2; [ | apply (rngl_le_refl Hor) ].
  rewrite (rngl_add_comm _ (c - a)) in H2.
  now rewrite (rngl_sub_add Hop) in H2.
}
Qed.

Theorem rngl_le_or_lt_add_sub_r {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (l1 (a + b) c ↔ l1 a (c - b))%L.
Proof.
intros Hroc Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_or_lt_add_sub_l Hroc Hop Hor).
Qed.

Theorem rngl_le_or_lt_sub_add_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (l1 (a - b) c ↔ l1 a (b + c))%L.
Proof.
intros Hroc Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
intros.
specialize (rngl_add_le_or_lt_compat_r Hroc Hor) as H1.
split; intros H2. {
  apply (H1 _ _ b b)%L in H2; [ | apply (rngl_le_refl Hor) ].
  now rewrite (rngl_sub_add Hop), rngl_add_comm in H2.
} {
  apply (H1 _ _ (-b) (-b))%L in H2; [ | apply (rngl_le_refl Hor) ].
  do 2 rewrite (rngl_add_opp_r Hop) in H2.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in H2.
}
Qed.

Theorem rngl_le_or_lt_sub_add_r {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (l1 (a - b) c ↔ l1 a (c + b))%L.
Proof.
intros Hroc Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_or_lt_sub_add_l Hroc Hop Hor).
Qed.

Theorem rngl_le_or_lt_add_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  ∀ a b, (l1 0 a → l1 b (a + b))%L.
Proof.
intros Hroc * Hza.
rewrite <- (rngl_add_0_l b) at 1.
do 2 rewrite (rngl_add_comm _ b).
now apply roc_add_ord_compat.
Qed.

Theorem rngl_le_or_lt_add_r {l1 l2} :
  rngl_order_compatibility l1 l2 →
  ∀ a b, (l1 0 b → l1 a (a + b))%L.
Proof.
intros Hroc * Hbz.
rewrite rngl_add_comm.
now apply (rngl_le_or_lt_add_l Hroc).
Qed.

Theorem rngl_sub_le_or_lt_compat {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (l1 a b → l1 c d → l1 (a - d) (b - c))%L.
Proof.
intros Hroc Hop Hor * Hab Hcd.
apply (roc_mono_l _ (a - c))%L. {
  apply roc_to_le.
  now apply (rngl_sub_le_or_lt_mono_l Hroc Hop Hor).
} {
  now apply (rngl_sub_le_or_lt_mono_r Hroc Hop Hor).
}
Qed.

Theorem rngl_le_or_lt_sub_l {l1 l2} :
  rngl_order_compatibility l1 l2 →
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (l1 0 b ↔ l1 (a - b) a)%L.
Proof.
intros Hroc Hop Hor *.
split; intros Hb. {
  apply (rngl_le_or_lt_sub_add_r Hroc Hop Hor).
  now apply (rngl_le_or_lt_add_r Hroc).
} {
  apply (rngl_le_or_lt_sub_add_l Hroc Hop Hor) in Hb.
  apply (rngl_add_le_or_lt_mono_r Hroc Hop Hor _ _ a).
  now rewrite rngl_add_0_l.
}
Qed.

(** *** specific theorems: version for ≤, followed with version for < *)

Theorem rngl_add_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%L.
Proof.
intros Hop Hor.
apply (rngl_add_le_or_lt_mono_l (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_add_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (b < c ↔ a + b < a + c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_add_le_or_lt_mono_l (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_add_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a + c ≤ b + c)%L.
Proof.
intros Hop Hor.
apply (rngl_add_le_or_lt_mono_r (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_add_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a < b ↔ a + c < b + c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_add_le_or_lt_mono_r (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 ≤ b - a ↔ a ≤ b)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_0_sub (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b - a ↔ a < b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_0_sub (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b ≤ 0 ↔ a ≤ b)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_sub_0 (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b < 0 ↔ a < b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_sub_0 (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_opp_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ b ↔ - b ≤ - a)%L.
Proof.
intros Hop Hor.
apply (rngl_opp_le_or_lt_compat (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_opp_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < b ↔ - b < - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_opp_le_or_lt_compat (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_opp_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ - a)%L ↔ (a ≤ 0)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_0_opp (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_opp_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < - a)%L ↔ (a < 0)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_0_opp (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_opp_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a ≤ 0)%L ↔ (0 ≤ a)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_opp_0 (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_opp_neg_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a < 0 ↔ 0 < a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_opp_0 (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_sub_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a ≤ b)%L ↔ (c - b ≤ c - a)%L.
Proof.
intros Hop Hor.
apply (rngl_sub_le_or_lt_mono_l (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_sub_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (c - b < c - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_sub_le_or_lt_mono_l (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_sub_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a - c ≤ b - c)%L.
Proof.
intros Hop Hor.
apply (rngl_sub_le_or_lt_mono_r (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_sub_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (a - c < b - c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_sub_le_or_lt_mono_r (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_add_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ b ≤ c - a)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_add_sub_l (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_add_lt_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ b < c - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_add_sub_l (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_add_le_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ a ≤ c - b)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_add_sub_r (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_add_lt_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ a < c - b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_add_sub_r (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_sub_le_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ b + c)%L.
Proof.
intros Hop Hor *.
apply (rngl_le_or_lt_sub_add_l (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_sub_lt_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < b + c)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_sub_add_l (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_sub_le_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ c + b)%L.
Proof.
intros Hop Hor *.
apply (rngl_le_or_lt_sub_add_r (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_sub_lt_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < c + b)%L.
Proof.
intros Hop Hor *.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_sub_add_r (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_add_le_lt_mono :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b)%L → (c < d)%L → (a + c < b + d)%L.
Proof.
intros Hop Hor * Hab Hcd.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
now apply (rngl_add_le_or_lt_compat_l (rngl_lt_le_comp Hos Hor) Hor).
Qed.

Theorem rngl_add_lt_le_mono :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b)%L → (c ≤ d)%L → (a + c < b + d)%L.
Proof.
intros Hos Hor * Hab Hcd.
now apply (rngl_add_le_or_lt_compat_r (rngl_lt_le_comp Hos Hor) Hor).
Qed.

Theorem rngl_le_add_l :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ a + b)%L.
Proof.
intros Hor * Hbz.
now apply (rngl_le_or_lt_add_l (rngl_le_lt_comp Hor)).
Qed.

Theorem rngl_lt_add_l :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (b < a + b)%L.
Proof.
intros Hos Hor * Hbz.
now apply (rngl_le_or_lt_add_l (rngl_lt_le_comp Hos Hor)).
Qed.

Theorem rngl_le_add_r :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b → a ≤ a + b)%L.
Proof.
intros Hor.
apply (rngl_le_or_lt_add_r (rngl_le_lt_comp Hor)).
Qed.

Theorem rngl_lt_add_r :
  rngl_has_opp_or_subt T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < b → a < a + b)%L.
Proof.
intros Hos Hor.
apply (rngl_le_or_lt_add_r (rngl_lt_le_comp Hos Hor)).
Qed.

Theorem rngl_sub_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a - d ≤ b - c)%L.
Proof.
intros Hop Hor.
apply (rngl_sub_le_or_lt_compat (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_sub_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b → c < d → a - d < b - c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_sub_le_or_lt_compat (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

Theorem rngl_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b ↔ a - b ≤ a)%L.
Proof.
intros Hop Hor.
apply (rngl_le_or_lt_sub_l (rngl_le_lt_comp Hor) Hop Hor).
Qed.

Theorem rngl_lt_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < b ↔ a - b < a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
apply (rngl_le_or_lt_sub_l (rngl_lt_le_comp Hos Hor) Hop Hor).
Qed.

(** *** other theorems *)

Theorem rngl_add_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b → c < d → a + c < b + d)%L.
Proof.
intros Hop Hor * Hab Hcd.
apply (rngl_lt_trans Hor _ (a + d)%L).
now apply (rngl_add_lt_mono_l Hop Hor).
now apply (rngl_add_lt_mono_r Hop Hor).
Qed.

Theorem rngl_leb_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, ((a - b ≤? 0) = (a ≤? b))%L.
Proof.
intros Hop Hor.
intros.
apply rngl_le_iff_leb_eq.
apply (rngl_le_sub_0 Hop Hor).
Qed.

Theorem rngl_eq_add_0 :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Hor * Haz Hbz Hab.
split. {
  apply (rngl_le_antisymm Hor) in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | easy ].
} {
  apply (rngl_le_antisymm Hor) in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  apply (rngl_add_le_compat Hor); [ easy | apply (rngl_le_refl Hor) ].
}
Qed.

(*********)

Theorem rngl_le_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (- a ≤ b ↔ 0 ≤ a + b)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_le_sub_le_add_l Hop Hor) in Hab.
now apply (rngl_le_sub_le_add_l Hop Hor) in Hab.
Qed.

Theorem rngl_le_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ - b ↔ a + b ≤ 0)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_le_add_le_sub_r Hop Hor) in Hab.
now apply (rngl_le_add_le_sub_r Hop Hor) in Hab.
Qed.

Theorem rngl_lt_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (- a < b ↔ 0 < a + b)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_lt_sub_lt_add_l Hop Hor) in Hab.
now apply (rngl_lt_sub_lt_add_l Hop Hor) in Hab.
Qed.

Theorem rngl_lt_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < - b ↔ a + b < 0)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
split; intros Hab.
now apply (rngl_lt_add_lt_sub_r Hop Hor) in Hab.
now apply (rngl_lt_add_lt_sub_r Hop Hor) in Hab.
Qed.

Theorem rngl_add_nonneg_nonneg :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a + b)%L.
Proof.
intros Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hor).
Qed.

Theorem rngl_add_pos_nonneg :
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → (0 ≤ b)%L → (0 < a + b)%L.
Proof.
intros Hor * Hza Hzb.
apply (rngl_lt_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hor).
Qed.

Theorem rngl_add_nonneg_pos :
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (0 < a + b)%L.
Proof.
intros Hor * Hza Hzb.
rewrite rngl_add_comm.
now apply (rngl_add_pos_nonneg Hor).
Qed.

Theorem rngl_add_nonpos_nonpos :
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → a + b ≤ 0)%L.
Proof.
intros Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ | easy ].
rewrite <- rngl_add_0_r.
apply (rngl_add_le_compat Hor); [ | easy ].
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_mul_nat_inj_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, ∀ i j, (0 ≤ a)%L → i ≤ j → (rngl_mul_nat a i ≤ rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz Hij.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j Hij.
induction i; intros; cbn. {
  induction j; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHj, Nat.le_0_l | ].
  now apply (rngl_le_add_l Hor).
}
destruct j; [ easy | ].
cbn.
apply Nat.succ_le_mono in Hij.
apply (rngl_add_le_mono_l Hop Hor).
now apply IHi.
Qed.

Theorem rngl_mul_nat_inj_le_iff :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i ≤ j ↔ (rngl_mul_nat a i ≤ rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; [ | intros; apply Nat.le_0_l ].
  intros H; clear H.
  induction j; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHj | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply rngl_nlt_ge in H; apply H; clear H.
  eapply (rngl_lt_le_trans Hor); [ apply Haz | ].
  apply (rngl_le_add_r Hor).
  clear IHi.
  induction i; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
cbn.
split; intros Hij. {
  apply Nat.succ_le_mono in Hij.
  apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
  now apply IHi.
} {
  apply -> Nat.succ_le_mono.
  apply (rngl_add_le_mono_l Hop Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_mul_nat_inj_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i < j ↔ (rngl_mul_nat a i < rngl_mul_nat a j)%L.
Proof.
intros Hop Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; intros Hj. 2: {
    destruct j; [ | apply Nat.lt_0_succ ].
    now apply (rngl_lt_irrefl Hor) in Hj.
  }
  induction j; [ easy | clear Hj ].
  cbn.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  destruct j; [ apply (rngl_le_refl Hor) | ].
  apply (rngl_lt_le_incl Hor), IHj.
  apply Nat.lt_0_succ.
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply rngl_nle_gt in H; apply H; clear H.
  eapply (rngl_le_trans Hor); [ apply (rngl_lt_le_incl Hor), Haz | ].
  apply (rngl_le_add_r Hor).
  clear IHi.
  induction i; [ apply (rngl_le_refl Hor) | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hor), (rngl_lt_le_incl Hor).
}
cbn.
split; intros Hij. {
  apply Nat.succ_lt_mono in Hij.
  apply (rngl_add_lt_mono_l Hop Hor).
  now apply IHi.
} {
  apply -> Nat.succ_lt_mono.
  apply (rngl_add_lt_mono_l Hop Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_abs_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_le_compat Hop Hor) in Haz.
  now rewrite (rngl_opp_0 Hop) in Haz.
} {
  apply (rngl_leb_gt Hor) in Haz.
  now apply (rngl_lt_le_incl Hor).
}
Qed.

Theorem rngl_abs_opp :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, rngl_abs (- a)%L = rngl_abs a.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (- a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
remember (a ≤? 0)%L as d eqn:Hd; symmetry in Hd.
destruct c. {
  apply rngl_leb_le in Hc.
  rewrite (rngl_opp_involutive Hop).
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_le_compat Hop Hor) in Hc.
  destruct d; [ | easy ].
  apply rngl_leb_le in Hd.
  apply (rngl_le_antisymm Hor) in Hd; [ | easy ].
  subst a.
  symmetry; apply (rngl_opp_0 Hop).
} {
  apply (rngl_leb_gt Hor) in Hc.
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_lt_compat Hop Hor) in Hc.
  destruct d; [ easy | ].
  apply (rngl_leb_gt Hor) in Hd.
  now apply (rngl_lt_asymm Hor) in Hd.
}
Qed.

Theorem rngl_le_abs_diag :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (a ≤ rngl_abs a)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hc.
apply (rngl_le_sub_0 Hop Hor).
rewrite (rngl_sub_opp_r Hop).
rewrite <- (rngl_add_0_l 0%L).
now apply (rngl_add_le_compat Hor).
Qed.

Theorem rngl_abs_nonneg_eq :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ a)%L → rngl_abs a = a.
Proof.
intros Hop Hor * Hza.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az; [ | easy ].
apply rngl_leb_le in Haz.
apply (rngl_le_antisymm Hor _ _ Hza) in Haz.
subst a.
apply (rngl_opp_0 Hop).
Qed.

Theorem rngl_abs_le :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (- x ≤ y ≤ x ↔ rngl_abs y ≤ x)%L.
Proof.
intros * Hop Hor *.
progress unfold rngl_abs.
split. {
  intros (Hxy, Hyx).
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz; [ | easy ].
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  intros Hyx.
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz. {
    apply rngl_leb_le in Hyz.
    split. {
      apply (rngl_opp_le_compat Hop Hor) in Hyx.
      now rewrite (rngl_opp_involutive Hop) in Hyx.
    } {
      apply (rngl_le_trans Hor _ 0%L); [ easy | ].
      apply (rngl_le_trans Hor _ (- y)%L); [ | easy ].
      apply (rngl_le_0_sub Hop Hor) in Hyz.
      progress unfold rngl_sub in Hyz.
      rewrite Hop in Hyz.
      now rewrite rngl_add_0_l in Hyz.
    }
  }
  split; [ | easy ].
  apply (rngl_leb_gt Hor) in Hyz.
  apply (rngl_lt_le_incl Hor).
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_le_trans Hor _ y)%L.
}
Qed.

Theorem rngl_le_abs :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (x ≤ y ∨ x ≤ -y)%L ↔ (x ≤ rngl_abs y)%L.
Proof.
intros Hop Hor.
intros.
split; intros Hxy. {
  destruct Hxy as [Hxy| Hxy]. {
    apply (rngl_le_trans Hor _ y); [ easy | ].
    apply (rngl_le_abs_diag Hop Hor).
  }
  apply (rngl_le_trans Hor _ (- y)); [ easy | ].
  rewrite <- (rngl_abs_opp Hop Hor).
  apply (rngl_le_abs_diag Hop Hor).
}
progress unfold rngl_abs in Hxy.
destruct (y ≤? 0)%L; [ now right | now left ].
Qed.

Theorem rngl_abs_lt :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x y, (- x < y < x ↔ rngl_abs y < x)%L.
Proof.
intros * Hop Hor *.
progress unfold rngl_abs.
split. {
  intros (Hxy, Hyx).
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz; [ | easy ].
  apply (rngl_opp_lt_compat Hop Hor).
  now rewrite (rngl_opp_involutive Hop).
} {
  intros Hyx.
  remember (y ≤? 0)%L as yz eqn:Hyz; symmetry in Hyz.
  destruct yz. {
    apply rngl_leb_le in Hyz.
    split. {
      apply (rngl_opp_lt_compat Hop Hor) in Hyx.
      now rewrite (rngl_opp_involutive Hop) in Hyx.
    } {
      apply (rngl_le_lt_trans Hor _ 0%L); [ easy | ].
      apply (rngl_le_lt_trans Hor _ (- y)%L); [ | easy ].
      apply (rngl_le_0_sub Hop Hor) in Hyz.
      progress unfold rngl_sub in Hyz.
      rewrite Hop in Hyz.
      now rewrite rngl_add_0_l in Hyz.
    }
  }
  split; [ | easy ].
  apply (rngl_leb_gt Hor) in Hyz.
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_lt_trans Hor _ y)%L.
}
Qed.

Theorem rngl_abs_sub_comm :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, rngl_abs (a - b)%L = rngl_abs (b - a)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_abs_opp Hop Hor).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_abs_nonpos_eq :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a : T, (a ≤ 0)%L → rngl_abs a = (- a)%L.
Proof.
intros Hop Hor * Haz.
rewrite <- (rngl_opp_involutive Hop a) at 1.
rewrite (rngl_abs_opp Hop Hor).
apply (rngl_abs_nonneg_eq Hop Hor).
rewrite <- (rngl_opp_0 Hop).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_abs_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ x, (x ≠ 0 → 0 < rngl_abs x)%L.
Proof.
intros Hop Hor * Hxz.
apply (rngl_le_neq Hor).
split. 2: {
  apply not_eq_sym.
  intros H; apply Hxz; clear Hxz.
  progress unfold rngl_abs in H.
  remember (x ≤? 0)%L as xz eqn:Hxz; symmetry in Hxz.
  destruct xz; [ | easy ].
  apply (f_equal rngl_opp) in H.
  rewrite (rngl_opp_involutive Hop) in H.
  now rewrite (rngl_opp_0 Hop) in H.
}
apply (rngl_abs_nonneg Hop Hor).
Qed.

Theorem rngl_abs_triangle :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (rngl_abs (a + b) ≤ rngl_abs a + rngl_abs b)%L.
Proof.
intros Hop Hor *.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
remember (b ≤? 0)%L as bz eqn:Hbz; symmetry in Hbz.
remember (a + b ≤? 0)%L as abz eqn:Habz; symmetry in Habz.
destruct abz. {
  apply rngl_leb_le in Habz.
  destruct az. {
    apply rngl_leb_le in Haz.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
    destruct bz; [ apply (rngl_le_refl Hor) | ].
    apply (rngl_leb_gt Hor) in Hbz.
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Haz.
  destruct bz. {
    rewrite rngl_add_comm.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    rewrite rngl_add_comm.
    apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
    apply (rngl_lt_le_incl Hor).
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt Hor) in Hbz.
  apply rngl_nlt_ge in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hor).
  now apply (rngl_lt_le_incl Hor).
}
apply (rngl_leb_gt Hor) in Habz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply rngl_nle_gt in Habz.
    exfalso; apply Habz; clear Habz.
    rewrite <- rngl_add_0_r.
    now apply (rngl_add_le_compat Hor).
  }
  apply (rngl_add_le_compat Hor); [ | apply (rngl_le_refl Hor) ].
  apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  now rewrite (rngl_opp_0 Hop).
}
apply (rngl_leb_gt Hor) in Haz.
apply (rngl_add_le_compat Hor); [ apply (rngl_le_refl Hor) | ].
destruct bz; [ | apply (rngl_le_refl Hor) ].
apply rngl_leb_le in Hbz.
apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_involutive Hop).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_add_neg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < 0)%L → (b ≤ 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
eapply (rngl_lt_le_trans Hor); [ | apply Hbz ].
apply (rngl_lt_add_lt_sub_r Hop Hor).
now rewrite (rngl_sub_diag Hos).
Qed.

Theorem rngl_add_nonpos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0)%L → (b < 0)%L → (a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
rewrite rngl_add_comm.
now apply (rngl_add_neg_nonpos Hop Hor).
Qed.

Theorem rngl_leb_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (-a ≤? b)%L = (-b ≤? a)%L.
Proof.
intros Hop Hor *.
remember (-a ≤? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_l Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_r Hop Hor).
}
Qed.

Theorem rngl_leb_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤? -b)%L = (b ≤? -a)%L.
Proof.
intros Hop Hor *.
remember (a ≤? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_leb_le in Hab.
  apply rngl_leb_le.
  apply (rngl_le_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_le_opp_r Hop Hor) in Hab.
} {
  apply (rngl_leb_gt Hor) in Hab.
  apply (rngl_leb_gt Hor).
  apply (rngl_lt_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_l Hop Hor).
}
Qed.

Theorem rngl_leb_0_opp :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤? - a)%L = (a ≤? 0)%L.
Proof.
intros Hop Hor *.
rewrite (rngl_leb_opp_r Hop Hor).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_ltb_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (-a <? b)%L = (-b <? a)%L.
Proof.
intros Hop Hor *.
remember (-a <? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_ltb_lt in Hab.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_l Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge_iff Hor) in Hab.
  apply rngl_ltb_ge.
  apply (rngl_le_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_r Hop Hor).
}
Qed.

Theorem rngl_ltb_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a <? -b)%L = (b <? -a)%L.
Proof.
intros Hop Hor *.
remember (a <? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply rngl_ltb_lt in Hab.
  apply rngl_ltb_lt.
  apply (rngl_lt_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_r Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge_iff Hor) in Hab.
  apply rngl_ltb_ge.
  apply (rngl_le_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_l Hop Hor).
}
Qed.

Theorem rngl_archimedean_ub :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a < b)%L →
  ∃ₜ n : nat, (rngl_mul_nat a n ≤ b < rngl_mul_nat a (n + 1))%L.
Proof.
intros Har Hor * (Ha, Hab).
specialize rngl_opt_archimedean as H1.
rewrite Har, Hor in H1; cbn in H1.
specialize (H1 a b Ha).
destruct H1 as (m, Hm).
induction m. {
  exfalso; cbn in Hm.
  apply rngl_nle_gt in Hm.
  apply Hm; clear Hm.
  now apply (rngl_le_trans Hor _ a); apply (rngl_lt_le_incl Hor).
}
destruct (rngl_le_dec Hor (rngl_mul_nat a m) b) as [Hba| Hba]. {
  now exists m; rewrite Nat.add_1_r.
}
apply (rngl_nle_gt_iff Hor) in Hba.
now apply IHm.
Qed.

Theorem rngl_archimedean :
  rngl_is_archimedean T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → ∃ₜ n, (b < rngl_mul_nat a n)%L.
Proof.
intros Har Hor.
specialize rngl_opt_archimedean as H1.
now rewrite Har, Hor in H1.
Qed.

End a.

Arguments rngl_abs_nonneg_eq {T ro rp} Hop Hor a%_L.
Arguments rngl_add_le_mono_l {T ro rp} Hop Hor (a b c)%_L.
Arguments rngl_add_lt_mono_l {T ro rp} Hop Hor (a b c)%_L.
Arguments rngl_le_add_r {T ro rp} Hor (a b)%_L Hb.

(** ** Order Compatibility (old version to be removed one day)

This structure, [order_compatibility], captures the key symmetry
between the two order relations [rngl_le] (≤) and [rngl_lt] (<) in
a ring-like structure.

## Core Idea

- Duality: If [l1 a b] holds, then [¬ l2 b a].

- Left Monotonicity: If [a ≤ b] and [l2 b c] then [l2 a c].

- Right Monotonicity: If [l2 a b] and [b ≤ c] then [l2 a c].

- Optional (requires additive inverses):

  - [l1 (a + b) c ↔ l1 b (c - a)]
  - [l2 a (b + c) ↔ l2 (a - b) c]

## Example

For [l1 = rngl_le] (≤) and [l2 = rngl_lt] (<), this recovers:

  - [a + b ≤ c ↔ b ≤ c - a]
  - [a + b < c ↔ b < c - a]

## Benefit

Capturing this compatibility reduces the need to duplicate
proofs for ≤ and <, making reasoning in ordered ring-like
structures more concise and systematic.
*)

(* previous version that should be removed if new version
   seems to be better *)
Class rngl_order_compatibility' {T} {ro : ring_like_op T}
  (l1 l2 : T → T → Prop) :=
  { roc_dual_1' : ∀ a b, l1 a b ↔ ¬ l2 b a;
    roc_dual_2' : ∀ a b, l2 a b ↔ ¬ l1 b a;
    roc_mono_l_1 : ∀ a b c, (a ≤ b)%L → l1 b c → l1 a c;
    roc_mono_r_1 : ∀ a b c, l1 a b → (b ≤ c)%L → l1 a c;
    roc_of_lt' : ∀ a b, (a < b)%L → l1 a b;
    roc_to_le' : ∀ a b, l1 a b → (a ≤ b)%L;
    roc_opt_add_sub_l_1 :
      if rngl_has_opp T then ∀ a b c, l1 (a + b)%L c ↔ l1 b (c - a)%L
      else not_applicable;
    roc_opt_add_sub_r_1 :
      if rngl_has_opp T then ∀ a b c, l1 a (b + c)%L ↔ l1 (a - b)%L c
      else not_applicable }.

Theorem roc_add_sub_l_1 {T} {ro : ring_like_op T} {l1 l2}
  {Hroc : rngl_order_compatibility' l1 l2} :
  rngl_has_opp T = true →
  ∀ a b c, l1 (a + b)%L c ↔ l1 b (c - a)%L.
Proof.
intros Hop *.
specialize (@roc_opt_add_sub_l_1 T ro l1 l2 Hroc) as H1.
now rewrite Hop in H1.
Qed.

Theorem roc_add_sub_r_1 {T} {ro : ring_like_op T} {l1 l2}
  {Hroc : rngl_order_compatibility' l1 l2} :
  rngl_has_opp T = true →
  ∀ a b c, l1 a (b + c)%L ↔ l1 (a - b)%L c.
Proof.
intros Hop *.
specialize (@roc_opt_add_sub_r_1 T ro l1 l2 Hroc) as H1.
now rewrite Hop in H1.
Qed.

Theorem roc_mono_l_2 {T} {ro : ring_like_op T} {l1 l2}
  {Hroc : rngl_order_compatibility' l1 l2} :
  ∀ a b c, (a ≤ b)%L → l2 b c → l2 a c.
Proof.
intros * Hab Hbc.
apply roc_dual_2' in Hbc.
apply roc_dual_2'.
intros Hca; apply Hbc; clear Hbc.
now apply (roc_mono_r_1 _ a).
Qed.

Theorem roc_mono_r_2 {T} {ro : ring_like_op T} {l1 l2}
  {Hroc : rngl_order_compatibility' l1 l2} :
  ∀ a b c, l2 a b → (b ≤ c)%L → l2 a c.
Proof.
intros * Hab Hbc.
apply roc_dual_2' in Hab.
apply roc_dual_2'.
intros Hca; apply Hab; clear Hab.
now apply (roc_mono_l_1 _ c).
Qed.

Theorem roc_add_sub_l_2 {T} {ro : ring_like_op T} {l1 l2}
  {Hroc : rngl_order_compatibility' l1 l2} :
  rngl_has_opp T = true →
  ∀ a b c, l2 (a + b)%L c ↔ l2 b (c - a)%L.
Proof.
intros Hop *.
split; intros H1. {
  apply roc_dual_2' in H1.
  apply roc_dual_2'.
  intros H2; apply H1; clear H1.
  now apply (roc_add_sub_r_1 Hop).
} {
  apply roc_dual_2' in H1.
  apply roc_dual_2'.
  intros H2; apply H1; clear H1.
  now apply (roc_add_sub_r_1 Hop).
}
Qed.

Theorem roc_add_sub_r_2 {T} {ro : ring_like_op T} {l1 l2}
  {Hroc : rngl_order_compatibility' l1 l2} :
  rngl_has_opp T = true →
  ∀ a b c, l2 a (b + c)%L ↔ l2 (a - b)%L c.
Proof.
intros Hop *.
split; intros H1. {
  apply roc_dual_2' in H1.
  apply roc_dual_2'.
  intros H2; apply H1; clear H1.
  now apply (roc_add_sub_l_1 Hop).
} {
  apply roc_dual_2' in H1.
  apply roc_dual_2'.
  intros H2; apply H1; clear H1.
  now apply (roc_add_sub_l_1 Hop).
}
Qed.

Theorem rngl_le_lt_compatibility' {T}
    {ro : ring_like_op T} {rp : ring_like_prop T} :
  rngl_is_ordered T = true →
  rngl_order_compatibility' rngl_le rngl_lt.
Proof.
intros Hor.
split. {
  intros.
  apply iff_sym, (rngl_nlt_ge_iff Hor).
} {
  intros.
  apply iff_sym, (rngl_nle_gt_iff Hor).
} {
  intros.
  eapply (rngl_le_trans Hor); [ eassumption | easy ].
} {
  intros.
  eapply (rngl_le_trans Hor); [ eassumption | easy ].
} {
  apply (rngl_lt_le_incl Hor).
} {
  easy.
} {
  intros.
  remember (rngl_has_opp T) as op eqn:Hop.
  symmetry in Hop.
  destruct op; [ | easy ].
  now apply (rngl_le_add_le_sub_l Hop Hor).
} {
  intros.
  remember (rngl_has_opp T) as op eqn:Hop.
  symmetry in Hop.
  destruct op; [ | easy ].
  intros.
  apply iff_sym, (rngl_le_sub_le_add_l Hop Hor).
}
Qed.

Theorem rngl_lt_le_compatibility' {T}
    {ro : ring_like_op T} {rp : ring_like_prop T} :
  rngl_is_ordered T = true →
  rngl_order_compatibility' rngl_lt rngl_le.
Proof.
intros Hor.
split. {
  intros.
  apply iff_sym, (rngl_nle_gt_iff Hor).
} {
  intros.
  apply iff_sym, (rngl_nlt_ge_iff Hor).
} {
  intros.
  eapply (rngl_le_lt_trans Hor); [ eassumption | easy ].
} {
  intros.
  eapply (rngl_lt_le_trans Hor); [ eassumption | easy ].
} {
  easy.
} {
  apply (rngl_lt_le_incl Hor).
} {
  intros.
  remember (rngl_has_opp T) as op eqn:Hop.
  symmetry in Hop.
  destruct op; [ | easy ].
  now apply (rngl_lt_add_lt_sub_l Hop Hor).
} {
  intros.
  remember (rngl_has_opp T) as op eqn:Hop.
  symmetry in Hop.
  destruct op; [ | easy ].
  intros.
  apply iff_sym, (rngl_lt_sub_lt_add_l Hop Hor).
}
Qed.
