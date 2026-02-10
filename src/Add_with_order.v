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
Require Import Stdlib.Arith.Arith.
Require Import Utf8 Structures Order Add.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Tactic Notation "pauto" := progress auto.
Hint Resolve rngl_le_refl : core.

Theorem rngl_add_le_mono_l :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (b ≤ c ↔ a + b ≤ a + c)%L.
Proof.
intros Hos Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
specialize rngl_ord_add_le_mono_l as H1.
now rewrite Hos in H1.
Qed.

Theorem rngl_add_lt_mono_l :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (b < c ↔ a + b < a + c)%L.
Proof.
intros Hos Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
intros.
split; intros Hbc. {
  apply rngl_le_neq.
  split; [ now apply H1, rngl_lt_le_incl | ].
  intros H.
  apply (rngl_add_cancel_l Hos) in H.
  subst.
  now apply rngl_lt_irrefl in Hbc.
} {
  apply rngl_le_neq.
  split; [ now apply (H1 a), rngl_lt_le_incl | ].
  intros H.
  subst.
  now apply rngl_lt_irrefl in Hbc.
}
Qed.

Theorem rngl_add_le_mono :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a + c ≤ b + d)%L.
Proof.
intros Hos Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros * Hab Hcd.
apply (rngl_le_trans Hor _ (a + d)).
now apply (rngl_add_le_mono_l Hos Hor).
do 2 rewrite (rngl_add_comm _ d).
now apply (rngl_add_le_mono_l Hos Hor).
Qed.

Theorem rngl_add_le_mono_r :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a + c ≤ b + c)%L.
Proof.
intros Hos Hor.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
split; intros H. {
  do 2 rewrite (rngl_add_comm _ c).
  now apply (rngl_add_le_mono_l Hos Hor).
} {
  do 2 rewrite (rngl_add_comm _ c) in H.
  now apply (rngl_add_le_mono_l Hos Hor) in H.
}
Qed.

Theorem rngl_add_lt_mono_r :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a < b ↔ a + c < b + c)%L.
Proof.
intros Hos Hor *.
do 2 rewrite (rngl_add_comm _ c).
apply (rngl_add_lt_mono_l Hos Hor).
Qed.

Theorem rngl_le_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 ≤ b - a ↔ a ≤ b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
split; intros Hab. {
  apply H1 with (a := (-a)%L).
  rewrite (rngl_add_opp_l Hop).
  rewrite (rngl_sub_diag Hos).
  now rewrite (rngl_add_opp_l Hop).
} {
  apply H1 with (a := a).
  rewrite rngl_add_0_r.
  rewrite rngl_add_comm.
  now rewrite (rngl_sub_add Hop).
}
Qed.

Theorem rngl_lt_0_sub :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < b - a ↔ a < b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
progress unfold rngl_lt.
split; intros Hab. {
  split. {
    apply H1 with (a := (-a)%L).
    rewrite (rngl_add_opp_l Hop).
    rewrite (rngl_sub_diag Hos).
    now rewrite (rngl_add_opp_l Hop).
  }
  intros H; subst b.
  now rewrite (rngl_sub_diag Hos) in Hab.
} {
  split. {
    apply H1 with (a := a).
    rewrite rngl_add_0_r, rngl_add_comm.
    now rewrite (rngl_sub_add Hop).
  }
  intros H.
  apply (f_equal (rngl_add a)) in H.
  rewrite rngl_add_0_r, rngl_add_comm in H.
  rewrite (rngl_sub_add Hop) in H.
  now subst b.
}
Qed.

Theorem rngl_le_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b ≤ 0 ↔ a ≤ b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
split; intros Hab. {
  apply H1 with (a := (-b)%L).
  rewrite (rngl_add_opp_l Hop).
  now rewrite (rngl_add_opp_diag_l Hop).
} {
  apply H1 with (a := b).
  rewrite rngl_add_0_r.
  rewrite rngl_add_comm.
  now rewrite (rngl_sub_add Hop).
}
Qed.

Theorem rngl_lt_sub_0 :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a - b < 0 ↔ a < b)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
progress unfold rngl_lt.
split; intros Hab. {
  split. {
    apply H1 with (a := (-b)%L).
    rewrite (rngl_add_opp_l Hop).
    now rewrite (rngl_add_opp_diag_l Hop).
  }
  intros H; subst b.
  now rewrite (rngl_sub_diag Hos) in Hab.
} {
  split. {
    apply H1 with (a := b).
    rewrite rngl_add_0_r, rngl_add_comm.
    now rewrite (rngl_sub_add Hop).
  }
  intros H.
  apply (f_equal (rngl_add b)) in H.
  rewrite rngl_add_0_r, rngl_add_comm in H.
  now rewrite (rngl_sub_add Hop) in H.
}
Qed.

Theorem rngl_opp_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ b ↔ - b ≤ - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
split; intros Hab. {
  apply H1 with (a := (a + b)%L).
  do 2 rewrite (rngl_add_opp_r Hop).
  rewrite (rngl_add_sub Hos), rngl_add_comm.
  now rewrite (rngl_add_sub Hos).
} {
  apply H1 with (a := (a + b)%L) in Hab.
  do 2 rewrite (rngl_add_opp_r Hop) in Hab.
  rewrite (rngl_add_sub Hos), rngl_add_comm in Hab.
  now rewrite (rngl_add_sub Hos) in Hab.
}
Qed.

Theorem rngl_opp_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < b ↔ - b < - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
specialize (rngl_opt_ord T) as rr.
rewrite Hor in rr.
move rr before rp.
intros.
specialize rngl_ord_add_le_mono_l as H1.
rewrite Hos in H1.
progress unfold rngl_lt.
split; intros Hab. {
  split. {
    apply H1 with (a := (a + b)%L).
    do 2 rewrite (rngl_add_opp_r Hop).
    rewrite (rngl_add_sub Hos), rngl_add_comm.
    now rewrite (rngl_add_sub Hos).
  }
  intros H.
  apply (f_equal rngl_opp) in H.
  do 2 rewrite (rngl_opp_involutive Hop) in H.
  now subst b.
} {
  destruct Hab as (Hab, Hba).
  apply H1 with (a := (a + b)%L) in Hab.
  do 2 rewrite (rngl_add_opp_r Hop) in Hab.
  rewrite (rngl_add_sub Hos), rngl_add_comm in Hab.
  rewrite (rngl_add_sub Hos) in Hab.
  split; [ easy | ].
  intros H; apply Hba; clear Hba; symmetry.
  now apply (f_equal rngl_opp) in H.
}
Qed.

Theorem rngl_opp_nonneg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 ≤ - a)%L ↔ (a ≤ 0)%L.
Proof.
intros Hop Hor.
split; intros Ha. {
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_pos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < - a)%L ↔ (a < 0)%L.
Proof.
intros Hop Hor.
split; intros Ha. {
  apply (rngl_opp_lt_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_lt_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_nonpos_nonneg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a ≤ 0)%L ↔ (0 ≤ a)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_le_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_le_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_opp_neg_pos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (- a < 0 ↔ 0 < a)%L.
Proof.
intros Hop Hor *.
split; intros Ha. {
  apply (rngl_opp_lt_compat Hop Hor).
  now rewrite (rngl_opp_0 Hop).
} {
  apply (rngl_opp_lt_compat Hop Hor) in Ha.
  now rewrite (rngl_opp_0 Hop) in Ha.
}
Qed.

Theorem rngl_sub_le_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a ≤ b)%L ↔ (c - b ≤ c - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Hab. {
  do 2 rewrite <- (rngl_add_opp_r Hop).
  apply (rngl_add_le_mono_l Hos Hor).
  now apply -> (rngl_opp_le_compat Hop Hor).
} {
  do 2 rewrite <- (rngl_add_opp_r Hop) in Hab.
  apply (rngl_add_le_mono_l Hos Hor) in Hab.
  now apply (rngl_opp_le_compat Hop Hor) in Hab.
}
Qed.

Theorem rngl_sub_lt_mono_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (c - b < c - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Hab. {
  do 2 rewrite <- (rngl_add_opp_r Hop).
  apply (rngl_add_lt_mono_l Hos Hor).
  now apply -> (rngl_opp_lt_compat Hop Hor).
} {
  do 2 rewrite <- (rngl_add_opp_r Hop) in Hab.
  apply (rngl_add_lt_mono_l Hos Hor) in Hab.
  now apply (rngl_opp_lt_compat Hop Hor) in Hab.
}
Qed.

Theorem rngl_sub_le_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a ≤ b ↔ a - c ≤ b - c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Hab. {
  do 2 rewrite <- (rngl_add_opp_r Hop).
  now apply (rngl_add_le_mono_r Hos Hor).
} {
  do 2 rewrite <- (rngl_add_opp_r Hop) in Hab.
  now apply (rngl_add_le_mono_r Hos Hor) in Hab.
}
Qed.

Theorem rngl_sub_lt_mono_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c : T, (a < b)%L ↔ (a - c < b - c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Hab. {
  do 2 rewrite <- (rngl_add_opp_r Hop).
  now apply (rngl_add_lt_mono_r Hos Hor).
} {
  do 2 rewrite <- (rngl_add_opp_r Hop) in Hab.
  now apply (rngl_add_lt_mono_r Hos Hor) in Hab.
}
Qed.

Theorem rngl_le_add_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ b ≤ c - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Habc. {
  apply (rngl_sub_le_mono_r Hop Hor _ _ a) in Habc.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in Habc.
} {
  apply (rngl_sub_le_mono_r Hop Hor _ _ a).
  now rewrite rngl_add_comm, (rngl_add_sub Hos).
}
Qed.

Theorem rngl_lt_add_lt_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ b < c - a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Habc. {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ a) in Habc.
  now rewrite rngl_add_comm, (rngl_add_sub Hos) in Habc.
} {
  apply (rngl_sub_lt_mono_r Hop Hor _ _ a).
  now rewrite rngl_add_comm, (rngl_add_sub Hos).
}
Qed.

Theorem rngl_le_add_le_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b ≤ c ↔ a ≤ c - b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_add_le_sub_l Hop Hor).
Qed.

Theorem rngl_lt_add_lt_sub_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a + b < c ↔ a < c - b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_lt_add_lt_sub_l Hop Hor).
Qed.

Theorem rngl_le_sub_le_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ b + c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Habc. {
  apply (rngl_add_le_mono_r Hos Hor _ _ b) in Habc.
  now rewrite (rngl_sub_add Hop), rngl_add_comm in Habc.
} {
  apply (rngl_add_le_mono_r Hos Hor _ _ b).
  now rewrite (rngl_sub_add Hop), rngl_add_comm.
}
Qed.

Theorem rngl_lt_sub_lt_add_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < b + c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
split; intros Habc. {
  apply (rngl_add_lt_mono_r Hos Hor _ _ b) in Habc.
  now rewrite (rngl_sub_add Hop), rngl_add_comm in Habc.
} {  
  apply (rngl_add_lt_mono_r Hos Hor _ _ b).
  now rewrite (rngl_sub_add Hop), rngl_add_comm.
}
Qed.

Theorem rngl_le_sub_le_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b ≤ c ↔ a ≤ c + b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_le_sub_le_add_l Hop Hor).
Qed.

Theorem rngl_lt_sub_lt_add_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c, (a - b < c ↔ a < c + b)%L.
Proof.
intros Hop Hor *.
rewrite rngl_add_comm.
apply (rngl_lt_sub_lt_add_l Hop Hor).
Qed.

Theorem rngl_add_le_lt_mono :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b)%L → (c < d)%L → (a + c < b + d)%L.
Proof.
intros Hos Hor * Hab Hcd.
apply (rngl_le_lt_trans Hor _ (b + c)).
now apply (rngl_add_le_mono_r Hos Hor).
now apply (rngl_add_lt_mono_l Hos Hor).
Qed.

Theorem rngl_add_lt_le_mono :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b)%L → (c ≤ d)%L → (a + c < b + d)%L.
Proof.
intros Hos Hor * Hab Hcd.
apply (rngl_lt_le_trans Hor _ (b + c)).
now apply (rngl_add_lt_mono_r Hos Hor).
now apply (rngl_add_le_mono_l Hos Hor).
Qed.

Theorem rngl_le_add_l :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → b ≤ a + b)%L.
Proof.
intros Hos Hor * Hbz.
rewrite <- (rngl_add_0_l b) at 1.
do 2 rewrite (rngl_add_comm _ b).
now apply (rngl_add_le_mono_l Hos Hor).
Qed.

Theorem rngl_lt_add_l :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b : T, (0 < a)%L → (b < a + b)%L.
Proof.
intros Hos Hor * Hbz.
rewrite <- (rngl_add_0_l b) at 1.
now apply (rngl_add_lt_mono_r Hos Hor).
Qed.

Theorem rngl_le_add_r :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b → a ≤ a + b)%L.
Proof.
intros Hos Hor * Hzb.
rewrite <- (rngl_add_0_r a) at 1.
now apply (rngl_add_le_mono_l Hos Hor).
Qed.

Theorem rngl_lt_add_r :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < b → a < a + b)%L.
Proof.
intros Hos Hor *.
rewrite rngl_add_comm.
apply (rngl_lt_add_l Hos Hor).
Qed.

Theorem rngl_sub_le_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a ≤ b → c ≤ d → a - d ≤ b - c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hab Hcd.
do 2 rewrite <- (rngl_add_opp_r Hop).
apply (rngl_add_le_mono Hos Hor); [ easy | ].
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_sub_lt_compat :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b → c < d → a - d < b - c)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros * Hab Hcd.
do 2 rewrite <- (rngl_add_opp_r Hop).
apply (rngl_add_lt_le_mono Hos Hor); [ easy | ].
now apply -> (rngl_opp_lt_compat Hop Hor).
Qed.

Theorem rngl_le_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ b ↔ a - b ≤ a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros *.
split; intros Hb. {
  apply (rngl_le_sub_le_add_l Hop Hor).
  now apply (rngl_le_add_l Hos Hor).
} {
  apply (rngl_le_sub_le_add_l Hop Hor) in Hb.
  apply (rngl_add_le_mono_l Hos Hor a).
  now rewrite rngl_add_0_r, rngl_add_comm.
}
Qed.

Theorem rngl_lt_sub_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < b ↔ a - b < a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros *.
split; intros Hb. {
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  now apply (rngl_lt_add_l Hos Hor).
} {
  apply (rngl_lt_sub_lt_add_l Hop Hor) in Hb.
  apply (rngl_add_lt_mono_l Hos Hor a).
  now rewrite rngl_add_0_r, rngl_add_comm.
}
Qed.

Theorem rngl_le_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (- a ≤ b ↔ 0 ≤ a + b)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
apply (rngl_le_sub_le_add_l Hop Hor).
Qed.

Theorem rngl_lt_opp_l :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (- a < b ↔ 0 < a + b)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
apply (rngl_lt_sub_lt_add_l Hop Hor).
Qed.

Theorem rngl_le_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ - b ↔ a + b ≤ 0)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
apply iff_sym.
apply (rngl_le_add_le_sub_r Hop Hor).
Qed.

Theorem rngl_lt_opp_r :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < - b ↔ a + b < 0)%L.
Proof.
intros Hop Hor *.
rewrite <- (rngl_sub_0_l Hop).
apply iff_sym.
apply (rngl_lt_add_lt_sub_r Hop Hor).
Qed.

Theorem rngl_le_0_add :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → 0 ≤ a + b)%L.
Proof.
intros Hos Hor.
intros * Ha Hb.
apply (rngl_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hos Hor).
Qed.

Theorem rngl_lt_0_add :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 < a)%L → (0 ≤ b)%L → (0 < a + b)%L.
Proof.
intros Hos Hor * Hza Hzb.
apply (rngl_lt_le_trans Hor _ a); [ easy | ].
now apply (rngl_le_add_r Hos Hor).
Qed.

(** *** other theorems *)

Theorem rngl_add_lt_compat :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b c d, (a < b → c < d → a + c < b + d)%L.
Proof.
intros Hos Hor * Hab Hcd.
apply (rngl_lt_trans Hor _ (a + d)%L).
now apply (rngl_add_lt_mono_l Hos Hor).
now apply (rngl_add_lt_mono_r Hos Hor).
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
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0)%L.
Proof.
intros Hos Hor * Haz Hbz Hab.
split. {
  apply (rngl_le_antisymm Hor) in Haz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_r a); subst ab.
  now apply (rngl_add_le_mono_l Hos Hor).
} {
  apply (rngl_le_antisymm Hor) in Hbz; [ easy | ].
  rewrite <- Hab.
  remember (a + b)%L as ab.
  rewrite <- (rngl_add_0_l b); subst ab.
  now apply (rngl_add_le_mono_r Hos Hor).
}
Qed.

Theorem rngl_mul_nat_inj_le :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i ≤ j ↔ (rngl_mul_nat a i ≤ rngl_mul_nat a j)%L.
Proof.
intros Hos Hor.
intros * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; [ | intros; apply Nat.le_0_l ].
  intros H; clear H.
  induction j; [ pauto | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHj | ].
  now apply (rngl_le_add_l Hos Hor), rngl_lt_le_incl.
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply (rngl_nlt_ge Hor) in H; apply H; clear H.
  eapply (rngl_lt_le_trans Hor); [ apply Haz | ].
  apply (rngl_le_add_r Hos Hor).
  clear IHi.
  induction i; [ pauto | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hos Hor), rngl_lt_le_incl.
}
cbn.
split; intros Hij. {
  apply Nat.succ_le_mono in Hij.
  apply (rngl_add_le_mono_l Hos Hor).
  now apply IHi.
} {
  apply -> Nat.succ_le_mono.
  apply (rngl_add_le_mono_l Hos Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_mul_nat_inj_lt :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a, (0 < a)%L → ∀ i j, i < j ↔ (rngl_mul_nat a i < rngl_mul_nat a j)%L.
Proof.
intros Hos Hor * Haz *.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
revert j.
induction i; intros; cbn. {
  split; intros Hj. 2: {
    destruct j; [ | apply Nat.lt_0_succ ].
    now apply rngl_lt_irrefl in Hj.
  }
  induction j; [ easy | clear Hj ].
  cbn.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hos Hor).
  destruct j; [ pauto | ].
  apply rngl_lt_le_incl, IHj.
  apply Nat.lt_0_succ.
}
destruct j. {
  split; [ easy | cbn ].
  intros H; exfalso.
  apply (rngl_nle_gt Hor) in H; apply H; clear H.
  eapply (rngl_le_trans Hor); [ apply rngl_lt_le_incl, Haz | ].
  apply (rngl_le_add_r Hos Hor).
  clear IHi.
  induction i; [ pauto | cbn ].
  eapply (rngl_le_trans Hor); [ apply IHi | ].
  now apply (rngl_le_add_l Hos Hor), rngl_lt_le_incl.
}
cbn.
split; intros Hij. {
  apply Nat.succ_lt_mono in Hij.
  apply (rngl_add_lt_mono_l Hos Hor).
  now apply IHi.
} {
  apply -> Nat.succ_lt_mono.
  apply (rngl_add_lt_mono_l Hos Hor) in Hij.
  now apply IHi.
}
Qed.

Theorem rngl_add_nonneg_pos :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (0 ≤ a)%L → (0 < b)%L → (0 < a + b)%L.
Proof.
intros Hos Hor * Hza Hzb.
rewrite rngl_add_comm.
now apply (rngl_lt_0_add Hos Hor).
Qed.

Theorem rngl_add_nonpos_nonpos :
  rngl_has_opp_or_psub T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b ≤ 0 → a + b ≤ 0)%L.
Proof.
intros Hos Hor * Ha Hb.
apply (rngl_le_trans Hor _ a); [ | easy ].
rewrite <- rngl_add_0_r.
now apply (rngl_add_le_mono_l Hos Hor).
Qed.

Theorem rngl_add_neg_nonpos :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a < 0 → b ≤ 0 → a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
eapply (rngl_lt_le_trans Hor); [ | apply Hbz ].
apply (rngl_lt_add_lt_sub_r Hop Hor).
now rewrite (rngl_sub_diag Hos).
Qed.

Theorem rngl_add_nonpos_neg :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a b, (a ≤ 0 → b < 0 → a + b < 0)%L.
Proof.
intros Hop Hor * Haz Hbz.
rewrite rngl_add_comm.
now apply (rngl_add_neg_nonpos Hop Hor).
Qed.

Theorem rngl_abs_nonneg :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (0 ≤ rngl_abs a)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_abs.
remember (a ≤? 0)%L as az eqn:Haz; symmetry in Haz.
destruct az. {
  apply rngl_leb_le in Haz.
  apply (rngl_opp_le_compat Hop Hor) in Haz.
  now rewrite (rngl_opp_0 Hop) in Haz.
} {
  apply (rngl_leb_gt_iff Hto) in Haz.
  now apply rngl_lt_le_incl.
}
Qed.

Theorem rngl_abs_opp :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, rngl_abs (- a)%L = rngl_abs a.
Proof.
intros Hop Hto *.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
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
  apply (rngl_leb_gt_iff Hto) in Hc.
  rewrite <- (rngl_opp_0 Hop) in Hc.
  apply (rngl_opp_lt_compat Hop Hor) in Hc.
  destruct d; [ easy | ].
  apply (rngl_leb_gt_iff Hto) in Hd.
  now apply (rngl_lt_asymm Hor) in Hd.
}
Qed.

Theorem rngl_le_abs_diag :
  rngl_has_opp T = true →
  rngl_is_ordered T = true →
  ∀ a, (a ≤ rngl_abs a)%L.
Proof.
intros Hop Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
progress unfold rngl_abs.
remember (a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ | pauto ].
apply rngl_leb_le in Hc.
apply (rngl_le_sub_0 Hop Hor).
rewrite (rngl_sub_opp_r Hop).
rewrite <- (rngl_add_0_l 0%L).
now apply (rngl_add_le_mono Hos Hor).
Qed.

Theorem rngl_le_opp_abs_diag :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (- a ≤ rngl_abs a)%L.
Proof.
intros Hop Hto.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
progress unfold rngl_abs.
remember (a ≤? 0)%L as c eqn:Hc; symmetry in Hc.
destruct c; [ pauto | ].
apply (rngl_leb_gt_iff Hto) in Hc.
apply (rngl_le_opp_l Hop Hor).
apply rngl_lt_le_incl in Hc.
now apply (rngl_le_0_add Hos Hor).
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

Theorem rngl_abs_nonpos_eq :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a : T, (a ≤ 0)%L → rngl_abs a = (- a)%L.
Proof.
intros Hop Hto * Haz.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
rewrite <- (rngl_opp_involutive Hop a) at 1.
rewrite (rngl_abs_opp Hop Hto).
apply (rngl_abs_nonneg_eq Hop Hor).
rewrite <- (rngl_opp_0 Hop).
now apply -> (rngl_opp_le_compat Hop Hor).
Qed.

Theorem rngl_abs_le :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ x y, (- x ≤ y ≤ x ↔ rngl_abs y ≤ x)%L.
Proof.
intros * Hop Hto *.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
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
  apply (rngl_leb_gt_iff Hto) in Hyz.
  apply rngl_lt_le_incl.
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply rngl_lt_le_incl.
  now apply (rngl_lt_le_trans Hor _ y)%L.
}
Qed.

Theorem rngl_le_abs :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ x y, (x ≤ y ∨ x ≤ -y)%L ↔ (x ≤ rngl_abs y)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
split; intros Hxy. {
  destruct Hxy as [Hxy| Hxy]. {
    apply (rngl_le_trans Hor _ y); [ easy | ].
    apply (rngl_le_abs_diag Hop Hor).
  }
  apply (rngl_le_trans Hor _ (- y)); [ easy | ].
  rewrite <- (rngl_abs_opp Hop Hto).
  apply (rngl_le_abs_diag Hop Hor).
}
progress unfold rngl_abs in Hxy.
destruct (y ≤? 0)%L; [ now right | now left ].
Qed.

Theorem rngl_abs_lt :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ x y, (- x < y < x ↔ rngl_abs y < x)%L.
Proof.
intros * Hop Hto *.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
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
  apply (rngl_leb_gt_iff Hto) in Hyz.
  apply (rngl_le_lt_trans Hor _ 0)%L; [ | easy ].
  rewrite <- (rngl_opp_0 Hop).
  apply -> (rngl_opp_le_compat Hop Hor).
  apply rngl_lt_le_incl.
  now apply (rngl_lt_trans Hor _ y)%L.
}
Qed.

Theorem rngl_abs_sub_comm :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, rngl_abs (a - b)%L = rngl_abs (b - a)%L.
Proof.
intros Hop Hto *.
rewrite <- (rngl_abs_opp Hop Hto).
now rewrite (rngl_opp_sub_distr Hop).
Qed.

Theorem rngl_abs_pos :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ x, (x ≠ 0 → 0 < rngl_abs x)%L.
Proof.
intros Hop Hto * Hxz.
apply rngl_le_neq.
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
apply (rngl_abs_nonneg Hop Hto).
Qed.

Theorem rngl_abs_triangle :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (rngl_abs (a + b) ≤ rngl_abs a + rngl_abs b)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros.
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
    apply (rngl_add_le_mono_l Hos Hor).
    destruct bz; [ pauto | ].
    apply (rngl_leb_gt_iff Hto) in Hbz.
    apply rngl_lt_le_incl.
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt_iff Hto) in Haz.
  destruct bz. {
    rewrite rngl_add_comm.
    rewrite (rngl_opp_add_distr Hop).
    progress unfold rngl_sub.
    rewrite Hop.
    rewrite rngl_add_comm.
    apply (rngl_add_le_mono_r Hos Hor).
    apply rngl_lt_le_incl.
    apply (rngl_lt_trans Hor _ 0)%L; [ | easy ].
    rewrite <- (rngl_opp_0 Hop).
    now apply -> (rngl_opp_lt_compat Hop Hor).
  }
  apply (rngl_leb_gt_iff Hto) in Hbz.
  apply (rngl_nlt_ge Hor) in Habz.
  exfalso; apply Habz; clear Habz.
  apply (rngl_lt_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_add_r Hos Hor).
  now apply rngl_lt_le_incl.
}
apply (rngl_leb_gt_iff Hto) in Habz.
destruct az. {
  apply rngl_leb_le in Haz.
  destruct bz. {
    apply rngl_leb_le in Hbz.
    apply (rngl_nle_gt Hor) in Habz.
    exfalso; apply Habz; clear Habz.
    rewrite <- rngl_add_0_r.
    now apply (rngl_add_le_mono Hos Hor).
  }
  apply (rngl_add_le_mono_r Hos Hor).
  apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  now rewrite (rngl_opp_0 Hop).
}
apply (rngl_leb_gt_iff Hto) in Haz.
apply (rngl_add_le_mono_l Hos Hor).
destruct bz; [ | pauto ].
apply rngl_leb_le in Hbz.
apply (rngl_le_trans Hor _ 0)%L; [ easy | ].
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_involutive Hop).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_leb_opp_l :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (-a ≤? b)%L = (-b ≤? a)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
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
  apply (rngl_leb_gt_iff Hto) in Hab.
  apply (rngl_leb_gt_iff Hto).
  apply (rngl_lt_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_r Hop Hor).
}
Qed.

Theorem rngl_leb_opp_r :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a ≤? -b)%L = (b ≤? -a)%L.
Proof.
intros Hop Hto.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
intros.
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
  apply (rngl_leb_gt_iff Hto) in Hab.
  apply (rngl_leb_gt_iff Hto).
  apply (rngl_lt_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_lt_opp_l Hop Hor).
}
Qed.

Theorem rngl_leb_0_opp :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a, (0 ≤? - a)%L = (a ≤? 0)%L.
Proof.
intros Hop Hto *.
rewrite (rngl_leb_opp_r Hop Hto).
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_ltb_opp_l :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (-a <? b)%L = (-b <? a)%L.
Proof.
intros Hop Hto *.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
remember (-a <? b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply (rngl_ltb_lt Heo) in Hab.
  apply (rngl_ltb_lt Heo).
  apply (rngl_lt_opp_l Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_l Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge_iff Hto) in Hab.
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_opp_r Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_r Hop Hor).
}
Qed.

Theorem rngl_ltb_opp_r :
  rngl_has_opp T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b, (a <? -b)%L = (b <? -a)%L.
Proof.
intros Hop Hto *.
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
remember (a <? -b)%L as ab eqn:Hab.
symmetry in Hab.
symmetry.
destruct ab. {
  apply (rngl_ltb_lt Heo) in Hab.
  apply (rngl_ltb_lt Heo).
  apply (rngl_lt_opp_r Hop Hor) in Hab.
  rewrite rngl_add_comm in Hab.
  now apply (rngl_lt_opp_r Hop Hor) in Hab.
} {
  apply (rngl_ltb_ge_iff Hto) in Hab.
  apply (rngl_ltb_ge Hor).
  apply (rngl_le_opp_l Hop Hor).
  rewrite rngl_add_comm.
  now apply (rngl_le_opp_l Hop Hor).
}
Qed.

Theorem rngl_archimedean_ub :
  rngl_is_archimedean T = true →
  rngl_is_totally_ordered T = true →
  ∀ a b : T, (0 < a < b)%L →
  ∃ₜ n : nat, (rngl_mul_nat a n ≤ b < rngl_mul_nat a (n + 1))%L.
Proof.
intros Har Hto * (Ha, Hab).
specialize (rngl_is_totally_ordered_is_ordered Hto) as Hor.
specialize rngl_opt_archimedean as H1.
rewrite Har, Hor in H1; cbn in H1.
specialize (H1 a b Ha).
destruct H1 as (m, Hm).
induction m. {
  exfalso; cbn in Hm.
  apply (rngl_nle_gt Hor) in Hm.
  apply Hm; clear Hm.
  now apply (rngl_le_trans Hor _ a); apply rngl_lt_le_incl.
}
destruct (rngl_leb_dec (rngl_mul_nat a m) b) as [Hba| Hba]. {
  apply rngl_leb_le in Hba.
  now exists m; rewrite Nat.add_1_r.
}
apply (rngl_leb_gt_iff Hto) in Hba.
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
Arguments rngl_add_le_mono_l {T ro rp} Hos Hor (a b c)%_L.
Arguments rngl_add_lt_mono_l {T ro rp} Hos Hor (a b c)%_L.
Arguments rngl_le_add_r {T ro rp} Hos Hor (a b)%_L.
