(** * IterMax

Maximum of ring-like values.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

This module defines two syntaxes:

- over lists:
<<
    Max (i ∈ l), f i
>>
- over sequences of natural numbers:
<<
    Max (i = b, e), f i
>>
These notations are introduced to improve code readability.

The maximum operates on ordered ring-like objects. When the
list or the sequence is empty, it returns [0].

Usage:
<<
    Require Import RingLike.IterMax.
>>
*)

From Stdlib Require Import Arith.
Import List.ListNotations.
Open Scope list.

Require Import Utf8.
Require Import Core Misc Utils.

Notation "'Max' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, rngl_max c (g)) 0%L)
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'Max' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, rngl_max c (g)) 0%L)
  (at level 45, i at level 0, l at level 60).

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem fold_left_rngl_max_fun_from_0 :
  rngl_is_ordered T = true →
  ∀ A a l (f : A → _),
  (0 ≤ a)%L
  → (∀ b, b ∈ l → (0 ≤ f b)%L)
  → (List.fold_left (λ c i, rngl_max c (f i)) l a =
     rngl_max a (List.fold_left (λ c i, rngl_max c (f i)) l 0)%L).
Proof.
intros Hor * Ha Hl.
revert a Ha.
induction l as [| b]; intros. {
  cbn.
  symmetry.
  now apply (rngl_max_l_iff Hor).
}
cbn.
rewrite IHl; cycle 1. {
  intros c Hc.
  now apply Hl; right.
} {
  apply (rngl_le_trans Hor _ a); [ easy | ].
  apply (rngl_le_max_l Hor).
}
rewrite <- (rngl_max_assoc Hor).
f_equal.
symmetry.
rewrite (proj2 (rngl_max_r_iff Hor _ _)); [ | now apply Hl; left ].
now apply IHl; intros; apply Hl; [ right | left ].
Qed.

Theorem rngl_max_iter_list_app :
  rngl_is_ordered T = true →
  ∀ A (la lb : list A) f,
  (∀ x, x ∈ lb → rngl_max 0 (f x) = f x)
  → Max (i ∈ la ++ lb), f i =
      rngl_max (Max (i ∈ la), f i) (Max (i ∈ lb), f i).
Proof.
intros Hor * Hm.
rewrite iter_list_app.
rewrite (rngl_max_comm Hor).
progress unfold iter_list.
revert la.
induction lb as [| b]; intros; cbn. {
  symmetry.
  apply (rngl_max_r_iff Hor).
  remember (List.fold_left _ _ _) as v eqn:Hv.
  remember 0%L as z in Hv.
  assert (Hz : (0 ≤ z)%L). {
    subst z.
    apply (rngl_le_refl Hor).
  }
  clear Heqz; subst v.
  revert z Hz.
  induction la as [| a]; intros; [ easy | cbn ].
  apply IHla.
  apply (rngl_le_trans Hor _ z); [ easy | ].
  apply (rngl_le_max_l Hor).
}
assert (H : ∀ x, x ∈ lb → rngl_max 0 (f x) = f x). {
  intros x Hx.
  now apply Hm; right.
}
specialize (IHlb H).
specialize (IHlb (la ++ [b])) as H1; clear H.
rewrite List.fold_left_app in H1.
cbn in H1.
rewrite H1; clear H1.
rewrite (rngl_max_comm Hor _ (f b)).
rewrite (rngl_max_assoc Hor).
f_equal.
specialize (IHlb [b]) as H1.
cbn in H1.
rewrite H1.
f_equal.
symmetry.
now apply Hm; left.
Qed.

Theorem rngl_max_iter_list_cons :
  rngl_is_ordered T = true →
  ∀ A a (la : list A) f,
  (∀ x, x ∈ a :: la → rngl_max 0 (f x) = f x)
  → Max (i ∈ a :: la), f i = rngl_max (f a) (Max (i ∈ la), f i).
Proof.
intros Hor * Hm.
rewrite List_cons_is_app.
rewrite (rngl_max_iter_list_app Hor _ _ _ _). {
  progress unfold iter_list at 1.
  cbn.
  rewrite Hm; [ easy | now left ].
}
intros x Hx.
now apply Hm; right.
Qed.

Theorem rngl_le_max_list_r :
  rngl_is_ordered T = true →
  ∀ A l (a : A) f,
  (∀ x, x ∈ l → rngl_max 0 (f x) = f x)%L
  → a ∈ l
  → (f a ≤ Max (i ∈ l), f i)%L.
Proof.
intros Hor * Hm Hal.
revert a Hal.
induction l as [| b]; intros; [ easy | ].
rewrite (rngl_max_iter_list_cons Hor); [ | easy ].
destruct Hal as [Hal| Hal]; [ subst b; apply (rngl_le_max_l Hor) | ].
eapply (rngl_le_trans Hor); [ | apply (rngl_le_max_r Hor) ].
apply IHl; [ | easy ].
intros x Hx.
now apply Hm; right.
Qed.

Theorem rngl_le_max_seq_r :
  rngl_is_ordered T = true →
  ∀ b e a f,
  (∀ x, x ∈ List.seq b (S e - b) → rngl_max 0 (f x) = f x)%L
  → a ∈ List.seq b (S e - b)
  → (f a ≤ Max (i = b, e), f i)%L.
Proof.
intros Hor * Hm His.
progress unfold iter_seq.
now apply (rngl_le_max_list_r Hor).
Qed.

Theorem rngl_max_list_empty : ∀ A g (l : list A),
  l = [] → Max (i ∈ l), g i = 0%L.
Proof.
intros * Hl.
now apply iter_list_empty.
Qed.

Theorem rngl_iter_max_list_nonneg :
  rngl_is_ordered T = true →
  ∀ A l (f : A → _),
  (∀ a, a ∈ l → (0 ≤ f a))%L
  → (0 ≤ Max (i ∈ l), f i)%L.
Proof.
intros Hor * Hf.
induction l as [| a]. {
  rewrite rngl_max_list_empty; [ | easy ].
  apply (rngl_le_refl Hor).
}
rewrite (rngl_max_iter_list_cons Hor). {
  eapply (rngl_le_trans Hor); [ | apply (rngl_le_max_r Hor) ].
  apply IHl.
  now intros; apply Hf; right.
}
intros b Hi.
apply (rngl_max_r_iff Hor).
now apply Hf.
Qed.

Theorem rngl_iter_max_seq_nonneg :
  rngl_is_ordered T = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → (0 ≤ f i)%L)
  → (0 ≤ Max (i = b, e), f i)%L.
Proof.
intros Hor * Hf.
destruct (lt_dec e b) as [Heb| Heb]. {
  progress unfold iter_seq.
  rewrite rngl_max_list_empty; [ apply (rngl_le_refl Hor) | ].
  now rewrite (proj2 (Nat.sub_0_le _ _)).
}
apply Nat.nlt_ge in Heb.
apply (rngl_iter_max_list_nonneg Hor).
intros i Hi.
apply Hf.
apply List.in_seq in Hi.
split; [ easy | ].
destruct Hi as (Hbi, Hib).
rewrite Nat.add_comm in Hib.
rewrite Nat.sub_add in Hib.
now apply -> Nat.lt_succ_r in Hib.
now apply Nat.le_le_succ_r.
Qed.

Theorem eq_rngl_max_list_0 :
  rngl_is_ordered T = true →
  ∀ l (f : nat → T),
  Max (i ∈ l), f i = 0%L
  → (∀ i, i ∈ l → (0 ≤ f i)%L)
  → ∀ i, i ∈ l
  → f i = 0%L.
Proof.
intros Hor * Hmz Hzi i Hi.
progress unfold iter_list in Hmz.
revert i Hi.
induction l as [| a]; intros; [ easy | ].
cbn in Hmz.
destruct Hi as [Hi| Hi]. {
  subst i.
  rewrite (proj2 (rngl_max_r_iff Hor _ _)) in Hmz; [ | now apply Hzi; left ].
  rewrite (fold_left_rngl_max_fun_from_0 Hor) in Hmz; cycle 1. {
    now apply Hzi; left.
  } {
    now intros; apply Hzi; right.
  }
  rewrite fold_iter_list in Hmz.
  remember (Max (i ∈ _), _) as m eqn:Hm in Hmz.
  progress unfold rngl_max in Hmz.
  remember (f a ≤? m)%L as am eqn:Ham.
  symmetry in Ham.
  destruct am; [ | easy ].
  move Hmz at top; subst m.
  apply rngl_leb_le in Ham.
  apply (rngl_le_antisymm Hor); [ easy | ].
  now apply Hzi; left.
}
apply IHl; [ | now intros; apply Hzi; right | easy ].
rewrite (proj2 (rngl_max_r_iff Hor _ _)) in Hmz; [ | now apply Hzi; left ].
rewrite (fold_left_rngl_max_fun_from_0 Hor) in Hmz; cycle 1. {
  now apply Hzi; left.
} {
  now intros; apply Hzi; right.
}
rewrite fold_iter_list in Hmz |-*.
remember (Max (i ∈ _), _) as m eqn:Hm in Hmz.
progress unfold rngl_max in Hmz.
remember (f a ≤? m)%L as am eqn:Ham.
symmetry in Ham.
destruct am; [ congruence | ].
apply (rngl_leb_gt_iff Hor) in Ham.
rewrite Hmz in Ham.
rewrite Hm in Ham.
exfalso.
apply rngl_nle_gt in Ham.
apply Ham; clear Ham.
apply (rngl_iter_max_list_nonneg Hor).
intros b Hb.
now apply Hzi; right.
Qed.

Theorem eq_rngl_max_seq_0 :
  rngl_is_ordered T = true →
  ∀ b e (f : nat → T),
  Max (i = b, e), f i = 0%L
  → (∀ i, b ≤ i ≤ e → (0 ≤ f i)%L)
  → ∀ i, b ≤ i ≤ e
  → f i = 0%L.
Proof.
intros Hor * Hm Hf i Hi.
apply (eq_rngl_max_list_0 Hor) with (i := i) in Hm; [ easy | | ]. {
  intros j Hj.
  apply Hf.
  apply List.in_seq in Hj.
  split; [ easy | flia Hj ].
}
apply List.in_seq.
split; [ easy | flia Hi ].
Qed.

End a.
