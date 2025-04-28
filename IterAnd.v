(* iterators of "and" on bool *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import List.ListNotations.

Require Import Misc.

Notation "'⋀' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c && g)%bool) true)
  (at level 45, i at level 0, b at level 60, e at level 60).

Notation "'⋀' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c && g)%bool) true)
  (at level 45, i at level 0, l at level 60).

Theorem all_true_and_list_true_iff : ∀ A (l : list A) f,
  (∀ a, a ∈ l → f a = true)
  ↔ ⋀ (a ∈ l), f a = true.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite iter_list_cons; cycle 1. {
  apply Bool.andb_true_l.
} {
  apply Bool.andb_true_r.
} {
  apply Bool.andb_assoc.
}
rewrite Bool.andb_true_iff.
split. {
  intros Hb.
  split; [ now apply Hb; left | ].
  apply IHl.
  intros a Ha.
  now apply Hb; right.
} {
  intros Hb a Ha.
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  now apply IHl.
}
Qed.

Theorem and_list_cons : ∀ A (a : A) la f,
  ⋀ (i ∈ a :: la), f i = (f a && ⋀ (i ∈ la), f i)%bool.
Proof.
intros.
apply iter_list_cons. {
  apply Bool.andb_true_l.
} {
  apply Bool.andb_true_r.
} {
  apply Bool.andb_assoc.
}
Qed.
