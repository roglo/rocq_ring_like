(** * IterAnd

Iterators of "and" on bool.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

This module defines two iterators syntaxes:

- over lists:
<<
    ⋀ (i ∈ l), f i
>>
- over sequences of natural numbers:
<<
    ⋀ (i = b, e), f i
>>
These notations are introduced to improve code readability.

Usage:
<<
    Require Import RingLike.IterAnd.
>>
*)

Set Nested Proofs Allowed.

From Stdlib Require Import Arith.
Import List.ListNotations.

Require Import Utf8.
Require Import Misc Utils.

Notation "'⋀' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c && g)%bool) true)
  (at level 36, i at level 0, b at level 60, e at level 60,
   right associativity,
   format "'[hv  ' ⋀  ( i  =  b ,  e ) ,  '/' '[' g ']' ']'").

Notation "'⋀' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c && g)%bool) true)
  (at level 36, i at level 0, l at level 60,
   right associativity,
   format "'[hv  ' ⋀  ( i  ∈  l ) ,  '/' '[' g ']' ']'").

Theorem all_true_rngl_and_list_true_iff : ∀ A (l : list A) f,
  (∀ a, a ∈ l → f a = true)
  ↔ ⋀ (a ∈ l), f a = true.
Proof.
intros.
induction l as [| b]; [ easy | ].
rewrite iter_list_cons; cycle 1.
apply Bool.andb_true_l.
apply Bool.andb_true_r.
apply Bool.andb_assoc.
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

Theorem rngl_and_list_cons : ∀ A (a : A) la f,
  ⋀ (i ∈ a :: la), f i = (f a && ⋀ (i ∈ la), f i)%bool.
Proof.
intros.
apply iter_list_cons.
apply Bool.andb_true_l.
apply Bool.andb_true_r.
apply Bool.andb_assoc.
Qed.

Theorem rngl_and_list_empty : ∀ A g (l : list A),
  l = [] → ⋀ (i ∈ l), g i = true.
Proof.
intros * Hl.
now apply iter_list_empty.
Qed.

Theorem fold_left_rngl_and_fun_from_true : ∀ A a l (f : A → _),
  (List.fold_left (λ c i, c && f i) l a =
   a && List.fold_left (λ c i, c && f i) l true)%bool.
Proof.
intros.
apply fold_left_op_fun_from_d.
apply Bool.andb_true_l.
apply Bool.andb_true_r.
apply Bool.andb_assoc.
Qed.

Theorem rngl_and_list_app : ∀ A (la lb : list A) f,
  ⋀ (i ∈ la ++ lb), f i = (⋀ (i ∈ la), f i && ⋀ (i ∈ lb), f i)%bool.
Proof.
intros.
rewrite iter_list_app.
unfold iter_list.
apply fold_left_rngl_and_fun_from_true.
Qed.

Theorem rngl_and_list_map : ∀ A B (f : A → B) (g : B → _) l,
  ⋀ (j ∈ ListDef.map f l), g j = ⋀ (i ∈ l), g (f i).
Proof.
intros.
unfold iter_list.
now rewrite List_fold_left_map.
Qed.

Theorem rngl_and_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → g i = h i)
  → ⋀ (i = b, k), g i = ⋀ (i = b, k), h i.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_and_list_eq_compat : ∀ A g h (l : list A),
  (∀ i, i ∈ l → g i = h i)
  → ⋀ (i ∈ l), g i = ⋀ (i ∈ l), h i.
Proof.
intros * Hgh.
now apply iter_list_eq_compat.
Qed.
