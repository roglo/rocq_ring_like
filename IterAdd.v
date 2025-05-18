(** * IterAdd

Summations on a ring-like.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

This module defines two summation syntaxes:

- over lists:
<<
    ∑ (i ∈ l), f i
>>
- over sequences of natural numbers:
<<
    ∑ (i = b, e), f i
>>
These notations are introduced to improve code readability.

The summation operates on ring-like objects, so it applies equally
whether the elements are numbers, polynomials, square matrices,
or other such structures.

Usage:
<<
    Require Import RingLike.IterAdd.
>>
*)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import ListDef.
Import List.ListNotations.
Open Scope list.

Require Import Core Misc Utils.
Require Import PermutationFun.

Notation "'∑' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c + g)%L) 0%L)
  (at level 45, i at level 0, b at level 60, e at level 60,
   right associativity,
   format "'[hv  ' ∑  ( i  =  b ,  e ) ,  '/' '[' g ']' ']'").

Notation "'∑' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c + g)%L) 0%L)
  (at level 45, i at level 0, l at level 60,
   right associativity,
   format "'[hv  ' ∑  ( i  ∈  l ) ,  '/' '[' g ']' ']'").

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hos : rngl_has_opp_or_subt T = true).

Theorem fold_left_rngl_add_fun_from_0 : ∀ A a l (f : A → _),
  (List.fold_left (λ c i, c + f i) l a =
   a + List.fold_left (λ c i, c + f i) l 0)%L.
Proof.
intros.
apply fold_left_op_fun_from_d. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem all_0_rngl_summation_list_0 : ∀ A l (f : A → T),
  (∀ i, i ∈ l → f i = 0%L)
  → ∑ (i ∈ l), f i = 0%L.
Proof.
intros * Hz.
apply iter_list_all_d; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem all_0_rngl_summation_0 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 0%L)
  → ∑ (i = b, e), f i = 0%L.
Proof.
intros * Hz.
apply iter_seq_all_d; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_list_split_first : ∀ A (l : list A) d f,
  l ≠ []
  → ∑ (i ∈ l), f i = (f (List.hd d l) + ∑ (i ∈ List.tl l), f i)%L.
Proof.
intros * Hlz.
apply iter_list_split_first; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_list_split_last : ∀ A (l : list A) d f,
  l ≠ []
  → ∑ (i ∈ l), f i = (∑ (i ∈ List.removelast l), f i + f (List.last l d))%L.
Proof.
intros * Hlz.
now apply iter_list_split_last.
Qed.

Theorem rngl_summation_list_split : ∀ A (l : list A) f n,
  ∑ (i ∈ l), f i =
    (∑ (i ∈ List.firstn n l), f i + ∑ (i ∈ List.skipn n l), f i)%L.
Proof.
intros.
rewrite <- List.firstn_skipn with (n := n) (l := l) at 1.
unfold iter_list.
rewrite List.fold_left_app.
now rewrite fold_left_rngl_add_fun_from_0.
Qed.

Theorem rngl_summation_split_first : ∀ b k g,
  b ≤ k
  → ∑ (i = b, k), g i = (g b + ∑ (i = S b, k), g i)%L.
Proof.
intros * Hbk.
apply iter_seq_split_first; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_split_last : ∀ b k g,
  b ≤ k
  → (∑ (i = b, k), g i = ∑ (i = S b, k), g (i - 1)%nat + g k)%L.
Proof.
intros * Hbk.
now apply iter_seq_split_last.
Qed.

Theorem rngl_summation_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → (∑ (i = b, k), g i = ∑ (i = b, j), g i + ∑ (i = j+1, k), g i)%L.
Proof.
intros * Hbjk.
apply iter_seq_split; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_split3 : ∀ j g b k,
  b ≤ j ≤ k
  → ∑ (i = b, k), g i =
       (∑ (i = S b, j), g (i - 1)%nat + g j + ∑ (i = j + 1, k), g i)%L.
Proof.
intros * Hj.
apply iter_seq_split3; [ | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%L)
  → (∑ (i = b, k), g i = ∑ (i = b, k), h i)%L.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_summation_list_eq_compat : ∀ A g h (l : list A),
  (∀ i, i ∈ l → (g i = h i)%L)
  → (∑ (i ∈ l), g i = ∑ (i ∈ l), h i)%L.
Proof.
intros * Hgh.
now apply iter_list_eq_compat.
Qed.

Theorem rngl_summation_succ_succ : ∀ b k g,
  (∑ (i = S b, S k), g i = ∑ (i = b, k), g (S i))%L.
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.

Theorem rngl_summation_list_empty : ∀ A g (l : list A),
  l = [] → ∑ (i ∈ l), g i = 0%L.
Proof.
intros * Hl.
now apply iter_list_empty.
Qed.

Theorem rngl_summation_empty : ∀ g b k,
  k < b → (∑ (i = b, k), g i = 0)%L.
Proof.
intros * Hkb.
now apply iter_seq_empty.
Qed.

Theorem rngl_summation_list_add_distr :
  ∀ A g h (l : list A),
  (∑ (i ∈ l), (g i + h i) =
  (∑ (i ∈ l), g i) + ∑ (i ∈ l), h i)%L.
Proof.
intros Hic *.
apply iter_list_distr. {
  apply rngl_add_0_l.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_add_distr : ∀ g h b k,
  (∑ (i = b, k), (g i + h i) =
   ∑ (i = b, k), g i + ∑ (i = b, k), h i)%L.
Proof.
intros g h b k.
apply iter_seq_distr. {
  apply rngl_add_0_l.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_opp_summation_list :
  rngl_has_opp T = true →
  ∀ A (f : A → T) l, (- (∑ (i ∈ l), f i))%L = ∑ (i ∈ l), - f i.
Proof.
intros Hop *.
rewrite iter_list_inv. 2: {
  intros.
  rewrite (rngl_add_opp_r Hop).
  rewrite rngl_add_comm.
  apply (rngl_opp_add_distr Hop).
}
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_summation_list_sub_distr :
  rngl_has_opp T = true →
  ∀ A g h (l : list A),
  (∑ (i ∈ l), (g i - h i) =
  (∑ (i ∈ l), g i) - ∑ (i ∈ l), h i)%L.
Proof.
intros Hop *.
unfold rngl_sub.
rewrite Hop.
rewrite rngl_summation_list_add_distr.
rewrite (rngl_opp_summation_list Hop).
easy.
Qed.

Theorem rngl_summation_shift : ∀ s b g k,
  s ≤ b ≤ k
  → ∑ (i = b, k), g i = ∑ (i = b - s, k - s), g (s + i)%nat.
Proof.
intros s b g k Hbk.
now apply (iter_shift s).
Qed.

Theorem rngl_summation_rshift : ∀ s b e f,
  ∑ (i = b, e), f i = ∑ (i = s + b, s + e), f (i - s)%nat.
Proof.
intros.
apply (iter_rshift s).
Qed.

Theorem rngl_opp_summation :
  rngl_has_opp T = true →
  ∀ b e f, ((- ∑ (i = b, e), f i) = ∑ (i = b, e), (- f i))%L.
Proof.
intros Hop *.
rewrite iter_seq_inv. 2: {
  intros.
  rewrite (rngl_add_opp_r Hop).
  rewrite rngl_add_comm.
  apply (rngl_opp_add_distr Hop).
}
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem rngl_summation_rtl : ∀ g b k,
  (∑ (i = b, k), g i = ∑ (i = b, k), g (k + b - i)%nat)%L.
Proof.
intros g b k.
apply iter_seq_rtl. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem mul_iter_list_distr_l_test : ∀ A B d
    (add mul : A → A → A)
    (add_0_l : ∀ x, add d x = x)
    (mul_add_distr_l : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)),
  ∀  a (la : list B) f,
  mul a (iter_list la (λ c i, add c (f i)) d) =
  if length la =? 0 then mul a d
  else iter_list la (λ c i, add c (mul a (f i))) d.
Proof.
intros.
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
  now apply Nat.eqb_eq, List.length_zero_iff_nil in Haz; subst la.
}
apply Nat.eqb_neq in Haz.
unfold iter_list.
destruct la as [| b]; intros; [ easy | cbn; clear Haz ].
do 2 rewrite add_0_l.
remember (f b) as a1 eqn:H; clear b H.
revert a1.
induction la as [| a2]; intros; [ easy | cbn ].
rewrite IHla.
f_equal.
apply mul_add_distr_l.
Qed.

Theorem mul_iter_list_distr_l : ∀ A B a (la : list B) f
    (add mul : A → A → A) d
    (mul_add_distr_l : ∀ y z, mul a (add y z) = add (mul a y) (mul a z)),
  mul a (iter_list la (λ c i, add c (f i)) d) =
  iter_list la (λ c i, add c (mul a (f i))) (mul a d).
Proof.
intros.
unfold iter_list.
revert d.
induction la as [| a1]; intros; [ easy | cbn ].
rewrite IHla.
f_equal.
apply mul_add_distr_l.
Qed.

Theorem mul_iter_list_distr_r : ∀ A B a (la : list B) f
    (add mul : A → A → A) d
    (mul_add_distr_r : ∀ y z, mul (add y z) a = add (mul y a) (mul z a)),
  mul (iter_list la (λ c i, add c (f i)) d) a =
  iter_list la (λ c i, add c (mul (f i) a)) (mul d a).
Proof.
intros.
unfold iter_list.
revert d.
induction la as [| a1]; intros; [ easy | cbn ].
rewrite IHla.
f_equal.
apply mul_add_distr_r.
Qed.

(* drawback: requires that 0 is absorbing for multiplication *)
(* should use mul_iter_list_distr_l_test instead of mul_iter_list_distr_l
   but the test "if length..." complicates the theorems using it *)
(* same problem with _r versions *)
Theorem rngl_mul_summation_list_distr_l : ∀ A a (la : list A) f,
  (a * (∑ (i ∈ la), f i) = ∑ (i ∈ la), a * f i)%L.
Proof.
intros.
rewrite mul_iter_list_distr_l; [ | apply rngl_mul_add_distr_l ].
now rewrite rngl_mul_0_r.
Qed.

Theorem rngl_mul_summation_distr_l : ∀ a b e f,
  (a * (∑ (i = b, e), f i) = ∑ (i = b, e), a * f i)%L.
Proof.
intros.
apply rngl_mul_summation_list_distr_l.
Qed.

Theorem rngl_mul_summation_list_distr_r : ∀ A a (la : list A) f,
  ((∑ (i ∈ la), f i) * a = ∑ (i ∈ la), f i * a)%L.
Proof.
intros.
rewrite mul_iter_list_distr_r; [ | intros; apply rngl_mul_add_distr_r ].
now rewrite rngl_mul_0_l.
Qed.

Theorem rngl_mul_summation_distr_r : ∀ a b e f,
  ((∑ (i = b, e), f i) * a = ∑ (i = b, e), f i * a)%L.
Proof.
intros.
apply rngl_mul_summation_list_distr_r.
Qed.

Theorem rngl_summation_list_only_one : ∀ A g (a : A),
  (∑ (i ∈ [a]), g i = g a)%L.
Proof.
intros.
unfold iter_list; cbn.
apply rngl_add_0_l.
Qed.

Theorem rngl_summation_only_one : ∀ g n, ∑ (i = n, n), g i = g n.
Proof.
intros g n.
apply iter_seq_only_one, rngl_add_0_l.
Qed.

Theorem rngl_summation_list_cons : ∀ A (a : A) la f,
  (∑ (i ∈ a :: la), f i = f a + ∑ (i ∈ la), f i)%L.
Proof.
intros.
apply iter_list_cons. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_list_app : ∀ A (la lb : list A) f,
  ∑ (i ∈ la ++ lb), f i = (∑ (i ∈ la), f i + ∑ (i ∈ lb), f i)%L.
Proof.
intros.
rewrite iter_list_app.
unfold iter_list.
apply fold_left_rngl_add_fun_from_0.
Qed.

Theorem rngl_summation_list_concat : ∀ A (ll : list (list A)) (f : A → T),
  ∑ (a ∈ List.concat ll), f a = ∑ (l ∈ ll), ∑ (a ∈ l), f a.
Proof.
intros.
induction ll as [| l]; cbn. {
  rewrite rngl_summation_list_empty; [ | easy ].
  now rewrite rngl_summation_list_empty.
}
rewrite rngl_summation_list_app.
rewrite rngl_summation_list_cons.
f_equal.
apply IHll.
Qed.

Theorem rngl_summation_summation_list_flat_map : ∀ A B la (f : A → list B) g,
  (∑ (a ∈ la), ∑ (b ∈ f a), g b) = ∑ (b ∈ List.flat_map f la), g b.
Proof.
intros.
induction la as [| a]; cbn. {
  now apply rngl_summation_list_empty.
}
rewrite rngl_summation_list_cons.
rewrite rngl_summation_list_app.
f_equal; apply IHla.
Qed.

Theorem rngl_summation_summation_list_swap : ∀ A B la lb (f : A → B → T),
  ∑ (a ∈ la), (∑ (b ∈ lb), f a b) =
  ∑ (b ∈ lb), (∑ (a ∈ la), f a b).
Proof.
intros.
induction la as [| a]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  erewrite rngl_summation_list_eq_compat. 2: {
    intros b Hb.
    now rewrite rngl_summation_list_empty.
  }
  now rewrite all_0_rngl_summation_list_0.
}
rewrite rngl_summation_list_cons.
symmetry.
erewrite rngl_summation_list_eq_compat. 2: {
  intros b Hb.
  now rewrite rngl_summation_list_cons.
}
cbn.
rewrite rngl_summation_list_add_distr.
now f_equal.
Qed.

Theorem rngl_summation_summation_list_exch {A B} : ∀ l1 l2 (g : A → B → _),
  (∑ (j ∈ l2), (∑ (i ∈ l1), g i j) =
   ∑ (i ∈ l1), ∑ (j ∈ l2), g i j)%L.
Proof.
intros.
revert l1.
induction l2 as [| a]; intros. {
  rewrite rngl_summation_list_empty; [ | easy ].
  symmetry.
  apply all_0_rngl_summation_list_0.
  intros i Hi.
  now apply rngl_summation_list_empty.
}
rewrite rngl_summation_list_cons.
symmetry.
erewrite rngl_summation_list_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_list_cons.
  easy.
}
cbn.
rewrite rngl_summation_list_add_distr.
f_equal; symmetry.
apply IHl2.
Qed.

Theorem rngl_summation_summation_exch : ∀ a b m n g,
  (∑ (j = a, m), (∑ (i = b, n), g i j) =
   ∑ (i = b, n), ∑ (j = a, m), g i j)%L.
Proof.
intros.
apply rngl_summation_summation_list_exch.
Qed.

Theorem rngl_summation_depend_summation_exch : ∀ g k,
  (∑ (j = 0, k), (∑ (i = 0, j), g i j) =
   ∑ (i = 0, k), ∑ (j = i, k), g i j)%L.
Proof.
intros g k.
induction k; [ easy | ].
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
cbn.
rewrite IHk.
symmetry.
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
cbn.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_summation_split_last; [ | flia Hi ].
  rewrite rngl_summation_succ_succ.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  easy.
}
cbn.
rewrite rngl_summation_add_distr.
rewrite <- rngl_add_assoc.
f_equal.
symmetry.
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
rewrite rngl_summation_only_one.
f_equal.
apply rngl_summation_eq_compat.
intros i Hi.
now rewrite Nat_sub_succ_1.
Qed.

Theorem fold_left_add_seq_add : ∀ a b len i g,
  List.fold_left (λ (c : T) (j : nat), (c + g i j)%L)
    (List.seq (b + i) len) a =
  List.fold_left (λ (c : T) (j : nat), (c + g i (i + j)%nat)%L)
    (List.seq b len) a.
Proof.
intros.
revert a b i.
induction len; intros; [ easy | cbn ].
rewrite fold_left_rngl_add_fun_from_0; symmetry.
rewrite fold_left_rngl_add_fun_from_0; symmetry.
rewrite Nat.add_comm at 1.
f_equal.
rewrite <- Nat.add_succ_l.
apply IHlen.
Qed.

Theorem rngl_summation_summation_shift : ∀ g k,
  (∑ (i = 0, k), (∑ (j = i, k), g i j) =
   ∑ (i = 0, k), ∑ (j = 0, k - i), g i (i + j)%nat)%L.
Proof.
intros g k.
apply rngl_summation_eq_compat; intros i Hi.
unfold iter_seq, iter_list.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ | now destruct Hi ].
now rewrite <- fold_left_add_seq_add, Nat.add_0_l.
Qed.

Theorem rngl_summation_ub_add_distr : ∀ a b f,
  (∑ (i = 0, a + b), f i)%L = (∑ (i = 0, a), f i + ∑ (i = S a, a + b), f i)%L.
Proof.
intros.
rewrite (rngl_summation_split a); [ | flia ].
now rewrite Nat.add_1_r.
Qed.

Theorem rngl_summation_summation_distr : ∀ a b f,
  (∑ (i = 0, a), ∑ (j = 0, b), f i j)%L =
  (∑ (i = 0, (S a * S b - 1)%nat), f (i / S b)%nat (i mod S b))%L.
Proof.
intros.
revert b.
induction a; intros. {
  unfold iter_seq at 1, iter_list at 1.
  cbn - [ "mod" "/" ].
  rewrite rngl_add_0_l, Nat.add_sub.
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite Nat.div_small; [ | flia Hi ].
  rewrite Nat.mod_small; [ easy | flia Hi ].
}
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite Nat_sub_succ_1.
  }
  easy.
}
remember (S a) as x.
cbn - [ "mod" "/" ]; subst x.
rewrite IHa.
rewrite Nat.sub_0_r.
rewrite (Nat.add_comm b).
rewrite rngl_summation_ub_add_distr.
rewrite (rngl_summation_split_last _ (S a * S b)); [ | cbn; flia ].
symmetry.
rewrite (rngl_summation_shift 1); [ | cbn; flia ].
symmetry.
rewrite Nat.sub_diag.
rewrite <- rngl_add_assoc.
f_equal. {
  apply rngl_summation_eq_compat.
  intros i Hi.
  now rewrite (Nat.add_comm 1 i), Nat.add_sub.
} {
  rewrite Nat.div_mul; [ | easy ].
  rewrite Nat.Div0.mod_mul.
  destruct b. {
    unfold iter_seq at 1, iter_list at 1.
    cbn - [ "mod" "/" ].
    rewrite rngl_add_0_l.
    rewrite rngl_summation_empty; [ | flia ].
    now rewrite rngl_add_0_r.
  }
  symmetry.
  rewrite (rngl_summation_shift (S (S a * S (S b)))); [ | flia ].
  symmetry.
  rewrite Nat.sub_diag.
  replace (S a * S (S b) + S b - S (S a * S (S b))) with b. 2: {
    cbn.
    rewrite <- Nat.add_succ_l.
    rewrite Nat.sub_add_distr.
    now do 2 rewrite Nat.add_sub.
  }
  rewrite rngl_summation_split_first; [ | easy ].
  f_equal.
  rewrite rngl_summation_succ_succ.
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite Nat.add_succ_comm.
  rewrite Nat.div_add_l; [ | easy ].
  rewrite (Nat.div_small (S i)); [ | flia Hi ].
  f_equal; [ symmetry; apply Nat.add_0_r | ].
  rewrite Nat_mod_add_l_mul_r.
  symmetry.
  apply Nat.mod_small; flia Hi.
}
Qed.

Theorem rngl_summation_list_permut : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ (la lb : list A) f,
  permutation eqb la lb
  → (∑ (i ∈ la), f i = ∑ (i ∈ lb), f i)%L.
Proof.
intros * Heqb * Hl.
apply (iter_list_permut Heqb); [ | | | | easy ]. {
  apply rngl_add_0_l.
} {
  apply rngl_add_0_r.
} {
  apply rngl_add_comm.
} {
  apply rngl_add_assoc.
}
Qed.

Theorem rngl_summation_seq_summation : ∀ b len f,
  len ≠ 0
  → (∑ (i ∈ List.seq b len), f i = ∑ (i = b, b + len - 1), f i)%L.
Proof.
intros * Hlen.
now apply iter_list_seq.
Qed.

Theorem rngl_summation_list_mul_summation_list :
  ∀ A B li lj (f : A → T) (g : B → T),
  ((∑ (i ∈ li), f i) * (∑ (j ∈ lj), g j))%L =
  ∑ (i ∈ li), (∑ (j ∈ lj), f i * g j).
Proof.
intros.
induction li as [| ai]. {
  rewrite rngl_summation_list_empty; [ symmetry | easy ].
  rewrite rngl_summation_list_empty; [ symmetry | easy ].
  now apply rngl_mul_0_l.
}
do 2 rewrite rngl_summation_list_cons.
rewrite rngl_mul_add_distr_r.
rewrite IHli.
now rewrite rngl_mul_summation_list_distr_l.
Qed.

Theorem rngl_summation_mul_summation : ∀ bi bj ei ej f g,
  ((∑ (i = bi, ei), f i) * (∑ (j = bj, ej), g j))%L =
  ∑ (i = bi, ei), (∑ (j = bj, ej), f i * g j).
Proof.
intros.
apply rngl_summation_list_mul_summation_list.
Qed.

Theorem rngl_summation_list_map :
  ∀ A B (f : A → B) (g : B → _) l,
  ∑ (j ∈ List.map f l), g j = ∑ (i ∈ l), g (f i).
Proof.
intros.
unfold iter_list.
rewrite List_fold_left_map.
now apply rngl_summation_list_eq_compat.
Qed.

Theorem rngl_summation_list_change_var : ∀ A B (l : list A) f g (h : _ → B),
  (∀ i, i ∈ l → g (h i) = i)
  → ∑ (i ∈ l), f i = ∑ (i ∈ List.map h l), f (g i).
Proof.
intros * Hgh.
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros i Hi.
now rewrite Hgh.
Qed.

Theorem rngl_summation_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → ∑ (i = b, e), f i = ∑ (i ∈ List.map h (List.seq b (S e - b))), f (g i).
Proof.
intros * Hgh.
apply rngl_summation_list_change_var.
intros i Hi.
apply List.in_seq in Hi.
apply Hgh.
flia Hi.
Qed.

Theorem rngl_summation_list_le_compat {A} :
  rngl_is_ordered T = true →
  ∀ l (g h : A → T),
  (∀ i, i ∈ l → (g i ≤ h i)%L)
  → (∑ (i ∈ l), g i ≤ ∑ (i ∈ l), h i)%L.
Proof.
intros Hor * Hgh.
induction l as [| a]; intros. {
  rewrite rngl_summation_list_empty; [ | easy ].
  rewrite rngl_summation_list_empty; [ | easy ].
  apply (rngl_le_refl Hor).
}
do 2 rewrite rngl_summation_list_cons.
apply (rngl_add_le_compat Hor); [ now apply Hgh; left | ].
apply IHl.
intros i Hi.
now apply Hgh; right.
Qed.

Theorem rngl_summation_le_compat :
  rngl_is_ordered T = true →
  ∀ b e g h,
  (∀ i, b ≤ i ≤ e → (g i ≤ h i)%L)
  → (∑ (i = b, e), g i ≤ ∑ (i = b, e), h i)%L.
Proof.
intros Hor * Hgh.
unfold iter_seq.
apply (rngl_summation_list_le_compat Hor).
intros i Hi.
apply Hgh.
apply List.in_seq in Hi.
destruct Hi as (Hbi, Hib).
split; [ easy | ].
flia Hbi Hib.
Qed.

Theorem rngl_summation_nonneg :
  rngl_is_ordered T = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → (0 ≤ f i)%L)
  → (0 ≤ ∑ (i = b, e), f i)%L.
Proof.
intros Hor.
intros * Hz.
eapply (rngl_le_trans Hor). 2: {
  apply (rngl_summation_le_compat Hor).
  apply Hz.
}
rewrite all_0_rngl_summation_0; [ | easy ].
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_summation_filter : ∀ A l f (g : A → T),
  ∑ (a ∈ List.filter f l), g a = ∑ (a ∈ l), if f a then g a else 0%L.
Proof.
intros.
induction l as [| b]; [ easy | cbn ].
rewrite rngl_summation_list_cons.
remember (f b) as fb eqn:Hfb; symmetry in Hfb.
destruct fb. {
  rewrite rngl_summation_list_cons; f_equal.
  apply IHl.
} {
  rewrite rngl_add_0_l.
  apply IHl.
}
Qed.

Theorem rngl_summation_1 :
  ∀ b e,
  (∑ (i = b, e), 1 = rngl_of_nat (S e - b))%L.
Proof.
intros.
remember (S e - b) as n eqn:Hn.
progress unfold iter_seq.
rewrite <- Hn; clear e Hn.
revert b.
induction n; intros; [ easy | cbn ].
rewrite rngl_summation_list_cons.
f_equal.
apply IHn.
Qed.

Theorem rngl_summation_const :
  rngl_has_1 T = true →
  ∀ b e c,
  (∑ (i = b, e), c = rngl_of_nat (S e - b) * c)%L.
Proof.
intros Hon *.
remember (S e - b) as n eqn:Hn.
progress unfold iter_seq.
rewrite <- Hn; clear e Hn.
revert b.
induction n; intros; cbn. {
  rewrite rngl_summation_list_empty; [ | easy ].
  symmetry; apply (rngl_mul_0_l Hos).
}
rewrite rngl_summation_list_cons.
rewrite rngl_mul_add_distr_r.
f_equal; [ | apply IHn ].
symmetry; apply (rngl_mul_1_l Hon).
Qed.

Theorem rngl_eval_polyn_is_summation :
  rngl_has_1 T = true →
  (0 + 0 * 1)%L = 0%L →
  ∀ (la : list T) x,
  (rngl_eval_polyn la x = ∑ (i = 0, length la - 1), la.[i] * x ^ i)%L.
Proof.
intros Hon glop.
intros.
progress unfold rngl_eval_polyn.
induction la as [| a]. {
  cbn; symmetry.
  apply all_0_rngl_summation_0.
  intros i (_, Hi).
  apply Nat.le_0_r in Hi; subst i.
  apply (rngl_mul_0_l Hos).
}
cbn.
rewrite IHla.
rewrite Nat.sub_0_r.
symmetry.
rewrite rngl_summation_split_first; [ | easy ].
cbn.
rewrite (rngl_mul_1_r Hon).
rewrite rngl_add_comm.
f_equal.
remember (length la) as len eqn:Hlen.
symmetry in Hlen.
destruct len. {
  cbn.
  apply List.length_zero_iff_nil in Hlen.
  subst la; cbn.
  rewrite rngl_summation_empty; [ | easy ].
  rewrite rngl_summation_only_one; symmetry.
  rewrite <- rngl_mul_assoc.
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_summation_succ_succ.
rewrite Nat_sub_succ_1.
rewrite (rngl_mul_summation_distr_r).
apply rngl_summation_eq_compat.
intros i (_, Hi).
rewrite <- rngl_mul_assoc; f_equal.
rewrite <- Nat.add_1_r.
rewrite (rngl_pow_add_r Hon).
now rewrite (rngl_pow_1_r Hon).
Qed.

Theorem rngl_summation_power :
  rngl_mul_is_comm T = true →
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ n x, x ≠ 1%L → ∑ (i = 0, n), x ^ i = ((x ^ S n - 1) / (x - 1))%L.
Proof.
clear Hos.
intros Hic Hon Hop Hiv.
specialize (rngl_has_opp_has_opp_or_subt Hop) as Hos.
specialize (rngl_has_inv_has_inv_or_quot Hiv) as Hiq.
specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
intros * Hx1.
assert (Hx1z : (x - 1)%L ≠ 0%L). {
  intros H; apply Hx1; clear Hx1.
  apply (f_equal (rngl_add 1%L)) in H.
  rewrite rngl_add_comm, rngl_add_0_r in H.
  now rewrite (rngl_sub_add Hop) in H.
}
induction n. {
  rewrite rngl_summation_only_one.
  rewrite rngl_pow_0_r.
  rewrite (rngl_pow_1_r Hon).
  symmetry.
  now apply (rngl_div_diag Hon Hiq).
}
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_succ_succ.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  now rewrite Nat_sub_succ_1.
}
rewrite IHn.
apply (rngl_mul_cancel_r Hi1 _ _ (x - 1)); [ easy | ].
rewrite rngl_mul_add_distr_r.
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite (rngl_mul_sub_distr_l Hop).
rewrite (rngl_mul_1_r Hon).
rewrite (rngl_add_sub_assoc Hop).
rewrite (rngl_add_sub_swap Hop).
rewrite (rngl_sub_sub_swap Hop).
rewrite (rngl_sub_diag Hos).
rewrite (rngl_sub_0_l Hop).
rewrite (rngl_mul_comm Hic).
apply (rngl_add_opp_l Hop).
Qed.

End a.
