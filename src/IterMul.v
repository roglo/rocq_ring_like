(** * IterMul

Products on a ring-like.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

This module defines two product syntaxes:

- over lists:
<<
    ∏ (i ∈ l), f i
>>
- over sequences of natural numbers:
<<
    ∏ (i = b, e), f i
>>
These notations are introduced to improve code readability.

The product operates on ring-like objects, so it applies equally
whether the elements are numbers, polynomials, square matrices,
or other such structures.

Usage:
<<
    Require Import RingLike.IterMul.
>>
*)

Set Nested Proofs Allowed.

Require Import Stdlib.Arith.Arith.
Import List.ListNotations.

Require Import Utf8 Core Misc Utils PermutationFun.

Notation "'∏' ( i = b , e ) , g" :=
  (iter_seq b e (λ c i, (c * g)%L) 1%L)
  (at level 35, i at level 0, b at level 60, e at level 60,
   right associativity,
   format "'[hv  ' ∏  ( i  =  b ,  e ) ,  '/' '[' g ']' ']'").

Notation "'∏' ( i ∈ l ) , g" :=
  (iter_list l (λ c i, (c * g)%L) 1%L)
  (at level 35, i at level 0, l at level 60,
   right associativity,
   format "'[hv  ' ∏  ( i  ∈  l ) ,  '/' '[' g ']' ']'").

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem fold_left_rngl_mul_fun_from_1 : ∀ A a l (f : A → _),
  (List.fold_left (λ c i, c * f i) l a =
   a * List.fold_left (λ c i, c * f i) l 1)%L.
Proof.
intros.
apply fold_left_op_fun_from_d. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem all_1_rngl_product_1 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 1%L)
  → ∏ (i = b, e), f i = 1%L.
Proof.
intros * Hz.
apply iter_seq_all_d; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_split_first : ∀ b k g,
  b ≤ k
  → ∏ (i = b, k), g i = (g b * ∏ (i = S b, k), g i)%L.
Proof.
intros * Hbk.
apply iter_seq_split_first; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_split_last : ∀ b k g,
  b ≤ k
  → ∏ (i = b, k), g i = (∏ (i = S b, k), g (i - 1)%nat * g k)%L.
Proof.
intros * Hbk.
now apply iter_seq_split_last.
Qed.

Theorem rngl_product_split : ∀ j g b k,
  b ≤ S j ≤ S k
  → ∏ (i = b, k), g i = ((∏ (i = b, j), g i) * (∏ (i = j+1, k), g i))%L.
Proof.
intros * Hbjk.
apply iter_seq_split; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_split3 : ∀ j g b k,
  b ≤ j ≤ k
  → ∏ (i = b, k), g i =
       (∏ (i = S b, j), g (i - 1)%nat * g j * ∏ (i = j + 1, k), g i)%L.
Proof.
intros * Hj.
apply iter_seq_split3; [ | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
(*
rewrite rngl_product_split with (j := j); [ | flia Hj ].
now rewrite rngl_product_split_last.
*)
Qed.

Theorem rngl_product_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%L)
  → (∏ (i = b, k), g i = ∏ (i = b, k), h i)%L.
Proof.
intros * Hgh.
now apply iter_seq_eq_compat.
Qed.

Theorem rngl_product_list_eq_compat : ∀ A g h (l : list A),
  (∀ i, i ∈ l → (g i = h i)%L)
  → (∏ (i ∈ l), g i = ∏ (i ∈ l), h i)%L.
Proof.
intros * Hgh.
now apply iter_list_eq_compat.
Qed.

Theorem rngl_product_list_cons : ∀ A (a : A) la f,
  (∏ (i ∈ a :: la), f i = f a * ∏ (i ∈ la), f i)%L.
Proof.
intros.
unfold iter_list; cbn.
rewrite rngl_mul_1_l.
now apply fold_left_rngl_mul_fun_from_1.
Qed.

Theorem rngl_product_list_app : ∀ A (la lb : list A) f,
  ∏ (i ∈ la ++ lb), f i = (∏ (i ∈ la), f i * ∏ (i ∈ lb), f i)%L.
Proof.
intros.
rewrite iter_list_app.
unfold iter_list.
apply fold_left_rngl_mul_fun_from_1.
Qed.

Theorem rngl_product_succ_succ : ∀ b k g,
  (∏ (i = S b, S k), g i = ∏ (i = b, k), g (S i))%L.
Proof.
intros b k g.
apply iter_seq_succ_succ.
Qed.

Theorem rngl_product_succ_succ' : ∀ b k g,
  (∏ (i = S b, S k), g (i - 1)%nat = ∏ (i = b, k), g i)%L.
Proof.
intros.
symmetry.
now rewrite <- iter_seq_succ_succ'.
Qed.

Theorem rngl_product_list_empty : ∀ A g (l : list A),
  l = [] → ∏ (i ∈ l), g i = 1%L.
Proof.
intros * Hl.
now apply iter_list_empty.
Qed.

Theorem rngl_product_empty : ∀ g b k,
  k < b → (∏ (i = b, k), g i = 1)%L.
Proof.
intros * Hkb.
now apply iter_seq_empty.
Qed.

Theorem rngl_product_list_mul_distr :
  rngl_mul_is_comm T = true →
  ∀ A g h (l : list A),
  (∏ (i ∈ l), (g i * h i) =
  (∏ (i ∈ l), g i) * ∏ (i ∈ l), h i)%L.
Proof.
intros Hic *.
apply iter_list_distr. {
  apply rngl_mul_1_l.
} {
  now apply rngl_mul_comm.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_mul_distr :
  rngl_mul_is_comm T = true →
  ∀ g h b k,
  (∏ (i = b, k), (g i * h i) =
  (∏ (i = b, k), g i) * ∏ (i = b, k), h i)%L.
Proof.
intros Hic g h b k.
apply iter_seq_distr. {
  apply rngl_mul_1_l.
} {
  now apply rngl_mul_comm.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_shift : ∀ s b g k,
  s ≤ b ≤ k
  → ∏ (i = b, k), g i = ∏ (i = b - s, k - s), g (s + i)%nat.
Proof.
intros s b g k Hbk.
now apply (iter_shift s).
Qed.

Theorem rngl_product_rshift : ∀ s b e f,
  ∏ (i = b, e), f i =  ∏ (i = s + b, s + e), f (i - s)%nat.
Proof.
intros.
destruct (le_dec b e) as [Hbe| Hbe]. 2: {
  apply Nat.nle_gt in Hbe.
  rewrite rngl_product_empty; [ | easy ].
  rewrite rngl_product_empty; [ | flia Hbe ].
  easy.
}
symmetry.
rewrite (rngl_product_shift s); [ | flia Hbe ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite Nat.add_comm, Nat.add_sub.
apply rngl_product_eq_compat.
intros i Hi.
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Theorem rngl_product_ub_mul_distr : ∀ a b f,
  (∏ (i = 0, a + b), f i)%L = (∏ (i = 0, a), f i * ∏ (i = S a, a + b), f i)%L.
Proof.
intros.
rewrite (rngl_product_split a); [ | flia ].
now rewrite Nat.add_1_r.
Qed.

Theorem rngl_product_list_integral :
  rngl_has_opp_or_psub T = true →
  (rngl_is_integral_domain T ||
   rngl_has_inv_or_pdiv T && rngl_has_eq_dec_or_order T)%bool = true →
  rngl_characteristic T ≠ 1 →
  ∀ A (l : list A) f,
  (∏ (i ∈ l), f i)%L = 0%L
  → ∃ i, i ∈ l ∧ f i = 0%L.
Proof.
intros Hom Hio H10 * Hz.
induction l as [| a]; [ now apply rngl_1_neq_0_iff in Hz | ].
unfold iter_list in Hz; cbn in Hz.
rewrite rngl_mul_1_l in Hz.
rewrite (fold_left_op_fun_from_d 1%L) in Hz; cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
rewrite fold_iter_list in Hz.
apply rngl_integral in Hz; [ | easy | easy ].
destruct Hz as [Hz| Hz]. {
  exists a.
  split; [ now left | easy ].
}
destruct (IHl Hz) as (i & Hil & Hfi).
exists i.
split; [ now right | easy ].
Qed.

Theorem rngl_product_integral :
  rngl_has_opp_or_psub T = true →
  (rngl_is_integral_domain T ||
     rngl_has_inv_or_pdiv T && rngl_has_eq_dec_or_order T)%bool = true →
  rngl_characteristic T ≠ 1 →
  ∀ b e f,
  (∏ (i = b, e), f i = 0)%L
  → ∃ i, b ≤ i ≤ e ∧ f i = 0%L.
Proof.
intros Hom Hio H10 * Hz.
apply rngl_product_list_integral in Hz; [ | easy | easy | easy ].
destruct Hz as (i & His & Hfi).
apply List.in_seq in His.
exists i.
split; [ flia His | easy ].
Qed.

Theorem rngl_product_list_permut : ∀ {A} {eqb : A → _},
  equality eqb →
  rngl_mul_is_comm T = true →
  ∀ (la lb : list A) f,
  permutation eqb la lb
  → ∏ (i ∈ la), f i = ∏ (i ∈ lb), f i.
Proof.
intros * Heqb Hic * Hl.
apply (iter_list_permut Heqb); [ | | | | easy ]. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  now apply rngl_mul_comm.
} {
  apply rngl_mul_assoc.
}
Qed.

Theorem rngl_product_change_var : ∀ A b e f g (h : _ → A),
  (∀ i, b ≤ i ≤ e → g (h i) = i)
  → (∏ (i = b, e), f i =
      ∏ (i ∈ List.map h (List.seq b (S e - b))), f (g i))%L.
Proof.
intros * Hgh.
unfold iter_seq, iter_list.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros i c Hi.
f_equal; f_equal; symmetry.
apply Hgh.
apply List.in_seq in Hi.
flia Hi.
Qed.

Theorem rngl_inv_product_list :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  (rngl_is_integral_domain T || rngl_has_eq_dec_or_order T)%bool = true →
  ∀ A (l : list A) f,
  (∀ i, i ∈ l → f i ≠ 0%L)
  → ((∏ (i ∈ l), f i)⁻¹ = ∏ (i ∈ List.rev l), ((f i)⁻¹))%L.
Proof.
intros Hos Hiv Hit.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros * Hnz.
  rewrite (H1 (∏ (i ∈ List.rev _), _)).
  apply H1.
}
intros * Hnz.
unfold iter_list.
induction l as [| a]; [ now apply (rngl_inv_1 Hiv); right | cbn ].
rewrite rngl_mul_1_l.
rewrite (fold_left_op_fun_from_d 1%L); cycle 1. {
  apply rngl_mul_1_l.
} {
  apply rngl_mul_1_r.
} {
  apply rngl_mul_assoc.
}
rewrite rngl_inv_mul_distr; [ | easy | easy | | ]; cycle 1. {
  now apply Hnz; left.
} {
  intros H1.
  rewrite fold_iter_list in H1.
  assert
    (Hit' :
       (rngl_is_integral_domain T ||
          rngl_has_inv_or_pdiv T &&
          rngl_has_eq_dec_or_order T)%bool = true). {
    apply Bool.orb_true_iff in Hit.
    apply Bool.orb_true_iff.
    destruct Hit as [Hit| Hit]; [ now left | right ].
    rewrite Hit, Bool.andb_true_iff; split; [ | easy ].
    now apply rngl_has_inv_or_pdiv_iff; left.
  }
  specialize (rngl_product_list_integral Hos Hit' Hc1) as H2.
  specialize (H2 A l f H1).
  destruct H2 as (i & Hil & Hfi).
  now revert Hfi; apply Hnz; right.
}
rewrite IHl. 2: {
  intros i Hi.
  now apply Hnz; right.
}
symmetry.
apply List.fold_left_app.
Qed.

Theorem rngl_inv_product :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv T = true →
  (rngl_is_integral_domain T || rngl_has_eq_dec_or_order T)%bool = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i ≠ 0%L)
  → ((∏ (i = b, e), f i)⁻¹ = ∏ (i = b, e), ((f (b + e - i)%nat)⁻¹))%L.
Proof.
intros Hom Hin Hit * Hnz.
unfold iter_seq.
rewrite rngl_inv_product_list; [ | easy | easy | easy | ]. 2: {
  intros i Hi.
  apply List.in_seq in Hi.
  apply Hnz; flia Hi.
}
unfold iter_list.
remember (S e - b) as len eqn:Hlen.
destruct len; [ easy | ].
replace e with (b + len) in Hnz |-* by flia Hlen.
clear e Hlen.
revert b Hnz.
induction len; intros. {
  cbn.
  do 2 rewrite rngl_mul_1_l.
  now rewrite Nat.add_0_r, Nat.add_sub.
}
symmetry.
rewrite List.seq_S at 1.
symmetry.
remember (S len) as sl; cbn; subst sl.
rewrite List.fold_left_app.
rewrite List.fold_left_app.
rewrite IHlen. 2: {
  intros i Hi.
  apply Hnz; flia Hi.
}
cbn - [ "-" ].
do 2 rewrite rngl_mul_1_l.
replace (b + (b + S len) - (b + S len)) with b by flia.
f_equal.
replace (S (b + S (b + len)) - S b) with (S (b + len)) by flia.
replace (b + (b + S len) - b) with (S (b + len)) by flia.
rewrite <- List.seq_shift.
rewrite List_fold_left_map; cbn.
apply List_fold_left_ext_in.
intros c d Hc.
f_equal; f_equal; f_equal.
flia.
Qed.

Theorem rngl_inv_product_list_comm : ∀ A (eqb : A → A → bool),
  equality eqb →
  rngl_has_opp_or_psub T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  (rngl_is_integral_domain T || rngl_has_eq_dec_or_order T)%bool = true →
  ∀ (l : list A) f,
  (∀ i, i ∈ l → f i ≠ 0%L)
  → ((∏ (i ∈ l), f i)⁻¹ = ∏ (i ∈ l), (( f i)⁻¹))%L.
Proof.
intros * Heqb Hom Hic Hin Hit * Hnz.
rewrite rngl_inv_product_list; [ | easy | easy | easy | easy ].
apply (rngl_product_list_permut Heqb Hic).
now apply permutation_rev_l.
Qed.

Theorem rngl_inv_product_comm :
  rngl_has_opp_or_psub T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  (rngl_is_integral_domain T || rngl_has_eq_dec_or_order T)%bool = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i ≠ 0%L)
  → ((∏ (i = b, e), f i)⁻¹ = ∏ (i = b, e), ((f i)⁻¹))%L.
Proof.
intros Hom Hic Hin Hit * Hnz.
apply (rngl_inv_product_list_comm _ _ Nat.eqb_eq); try easy.
intros i Hi.
apply List.in_seq in Hi.
apply Hnz; flia Hi.
Qed.

Theorem rngl_product_div_distr :
  rngl_has_opp_or_psub T = true →
  rngl_mul_is_comm T = true →
  rngl_has_inv T = true →
  (rngl_is_integral_domain T || rngl_has_eq_dec_or_order T)%bool = true →
  ∀ b e f g,
  (∀ i, b ≤ i ≤ e → g i ≠ 0%L)
  → (∏ (i = b, e), (f i / g i))%L =
    ((∏ (i = b, e), f i) / (∏ (i = b, e), g i))%L.
Proof.
intros Hom Hic Hin Hit * Hg.
unfold rngl_div.
rewrite Hin.
rewrite rngl_product_mul_distr; [ | easy ].
f_equal; symmetry.
now apply rngl_inv_product_comm.
Qed.

Theorem rngl_product_seq_product : ∀ b len f,
  len ≠ 0
  → (∏ (i ∈ List.seq b len), f i = ∏ (i = b, b + len - 1), f i)%L.
Proof.
intros * Hlen.
now apply iter_list_seq.
Qed.

Theorem rngl_product_1_opp_1 :
  rngl_has_opp T = true →
  ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 1%L ∨ f i = (-1)%L)
  → (∏ (i = b, e), f i = 1)%L ∨ (∏ (i = b, e), f i = -1)%L.
Proof.
intros Hop * Hf.
unfold iter_seq.
remember (S e - b) as len eqn:Hlen.
destruct len; [ now left | ].
assert (H : ∀ i, b ≤ i ≤ b + len → f i = 1%L ∨ f i = (-1)%L). {
  intros i Hi.
  apply Hf.
  flia Hlen Hi.
}
move H before Hf; clear Hf; rename H into Hf.
replace e with (b + len) by flia Hlen.
clear e Hlen.
revert b Hf.
induction len; intros. {
  cbn.
  unfold iter_list; cbn.
  rewrite rngl_mul_1_l.
  apply Hf; flia.
}
remember (S len) as x; cbn; subst x.
rewrite rngl_product_list_cons.
specialize (Hf b) as H1.
assert (H : b ≤ b ≤ b + S len) by flia.
specialize (H1 H); clear H.
specialize (IHlen (S b)) as H2.
assert (H : ∀ i, S b ≤ i ≤ S b + len → f i = 1%L ∨ f i = (-1)%L). {
  intros i Hi.
  apply Hf.
  flia Hi.
}
specialize (H2 H); clear H.
destruct H1 as [H1| H1]; rewrite H1. {
  now rewrite rngl_mul_1_l.
} {
  destruct H2 as [H2| H2]; rewrite H2; [ right | left ]. {
    rewrite rngl_mul_opp_l; [ | easy ].
    now rewrite rngl_mul_1_l.
  } {
    rewrite rngl_mul_opp_opp; [ | easy ].
    apply rngl_mul_1_l.
  }
}
Qed.

Theorem rngl_product_list_only_one : ∀ A g (a : A),
  (∏ (i ∈ [a]), g i = g a)%L.
Proof.
intros.
unfold iter_list; cbn.
apply rngl_mul_1_l.
Qed.

Theorem rngl_product_only_one : ∀ g n, (∏ (i = n, n), g i = g n)%L.
Proof.
intros g n.
apply iter_seq_only_one, rngl_mul_1_l.
Qed.

End a.

Require Import IterAdd.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.

Theorem rngl_product_summation_distr_cart_prod :
  rngl_has_opp_or_psub T = true →
  ∀ m n (f : nat → nat → T),
  m ≠ 0
  → ∏ (i = 1, m), (∑ (j = 1, n), f i j) =
    ∑ (l ∈ List_cart_prod (List.repeat (List.seq 1 n) m)),
      ∏ (i = 1, m), f i (List.nth (i - 1) l 0%nat).
Proof.
intros Hop * Hmz.
revert n f.
induction m; intros; [ easy | clear Hmz; cbn ].
remember (List.repeat (List.seq 1 n) m) as ll eqn:Hll; symmetry in Hll.
rewrite List.flat_map_concat_map.
rewrite rngl_summation_list_concat.
rewrite rngl_summation_list_map.
erewrite rngl_summation_list_eq_compat. 2: {
  intros i Hi.
  now rewrite rngl_summation_list_map.
}
cbn - [ List.nth ].
destruct m. {
  cbn in Hll; subst ll.
  rewrite (rngl_product_only_one).
  rewrite fold_iter_seq'.
  cbn - [ List.nth ].
  rewrite Nat.sub_0_r.
  apply rngl_summation_eq_compat.
  intros i Hi.
  rewrite rngl_summation_list_only_one.
  now rewrite rngl_product_only_one, Nat.sub_diag.
}
specialize (IHm (Nat.neq_succ_0 _)).
rewrite rngl_product_split_first; [ | now apply -> Nat.succ_le_mono ].
rewrite (rngl_product_shift 1); [ | flia ].
do 2 rewrite Nat_sub_succ_1.
rewrite IHm.
rewrite Hll.
unfold iter_seq at 1.
rewrite rngl_summation_list_mul_summation_list; [ | easy ].
rewrite Nat_sub_succ_1.
apply rngl_summation_list_eq_compat.
intros i Hi.
apply rngl_summation_list_eq_compat.
intros l Hl.
symmetry.
rewrite rngl_product_split_first; [ | flia ].
rewrite List_nth_0_cons.
f_equal.
rewrite (rngl_product_shift 1); [ | flia ].
do 2 rewrite Nat_sub_succ_1.
apply rngl_product_eq_compat.
intros k Hk.
rewrite Nat.add_comm, Nat.add_sub.
destruct k; [ easy | ].
rewrite List_nth_succ_cons.
now rewrite Nat_sub_succ_1.
Qed.

End a.

Arguments rngl_product_list_permut {T ro rp} {A eqb} Heb Hic
  (la lb)%_list.
