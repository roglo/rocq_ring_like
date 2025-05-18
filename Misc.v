(** * Misc.v

Various definitions, theorems, and notations used in the RingLike
library, some of which may eventually be incorporated into the Rocq
standard library.
*)

From Stdlib Require Import Utf8 Arith Psatz.
Import List.ListNotations.
Open Scope list.

Global Hint Resolve Nat.le_0_l : core.
Global Hint Resolve Nat.lt_0_succ : core.
Global Hint Resolve Nat.lt_succ_diag_r : core.

Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).
Notation "E ⊂ F" := (List.incl E F) (at level 70).

Notation "x ≠? y" := (negb (Nat.eqb x y)) (at level 70) : nat_scope.

Definition comp {A B C} (f : B → C) (g : A → B) x := f (g x).

(** ** flia
"fast" lia, to improve compilation speed
*)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

(* end flia *)

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat (at level 70, y at next level).

Notation "a ≡ b 'mod' c" := (a mod c = b mod c) (at level 70, b at level 36).
Notation "a ≢ b 'mod' c" := (a mod c ≠ b mod c) (at level 70, b at level 36).

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_mod_add_l_mul_r : ∀ a b c,
  (c * b + a) mod b = a mod b.
Proof.
intros.
rewrite Nat.add_comm.
apply Nat.Div0.mod_add.
Qed.

Theorem List_app_cons : ∀ A la lb (b : A), la ++ b :: lb = la ++ [b] ++ lb.
Proof. easy. Qed.

Theorem List_nth_nil : ∀ A i (d : A), List.nth i [] d = d.
Proof. now intros; destruct i. Qed.

Theorem List_nth_0_cons : ∀ A (a : A) la d, List.nth 0 (a :: la) d = a.
Proof. easy. Qed.

Theorem List_length_cons : ∀ A (a : A) la, length (a :: la) = S (length la).
Proof. easy. Qed.

Theorem List_cons_is_app : ∀ {A} (a : A) la, a :: la = [a] ++ la.
Proof. easy. Qed.

Theorem List_map_nth' : ∀ {A B} a b (f : A → B) l n,
  n < length l → List.nth n (List.map f l) b = f (List.nth n l a).
Proof.
intros * Hnl.
revert n Hnl.
induction l as [| c l]; intros; [ easy | ].
cbn in Hnl; cbn.
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hnl.
now apply IHl.
Qed.

Theorem List_fold_left_map :
  ∀ A B C (f : A → B → A) (g : C → B) (l : list C) a,
  List.fold_left f (List.map g l) a = List.fold_left (λ c b, f c (g b)) l a.
Proof.
intros.
revert a.
induction l as [| c]; intros; [ easy | apply IHl ].
Qed.

Theorem List_fold_left_ext_in : ∀ A B (f g : A → B → A) l a,
  (∀ b c, b ∈ l → f c b = g c b)
  → List.fold_left f l a = List.fold_left g l a.
Proof.
intros * Hfg.
revert a.
induction l as [| d]; intros; [ easy | cbn ].
rewrite (Hfg d a); [ | now left ].
apply IHl.
intros b c Hb.
apply Hfg.
now right.
Qed.

Theorem Nat_mul_2_l : ∀ n, 2 * n = n + n.
Proof.
intros; cbn.
now rewrite Nat.add_0_r.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_div_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.div_add; [ | easy ].
replace n with (0 + n) at 3 by easy; f_equal.
apply Nat.div_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

(** ** Iterators for aggregation operations

    The functions [iter_list] and [iter_seq] define generic iteration
    schemes over lists and integer intervals, respectively. They are
    designed to support readable notations such as:

    - [∑ (i ∈ l), f i] : list-based summation
    - [∑ (i = b, e), f i] : summation over integer ranges

    These iterators also apply to other aggregation operations:
    products (∏), maxima (Max), conjunctions (⋀).

    The Rocq system renders [iter_list] and [iter_seq] symbolically
    (∑, ∏, Max, ⋀) according to their use context.

    There are also various theorems for manipulating these
    iterators.

    These definitions and theorems are used in the following modules:

    - [[RingLike.IterAdd]]
    - [[RingLike.IterMul]]
    - [[RingLike.IterMax]]
    - [[RingLike.IterAnd]]
*)

Definition iter_list {A B} (l : list B) f (d : A) := List.fold_left f l d.

Definition iter_seq {T} b e f (d : T) := iter_list (List.seq b (S e - b)) f d.

Arguments iter_seq : simpl never.
Arguments iter_list : simpl never.

Theorem fold_iter_list : ∀ {A B} (f : A → B → A) l d,
  List.fold_left f l d = iter_list l f d.
Proof. easy. Qed.

Theorem fold_iter_seq' : ∀ A b len f (d : A),
  iter_list (List.seq b len) f d =
    if b + len =? 0 then d
    else iter_seq b (b + len - 1) f d.
Proof.
intros.
progress unfold iter_seq.
f_equal; f_equal.
remember (b + len =? 0) as x eqn:Hx; symmetry in Hx.
destruct x. {
  apply Nat.eqb_eq in Hx.
  now apply Nat.eq_add_0 in Hx; destruct Hx; subst b len.
}
apply Nat.eqb_neq in Hx.
destruct len. {
  rewrite Nat.add_0_r in Hx.
  destruct b; [ easy | cbn ].
  now rewrite Nat.add_sub, Nat.sub_diag.
}
rewrite Nat.sub_succ_l; [ cbn | flia ].
f_equal; f_equal; f_equal.
flia.
Qed.

Theorem fold_left_op_fun_from_d : ∀ {T A} d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  List.fold_left (λ (c : T) i, op c (f i)) l a =
  op a (List.fold_left (λ (c : T) i, op c (f i)) l d).
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply op_d_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite op_d_l.
apply op_assoc.
Qed.

Theorem iter_list_op_fun_from_d : ∀ T A d op a l (f : A → _)
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list l (λ (c : T) (i : A), op c (f i)) a =
  op a (iter_list l (λ (c : T) (i : A), op c (f i)) d).
Proof.
intros.
progress unfold iter_list.
revert a.
induction l as [| x l]; intros; [ symmetry; apply op_d_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite op_d_l.
apply op_assoc.
Qed.

Theorem iter_list_all_d : ∀ T A d op (l : list A) f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  (∀ i, i ∈ l → f i = d)
  → iter_list l (λ (c : T) i, op c (f i)) d = d.
Proof.
intros * op_d_l op_d_r op_assoc Hz.
progress unfold iter_list.
induction l as [| a]; [ easy | cbn ].
rewrite (fold_left_op_fun_from_d d); [ | easy | easy | easy ].
rewrite IHl. {
  rewrite op_d_l, op_d_r.
  now apply Hz; left.
}
intros i Hi.
apply Hz.
now right.
Qed.

Theorem iter_seq_all_d : ∀ T d op b e f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  (∀ i : nat, b ≤ i ≤ e → f i = d)
  → iter_seq b e (λ (c : T) (i : nat), op c (f i)) d = d.
Proof.
intros * op_d_l od_d_r op_assoc Hz.
apply iter_list_all_d; [ easy | easy | easy | ].
intros i Hi.
apply List.in_seq in Hi.
apply Hz; flia Hi.
Qed.

Theorem iter_list_split_first : ∀ T A d op l z f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  l ≠ []
  → iter_list l (λ (c : T) (i : A), op c (f i)) d =
    op (f (List.hd z l))
      (iter_list (List.tl l) (λ (c : T) (i : A), op c (f i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hl.
progress unfold iter_list.
destruct l as [| a]; [ easy | cbn ].
rewrite op_d_l.
now rewrite fold_left_op_fun_from_d with (d := d).
Qed.

Theorem iter_list_split_last : ∀ T A d (op : T → T → T) l (g : A → T) z,
  l ≠ []
  → iter_list l (λ c i, op c (g i)) d =
    op (iter_list (List.removelast l) (λ c i, op c (g i)) d)
      (g (List.last l z)).
Proof.
intros * Hlz.
progress unfold iter_list.
induction l as [| a] using List.rev_ind; [ easy | clear IHl Hlz ].
rewrite List.removelast_last.
rewrite List.last_last.
now rewrite List.fold_left_app.
Qed.

Theorem iter_seq_split_first : ∀ T d op b k g
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  b ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (g b) (iter_seq (S b) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hbk.
progress unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace (S k - S b) with (len - 1) by flia Hlen.
assert (H : len ≠ 0) by flia Hlen Hbk.
clear k Hbk Hlen.
rename H into Hlen.
destruct len; [ easy | cbn ].
rewrite op_d_l, Nat.sub_0_r.
apply fold_left_op_fun_from_d. {
  apply op_d_l.
} {
  apply op_d_r.
} {
  apply op_assoc.
}
Qed.

Theorem iter_seq_split_last : ∀ T d (op : T → T → T) b k g,
  b ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (iter_seq (S b) k (λ (c : T) (i : nat), op c (g (i - 1)%nat)) d) (g k).
Proof.
intros * Hbk.
progress unfold iter_seq, iter_list.
remember (S k - S b) as len eqn:Hlen.
rewrite Nat.sub_succ in Hlen.
replace (S k - b) with (S len) by flia Hbk Hlen.
replace k with (b + len) by flia Hbk Hlen.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
rewrite List.seq_S.
rewrite List.fold_left_app.
cbn; f_equal.
apply List_fold_left_ext_in.
intros i c Hi.
now rewrite Nat.sub_0_r.
Qed.

Theorem iter_seq_split : ∀ T d op j g b k
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
   b ≤ S j ≤ S k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (iter_seq b j (λ (c : T) (i : nat), op c (g i)) d)
      (iter_seq (j + 1) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc (Hbj, Hjk).
progress unfold iter_seq, iter_list.
remember (S j - b) as len1 eqn:Hlen1.
remember (S k - b) as len2 eqn:Hlen2.
move len2 before len1.
replace (S k - (j + 1)) with (len2 - len1) by flia Hlen1 Hlen2 Hbj.
replace (j + 1) with (b + len1) by flia Hlen1 Hbj.
assert (Hll : len1 ≤ len2) by flia Hlen1 Hlen2 Hjk.
clear - Hll op_d_l op_d_r op_assoc.
revert b len2 Hll.
induction len1; intros. {
  cbn; rewrite Nat.add_0_r, Nat.sub_0_r; symmetry.
  apply op_d_l.
}
destruct len2; [ flia Hll | ].
apply Nat.succ_le_mono in Hll; cbn.
rewrite op_d_l.
rewrite (fold_left_op_fun_from_d d _ (g b)); [ | easy | easy | easy ].
rewrite (fold_left_op_fun_from_d d _ (g b)); [ | easy | easy | easy ].
rewrite <- op_assoc; f_equal.
replace len2 with (len1 + (len2 - len1)) at 1 by flia Hll.
rewrite List.seq_app, List.fold_left_app.
rewrite (fold_left_op_fun_from_d d); [ | easy | easy | easy ].
now rewrite Nat.add_succ_comm.
Qed.

Theorem iter_seq_split3 : ∀ T d op j g b k
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  b ≤ j ≤ k
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d =
    op (op (iter_seq (S b) j (λ (c : T) (i : nat), op c (g (i - 1))) d) (g j))
      (iter_seq (j + 1) k (λ (c : T) (i : nat), op c (g i)) d).
Proof.
intros * op_d_l op_d_r op_assoc Hj.
rewrite iter_seq_split with (j := j); [ | easy | easy | easy | flia Hj ].
now rewrite iter_seq_split_last.
Qed.

Theorem iter_list_eq_compat : ∀ A B d (op : A → A → A) (l : list B) g h,
  (∀ i, i ∈ l → g i = h i)
  → iter_list l (λ c i, op c (g i)) d =
    iter_list l (λ c i, op c (h i)) d.
Proof.
intros * Hgh.
progress unfold iter_list.
revert d.
induction l as [| a]; intros; [ easy | cbn ].
rewrite Hgh; [ | now left ].
apply IHl.
intros i Hi.
apply Hgh.
now right.
Qed.

Theorem iter_seq_eq_compat : ∀ T d (op : T → T → T) b k g h,
  (∀ i, b ≤ i ≤ k → g i = h i)
  → iter_seq b k (λ c i, op c (g i)) d =
    iter_seq b k (λ c i, op c (h i)) d.
Proof.
intros * Hgh.
apply iter_list_eq_compat.
intros i Hi.
apply Hgh.
apply List.in_seq in Hi.
flia Hi.
Qed.

Theorem iter_seq_succ_succ : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) f d =
  iter_seq b k (λ c i, f c (S i)) d.
Proof.
intros.
progress unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
rewrite <- List.seq_shift.
now rewrite List_fold_left_map.
Qed.

Theorem iter_seq_succ_succ' : ∀ {T} (d : T) b k f,
  iter_seq (S b) (S k) (λ c i, f c (i - 1)) d =
  iter_seq b k (λ c i, f c i) d.
Proof.
intros.
progress unfold iter_seq, iter_list.
rewrite Nat.sub_succ.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j i Hj.
f_equal.
rewrite Nat.sub_succ.
apply Nat.sub_0_r.
Qed.

Theorem iter_list_empty : ∀ T A d (op : T → T → T) (l : list A) g,
  l = []
  → iter_list l (λ c i, op c (g i)) d = d.
Proof.
now intros * Hl; subst l.
Qed.

Theorem iter_seq_empty : ∀ T d (op : T → T → T) b k g,
  k < b
  → iter_seq b k (λ (c : T) (i : nat), op c (g i)) d = d.
Proof.
intros * Hkb.
progress unfold iter_seq.
now replace (S k - b) with 0 by flia Hkb.
Qed.

Theorem iter_list_distr : ∀ T A d op g h (l : list A)
  (op_d_l : ∀ x, op d x = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list l (λ (c : T) (i : A), op c (op (g i) (h i))) d =
  op (iter_list l (λ (c : T) (i : A), op c (g i)) d)
    (iter_list l (λ (c : T) (i : A), op c (h i)) d).
Proof.
intros.
progress unfold iter_list.
induction l as [| a]; [ symmetry; apply op_d_l | cbn ].
rewrite (fold_left_op_fun_from_d d); [ | easy | | easy ]. 2: {
  intros; rewrite op_comm; apply op_d_l.
}
symmetry.
rewrite (fold_left_op_fun_from_d d); [ | easy | | easy ]. 2: {
  intros; rewrite op_comm; apply op_d_l.
}
rewrite fold_iter_list.
rewrite (fold_left_op_fun_from_d d); [ | easy | | easy ]. 2: {
  intros; rewrite op_comm; apply op_d_l.
}
rewrite IHl.
do 2 rewrite fold_iter_list.
remember (iter_list _ _ _) as b eqn:Hb in |-*.
remember (iter_list _ _ _) as c eqn:Hc in |-*.
do 3 rewrite op_d_l.
do 2 rewrite op_assoc.
f_equal.
symmetry.
rewrite (op_comm _ b).
rewrite op_assoc.
f_equal.
apply op_comm.
Qed.

Theorem iter_seq_distr : ∀ T d op g h b k
  (op_d_l : ∀ x, op d x = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_seq b k (λ (c : T) (i : nat), (op c (op (g i) (h i)))) d =
  op
    (iter_seq b k (λ (c : T) (i : nat), op c (g i)) d)
    (iter_seq b k (λ (c : T) (i : nat), op c (h i)) d).
Proof.
intros.
now apply iter_list_distr.
Qed.

Theorem iter_list_inv : ∀ T A d op inv (f : A → T) l
  (inv_op_distr : ∀ a b, inv (op a b) = op (inv a) (inv b)),
  inv (iter_list l (λ (c : T) i, op c (f i)) d) =
  iter_list l (λ (c : T) i, op c (inv (f i))) (inv d).
Proof.
intros.
progress unfold iter_list.
revert d.
induction l as [| a la]; intros; [ easy | cbn ].
rewrite IHla.
now rewrite inv_op_distr.
Qed.

Theorem iter_shift : ∀ {T} s b k f (d : T),
  s ≤ b ≤ k
  → iter_seq b k f d =
    iter_seq (b - s) (k - s) (λ c i, f c (s + i)) d.
Proof.
intros * (Hsb, Hbk).
progress unfold iter_seq, iter_list.
replace (S (k - s) - (b - s)) with (S (k - b)) by flia Hsb Hbk.
rewrite <- Nat.sub_succ_l; [ | easy ].
remember (S k - b)%nat as len; clear Heqlen.
clear k Hbk.
revert b d Hsb.
induction len; intros; [ easy | ].
rewrite List.seq_S; symmetry.
rewrite List.seq_S; symmetry.
do 2 rewrite List.fold_left_app; cbn.
rewrite IHlen; [ | easy ].
now replace (s + (b - s + len)) with (b + len) by flia Hsb.
Qed.

Theorem iter_rshift : ∀ {T} s b k f (d : T),
  iter_seq b k f d =
  iter_seq (s + b) (s + k) (λ c i, f c (i - s)) d.
Proof.
intros.
progress unfold iter_seq, iter_list.
replace (S (s + k) - (s + b)) with (S k - b) by flia.
remember (S k - b)%nat as len; clear Heqlen.
clear k.
revert b d.
induction len; intros; [ easy | ].
rewrite List.seq_S; symmetry.
rewrite List.seq_S; symmetry.
do 2 rewrite List.fold_left_app; cbn.
rewrite IHlen.
rewrite Nat.add_comm.
rewrite Nat.add_shuffle0.
rewrite Nat.add_sub.
easy.
Qed.

Theorem iter_seq_inv : ∀ T d op inv b e f
  (inv_op_distr : ∀ a b, inv (op a b) = op (inv a) (inv b)),
  inv (iter_seq b e (λ (c : T) (i : nat), op c (f i)) d) =
  iter_seq b e (λ (c : T) (i : nat), op c (inv (f i))) (inv d).
Proof.
intros.
now apply iter_list_inv.
Qed.

Theorem iter_seq_rtl : ∀ T d op b k f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_seq b k (λ (c : T) (i : nat), op c (f i)) d =
  iter_seq b k (λ (c : T) (i : nat), op c (f (k + b - i))) d.
Proof.
intros.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  progress unfold iter_seq.
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
progress unfold iter_seq, iter_list.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen.
clear Hlen Hkb.
revert b.
induction len; intros; [ easy | ].
rewrite List.seq_S at 1; cbn.
rewrite List.fold_left_app; cbn.
symmetry.
rewrite fold_left_op_fun_from_d with (d := d); [ | easy | easy | easy ].
rewrite op_comm.
f_equal; [ | rewrite op_d_l; f_equal; flia ].
rewrite IHlen.
rewrite <- List.seq_shift.
rewrite List_fold_left_map.
apply List_fold_left_ext_in.
intros j c Hj.
apply List.in_seq in Hj.
f_equal; f_equal; flia.
Qed.

Theorem if_bool_if_dec : ∀ A (b : bool) (x y : A),
  (if b then x else y) =
  if Sumbool.sumbool_of_bool b then x else y.
Proof.
intros.
now destruct (Sumbool.sumbool_of_bool b); subst b.
Qed.

(* conversions if ...? into if ..._dec *)

Theorem if_eqb_eq_dec : ∀ {A} i j (a b : A),
  (if i =? j then a else b) = (if Nat.eq_dec i j then a else b).
Proof.
intros.
destruct (Nat.eq_dec i j) as [H1| H1]. {
  now apply Nat.eqb_eq in H1; rewrite H1.
}
now apply Nat.eqb_neq in H1; rewrite H1.
Qed.

Theorem if_ltb_lt_dec : ∀ A i j (a b : A),
  (if i <? j then a else b) = (if lt_dec i j then a else b).
Proof.
intros.
destruct (lt_dec i j) as [H1| H1]. {
  now apply Nat.ltb_lt in H1; rewrite H1.
}
now apply Nat.ltb_nlt in H1; rewrite H1.
Qed.

Theorem if_leb_le_dec : ∀ A i j (a b : A),
  (if i <=? j then a else b) = (if le_dec i j then a else b).
Proof.
intros.
destruct (le_dec i j) as [H1| H1]. {
  now apply Nat.leb_le in H1; rewrite H1.
}
now apply Nat.leb_nle in H1; rewrite H1.
Qed.

(* *)

Theorem iter_list_only_one : ∀ T A d (op : T → T → T) (g : A → T) a,
  op d (g a) = g a
  → iter_list [a] (λ c i, op c (g i)) d = g a.
Proof.
intros * Ha.
now progress unfold iter_list; cbn.
Qed.

Theorem iter_seq_only_one : ∀ T d (op : T → T → T) g n,
  op d (g n) = g n
  → iter_seq n n (λ c i, op c (g i)) d = g n.
Proof.
intros * op_d_l.
progress unfold iter_seq.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag.
apply iter_list_only_one.
now apply iter_list_only_one.
Qed.

Theorem iter_list_cons : ∀ A B d op (a : B) la f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  iter_list (a :: la) (λ (c : A) i, op c (f i)) d =
  op (f a) (iter_list la (λ (c : A) i, op c (f i)) d).
Proof.
intros.
progress unfold iter_list; cbn.
rewrite op_d_l.
now apply (fold_left_op_fun_from_d d).
Qed.

Theorem iter_list_app : ∀ A B (d : A) (f : A → B → A) la lb,
  iter_list (la ++ lb) f d = iter_list lb f (iter_list la f d).
Proof.
intros.
progress unfold iter_list.
now rewrite List.fold_left_app.
Qed.

Definition equality {A} (eqb : A → A → bool) := ∀ a b, eqb a b = true ↔ a = b.

Theorem iter_list_seq : ∀ T d (op : T → T → T) b len f,
  len ≠ 0
  → iter_list (List.seq b len) (λ c i, op c (f i)) d =
    iter_seq b (b + len - 1) (λ c i, op c (f i)) d.
Proof.
intros * Hlen.
progress unfold iter_seq.
f_equal; f_equal.
flia Hlen.
Qed.

Theorem List_flat_length_map : ∀ A B (f : A → list B) l,
  length (List.flat_map f l) = iter_list l (fun c a => c + length (f a)) 0.
Proof.
intros.
induction l as [| a]; [ now rewrite iter_list_empty | cbn ].
rewrite List.length_app.
rewrite iter_list_cons; cycle 1. {
  apply Nat.add_0_l.
} {
  apply Nat.add_0_r.
} {
  apply Nat.add_assoc.
}
now cbn; f_equal.
Qed.

(** ** cart_prod

Cartesian product of several lists
*)

Fixpoint cart_prod {A} (ll : list (list A)) :=
  match ll with
  | [] => [[]]
  | l :: ll' => List.flat_map (λ a, List.map (cons a) (cart_prod ll')) l
  end.

Theorem cart_prod_length : ∀ A (ll : list (list A)),
  ll ≠ []
  → length (cart_prod ll) = iter_list ll (fun c l => c * length l) 1.
Proof.
intros * Hll.
revert Hll.
induction ll as [| l1]; intros; [ easy | clear Hll; cbn ].
rewrite iter_list_cons; cycle 1. {
  apply Nat.mul_1_l.
} {
  apply Nat.mul_1_r.
} {
  apply Nat.mul_assoc.
}
rewrite List_flat_length_map.
erewrite iter_list_eq_compat. 2: {
  intros i Hi.
  now rewrite List.length_map.
}
cbn.
destruct ll as [| l2]. {
  rewrite iter_list_empty with (l := []); [ | easy ].
  rewrite Nat.mul_1_r; cbn.
  induction l1 as [| a]; [ easy | ].
  rewrite iter_list_cons; cycle 1.
    apply Nat.add_0_l.
    apply Nat.add_0_r.
    apply Nat.add_assoc.
  now cbn; rewrite IHl1.
}
rewrite IHll; [ | easy ].
induction l1 as [| a]; [ easy | ].
rewrite iter_list_cons; cycle 1.
  apply Nat.add_0_l.
  apply Nat.add_0_r.
  apply Nat.add_assoc.
now cbn; rewrite IHl1.
Qed.

Theorem in_cart_prod_length : ∀ A (ll : list (list A)) l,
  l ∈ cart_prod ll → length l = length ll.
Proof.
intros * Hl.
revert l Hl.
induction ll as [| l1]; intros. {
  cbn in Hl.
  destruct Hl as [Hl| Hl]; [ now subst l | easy ].
}
cbn in Hl.
apply List.in_flat_map in Hl.
destruct Hl as (a & Hl1 & Ha).
apply List.in_map_iff in Ha.
destruct Ha as (l3 & Hl & Hl3).
subst l; cbn; f_equal.
now apply IHll.
Qed.

Theorem List_nth_succ_cons : ∀ {A} (a : A) la i,
  List.nth (S i) (a :: la) = List.nth i la.
Proof. easy. Qed.

Theorem nth_in_cart_prod : ∀ A (d : A) ll l i,
  i < length ll
  → l ∈ cart_prod ll
  → List.nth i l d ∈ List.nth i ll [].
Proof.
intros * Hi Hll.
revert l i Hi Hll.
induction ll as [| l1]; intros; [ easy | ].
cbn in Hll |-*.
destruct i. {
  destruct ll as [| l2]. {
    apply List.in_flat_map in Hll.
    destruct Hll as (a & Ha & Hla).
    apply List.in_map_iff in Hla.
    now destruct Hla as (l2 & H & Hl2); subst l.
  }
  apply List.in_flat_map in Hll.
  destruct Hll as (a & Hl1 & Hl).
  apply List.in_map_iff in Hl.
  now destruct Hl as (l3 & H & Hl3); subst l.
}
cbn in Hi; apply Nat.succ_lt_mono in Hi.
destruct ll as [| l2]; [ easy | ].
apply List.in_flat_map in Hll.
destruct Hll as (a & Ha & Hl).
apply List.in_map_iff in Hl.
destruct Hl as (l3 & H & Hl3); subst l.
rewrite List_nth_succ_cons.
now apply IHll.
Qed.

Theorem in_cart_prod_iff : ∀ {A} (d : A) ll la,
  la ∈ cart_prod ll
  ↔ length la = length ll ∧
    ∀ i, i < length la → List.nth i la d ∈ List.nth i ll [].
Proof.
intros.
split. {
  intros Hla.
  split; [ now apply in_cart_prod_length in Hla | ].
  intros i Hi.
  apply nth_in_cart_prod; [ | easy ].
  apply in_cart_prod_length in Hla.
  congruence.
} {
  intros (Hla & Hnth).
  revert la Hla Hnth.
  induction ll as [| lb]; intros. {
    now apply List.length_zero_iff_nil in Hla; subst la; left.
  }
  cbn.
  destruct la as [| a]; [ easy | ].
  cbn in Hla; apply Nat.succ_inj in Hla.
  apply List.in_flat_map.
  exists a.
  specialize (Hnth 0 (Nat.lt_0_succ _)) as H1; cbn in H1.
  split; [ easy | ].
  apply List.in_map_iff.
  exists la.
  split; [ easy | ].
  apply IHll; [ easy | ].
  intros i Hi.
  specialize (Hnth (S i)) as H2.
  cbn in H2.
  apply Nat.succ_lt_mono in Hi.
  now specialize (H2 Hi).
}
Qed.

(** ** extract

Like "find" but returning all details:
- what is before
- the value found
- what is after *)

Fixpoint extract {A} (f : A → bool) l :=
  match l with
  | [] => None
  | a :: la =>
      if f a then Some ([], a, la)
      else
        match extract f la with
        | None => None
        | Some (bef, b, aft) => Some (a :: bef, b, aft)
        end
  end.

Theorem extract_Some_iff : ∀ A (f : A → _) l a bef aft,
  extract f l = Some (bef, a, aft)
  ↔ (∀ x, x ∈ bef → f x = false) ∧ f a = true ∧ l = bef ++ a :: aft.
Proof.
intros.
split. {
  intros He.
  revert a bef aft He.
  induction l as [| b]; intros; [ easy | cbn ].
  cbn in He.
  remember (f b) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb. {
    now injection He; clear He; intros; subst bef b aft.
  }
  remember (extract f l) as lal eqn:Hlal; symmetry in Hlal.
  destruct lal as [((bef', x), aft') | ]; [ | easy ].
  injection He; clear He; intros; subst bef x aft'.
  rename bef' into bef.
  specialize (IHl _ _ _ eq_refl) as H1.
  destruct H1 as (H1 & H2 & H3).
  split. {
    intros c Hc.
    destruct Hc as [Hc| Hc]; [ now subst c | ].
    now apply H1.
  }
  split; [ easy | ].
  now cbn; f_equal.
} {
  intros He.
  destruct He as (Hbef & Hf & Hl).
  subst l.
  revert a aft Hf.
  induction bef as [| b]; intros; cbn; [ now rewrite Hf | ].
  rewrite Hbef; [ | now left ].
  rewrite IHbef; [ easy | | easy ].
  now intros c Hc; apply Hbef; right.
}
Qed.

Theorem extract_None_iff : ∀ {A} (f : A → _) l,
  extract f l = None ↔ ∀ a, a ∈ l → f a = false.
Proof.
intros.
split. {
  intros He * Ha.
  revert a Ha.
  induction l as [| b]; intros; [ easy | ].
  cbn in He.
  remember (f b) as fb eqn:Hfb; symmetry in Hfb.
  destruct fb; [ easy | ].
  destruct Ha as [Ha| Ha]; [ now subst b | ].
  apply IHl; [ | easy ].
  now destruct (extract f l) as [((bef, x), aft)| ].
} {
  intros Hf.
  induction l as [| a]; [ easy | cbn ].
  rewrite Hf; [ | now left ].
  rewrite IHl; [ easy | ].
  intros c Hc.
  now apply Hf; right.
}
Qed.

Theorem equality_refl {A} {eqb : A → _} : equality eqb → ∀ a, eqb a a = true.
Proof.
intros * Heqb *.
now apply Heqb.
Qed.

(* *)

Theorem NoDup_app_comm {A} : ∀ l l' : list A,
  List.NoDup (l ++ l') → List.NoDup (l' ++ l).
Proof.
intros * Hll.
revert l Hll.
induction l' as [| a l']; intros; [ now rewrite List.app_nil_r in Hll | ].
cbn; constructor. {
  intros Ha.
  apply List.NoDup_remove_2 in Hll; apply Hll.
  apply List.in_app_or in Ha.
  apply List.in_or_app.
  now destruct Ha; [ right | left ].
}
apply IHl'.
now apply List.NoDup_remove_1 in Hll.
Qed.

Theorem NoDup_app_remove_l :
  ∀ A (l l' : list A), List.NoDup (l ++ l') → List.NoDup l'.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
revert l Hnd.
induction l' as [| b]; intros; [ constructor | ].
cbn in Hnd.
apply List.NoDup_cons_iff in Hnd.
destruct Hnd as (H1, H2).
constructor; [ | now apply IHl' in H2 ].
intros H; apply H1.
now apply List.in_or_app; left.
Qed.

Theorem NoDup_app_remove_r :
  ∀ A (l l' : list A), List.NoDup (l ++ l') → List.NoDup l.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
now apply NoDup_app_remove_l in Hnd.
Qed.

Theorem NoDup_app_iff : ∀ A (l l' : list A),
  List.NoDup (l ++ l') ↔
    List.NoDup l ∧ List.NoDup l' ∧ (∀ a, a ∈ l → a ∉ l').
Proof.
intros.
split. {
  intros Hnd.
  split; [ now apply NoDup_app_remove_r in Hnd | ].
  split; [ now apply NoDup_app_remove_l in Hnd | ].
  intros a Ha Ha'.
  revert l' Hnd Ha'.
  induction l as [| b]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. {
    subst b.
    apply NoDup_app_comm in Hnd.
    apply List.NoDup_remove_2 in Hnd.
    apply Hnd.
    now apply List.in_app_iff; left.
  }
  apply (IHl Ha l'); [ | easy ].
  cbn in Hnd.
  now apply List.NoDup_cons_iff in Hnd.
} {
  intros * (Hnl & Hnl' & Hll).
  revert l' Hnl' Hll.
  induction l as [| b l]; intros; [ easy | cbn ].
  constructor. {
    intros Hb.
    apply List.in_app_or in Hb.
    destruct Hb as [Hb| Hb]. {
      now apply List.NoDup_cons_iff in Hnl.
    } {
      now specialize (Hll b (or_introl eq_refl)) as H1.
    }
  } {
    apply List.NoDup_cons_iff in Hnl.
    apply IHl; [ easy | easy | ].
    intros a Ha.
    now apply Hll; right.
  }
}
Qed.

(** ** List_rank

Rank of the first element satisfying a predicate
Like "find" but returning the rank, not the element itself *)

Fixpoint List_rank_loop i [A] (f : A → bool) (l : list A) : nat :=
  match l with
  | [] => i
  | x :: tl => if f x then i else List_rank_loop (S i) f tl
end.

Definition List_rank [A] := @List_rank_loop 0 A.

Theorem List_rank_loop_interv : ∀ {A} f (l : list A) i,
  i ≤ List_rank_loop i f l ≤ i + length l.
Proof.
intros.
revert i.
induction l as [| a]; intros; cbn; [ now rewrite Nat.add_0_r | ].
destruct (f a). {
  split; [ easy | ].
  apply Nat.le_add_r.
}
specialize (IHl (S i)).
rewrite Nat.add_succ_comm in IHl.
split; [ flia IHl | easy ].
Qed.

Theorem List_rank_loop_if : ∀ A d f (l : list A) i j,
  List_rank_loop i f l = j
  → (∀ k, i ≤ k < j → f (List.nth (k - i) l d) = false) ∧
    (j < i + length l ∧ f (List.nth (j - i) l d) = true ∨
     j = i + length l).
Proof.
intros * Hi.
split. {
  intros p Hp.
  remember (p - i) as k eqn:Hk.
  replace p with (i + k) in Hp by flia Hp Hk.
  destruct Hp as (_, Hp).
  clear p Hk.
  revert i l Hi Hp.
  induction k; intros. {
    rewrite Nat.add_0_r in Hp.
    destruct l as [| a]. {
      now subst j; apply Nat.lt_irrefl in Hp.
    }
    cbn in Hi |-*.
    destruct (f a); [ | easy ].
    now subst j; apply Nat.lt_irrefl in Hp.
  }
  destruct l as [| a]; [ subst j; cbn in Hp; flia Hp | ].
  cbn in Hi |-*.
  rewrite <- Nat.add_succ_comm in Hp.
  remember (f a) as b eqn:Hb; symmetry in Hb.
  destruct b; [ subst j; flia Hp | ].
  now apply IHk with (i := S i).
}
remember (j - i) as k eqn:Hk.
replace j with (i + k) in Hi |-*. 2: {
  specialize (List_rank_loop_interv f l i) as H1.
  rewrite Hi in H1.
  flia Hk H1.
}
clear j Hk.
revert i l Hi.
induction k; intros. {
  rewrite Nat.add_0_r in Hi |-*.
  destruct l; [ now right; symmetry; apply Nat.add_0_r | ].
  left; cbn in Hi |-*.
  split; [ flia | ].
  destruct (f a); [ easy | ].
  specialize (List_rank_loop_interv f l (S i)) as H1.
  rewrite Hi in H1; flia H1.
}
destruct l; cbn in Hi; [ flia Hi | ].
destruct (f a); [ flia Hi | cbn in Hi ].
rewrite <- Nat.add_succ_comm in Hi.
apply IHk in Hi; cbn.
now do 2 rewrite <- Nat.add_succ_comm.
Qed.

Theorem List_rank_if : ∀ {A} d f (l : list A) {i},
  List_rank f l = i
  → (∀ j, j < i → f (List.nth j l d) = false) ∧
    (i < length l ∧ f (List.nth i l d) = true ∨ i = length l).
Proof.
intros * Hi.
apply List_rank_loop_if with (d := d) in Hi.
rewrite Nat.sub_0_r in Hi; cbn in Hi.
destruct Hi as (Hbef, Hat).
split; [ | easy ].
intros j Hj.
specialize (Hbef j).
rewrite Nat.sub_0_r in Hbef.
now apply Hbef.
Qed.

(* end List_rank *)

Definition unsome {A} (d : A) o :=
  match o with
  | Some x => x
  | None => d
  end.

Theorem List_seq_cut3 : ∀ i sta len,
  i ∈ List.seq sta len
  → List.seq sta len =
      List.seq sta (i - sta) ++ [i] ++ List.seq (S i) (sta + len - S i).
Proof.
intros * His.
apply List.in_seq in His.
replace len with (i - sta + (len - (i - sta))) at 1 by flia His.
rewrite List.seq_app.
f_equal.
replace (sta + (i - sta)) with i by flia His.
replace (len - (i - sta)) with (1 + (sta + len - S i)) by flia His.
rewrite List.seq_app; cbn.
now rewrite Nat.add_1_r.
Qed.

Theorem List_app_eq_app' :
  ∀ (X : Type) (x1 x2 y1 y2 : list X),
    length x1 = length y1
    → x1 ++ x2 = y1 ++ y2
    → x1 = y1 ∧ x2 = y2.
Proof.
intros * Hxy Haa.
revert x2 y1 y2 Hxy Haa.
induction x1 as [| a1]; intros; cbn. {
  cbn in Hxy, Haa.
  symmetry in Hxy; apply List.length_zero_iff_nil in Hxy.
  now subst x2 y1.
}
destruct y1 as [| b1]; [ easy | ].
injection Haa; clear Haa; intros H1 H2; subst b1.
cbn in Hxy.
apply Nat.succ_inj in Hxy.
specialize (IHx1 x2 y1 y2 Hxy H1).
now destruct IHx1; subst y1 y2.
Qed.

Theorem List_skipn_is_cons : ∀ {A} (d : A) la n,
  n < length la
  → List.skipn n la = List.nth n la d :: List.skipn (S n) la.
Proof.
intros * Hn.
revert n Hn.
induction la as [| a]; intros; [ easy | ].
destruct n; [ easy | ].
cbn in Hn; apply Nat.succ_lt_mono in Hn.
rewrite List_nth_succ_cons.
do 2 rewrite List.skipn_cons.
now apply IHla.
Qed.

Theorem List_nth_skipn : ∀ A (l : list A) i j d,
  List.nth i (List.skipn j l) d = List.nth (i + j) l d.
Proof.
intros.
revert i j.
induction l as [| a la]; intros. {
  rewrite List.skipn_nil; cbn.
  now destruct i, j.
}
destruct j; [ now rewrite Nat.add_0_r | ].
rewrite Nat.add_succ_r; cbn.
apply IHla.
Qed.

Theorem List_length_map_seq : ∀ A (f : _ → A) a len,
  length (List.map f (List.seq a len)) = len.
Proof.
intros.
now rewrite List.length_map, List.length_seq.
Qed.

Theorem List_map_nth_seq : ∀ {A} d (la : list A),
  la = List.map (λ i, List.nth i la d) (List.seq 0 (length la)).
Proof.
intros.
induction la as [| a]; [ easy | ].
cbn; f_equal.
rewrite <- List.seq_shift.
now rewrite List.map_map.
Qed.

Theorem List_last_nth : ∀ A (la : list A) d,
  List.last la d = List.nth (length la - 1) la d.
Proof.
intros.
destruct la as [| a] using List.rev_ind; [ easy | cbn ].
rewrite List.last_last, List.length_app, Nat.add_sub.
rewrite List.app_nth2; [ | now progress unfold ge ].
now rewrite Nat.sub_diag.
Qed.

Theorem List_eq_rev_nil {A} : ∀ (l : list A), List.rev l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a]; [ easy | cbn in Hl ].
now apply List.app_eq_nil in Hl.
Qed.

Theorem List_last_rev : ∀ A (l : list A) d,
  List.last (List.rev l) d = List.hd d l.
Proof.
intros.
destruct l as [| a]; [ easy | apply List.last_last ].
Qed.

Theorem List_rev_symm :
  ∀ A (la lb : list A), List.rev la = lb → la = List.rev lb.
Proof.
intros * Hab.
now subst lb; rewrite List.rev_involutive.
Qed.

Theorem List_nth_app_repeat_r :
  ∀ A (d : A) i n la,
  List.nth i (la ++ List.repeat d n) d = List.nth i la d.
Proof.
intros.
destruct (lt_dec i (length la)) as [Hila| Hila]. {
  now apply List.app_nth1.
}
apply Nat.nlt_ge in Hila.
rewrite List.app_nth2; [ | easy ].
now rewrite List.nth_repeat, List.nth_overflow.
Qed.

Theorem min_add_sub_max : ∀ a b, min (a + (b - a)) (b + (a - b)) = max a b.
Proof.
intros.
destruct (le_dec a b) as [Hab| Hab]. {
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite Nat.add_0_r, Nat.min_id; symmetry.
  now apply Nat.max_r.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab.
  rewrite Nat.min_comm, Nat.max_comm.
  rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite Nat.add_0_r, Nat.min_id; symmetry.
  now apply Nat.max_r.
}
Qed.

(** ** List_map2

Map with two lists
*)

Fixpoint List_map2 {A B C} (f : A → B → C) la lb :=
  match la with
  | [] => []
  | a :: la' =>
      match lb with
      | [] => []
      | b :: lb' => f a b :: List_map2 f la' lb'
      end
  end.

Theorem List_map2_nil_l : ∀ A B C (f : A → B → C) la, List_map2 f [] la = [].
Proof.
intros.
now destruct la.
Qed.

Theorem List_map2_nil_r : ∀ A B C (f : A → B → C) la, List_map2 f la [] = [].
Proof.
intros.
now destruct la.
Qed.

Theorem List_map2_nth : ∀ {A B C} a b c (f : A → B → C) la lb n,
  n < length la
  → n < length lb
  → List.nth n (List_map2 f la lb) c = f (List.nth n la a) (List.nth n lb b).
Proof.
intros * Hla Hlb.
revert n lb Hla Hlb.
induction la as [| a']; intros; [ easy | cbn ].
destruct lb as [| b']; [ easy | cbn ].
destruct n; [ easy | cbn ].
cbn in Hla, Hlb.
apply Nat.succ_lt_mono in Hla.
apply Nat.succ_lt_mono in Hlb.
destruct n; [ now apply IHla | ].
now apply IHla.
Qed.

Theorem List_map2_map_l :
  ∀ A B C D (f : C → B → D) g (la : list A) (lb : list B),
  List_map2 f (List.map g la) lb = List_map2 (λ a b, f (g a) b) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_map2_map_r :
  ∀ A B C D (f : A → C → D) g (la : list A) (lb : list B),
  List_map2 f la (List.map g lb) = List_map2 (λ a b, f a (g b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_map_map2 : ∀ A B C D (f : A → B) (g : C → D → A) la lb,
  List.map f (List_map2 g la lb) = List_map2 (λ a b, f (g a b)) la lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem List_fold_left_map2 :
  ∀ A B C D (f : A → B → A) (g : C → D → B) lc ld (a : A),
  List.fold_left f (List_map2 g lc ld) a =
  List.fold_left (λ b c, f b (g (fst c) (snd c))) (List.combine lc ld) a.
Proof.
intros.
revert ld a.
induction lc as [| c]; intros; [ easy | cbn ].
destruct ld as [| d]; [ easy | cbn ].
apply IHlc.
Qed.

Theorem List_length_map2 : ∀ A B C (f : A → B → C) la lb,
  length (List_map2 f la lb) = min (length la) (length lb).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem List_in_map2_iff : ∀ A B C (f : A → B → C) la lb c,
  c ∈ List_map2 f la lb ↔
  ∃ i,
  i < min (length la) (length lb) ∧
  ∃ a b, f (List.nth i la a) (List.nth i lb b) = c.
Proof.
intros.
split. {
  intros Hc.
  revert lb Hc.
  induction la as [| a]; intros; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  cbn in Hc.
  destruct Hc as [Hc| Hc]. {
    exists 0.
    split; [ cbn; flia | now exists a, b ].
  }
  specialize (IHla _ Hc) as H1.
  destruct H1 as (i & Him & a' & b' & Hi).
  exists (S i).
  split; [ cbn; flia Him | ].
  now exists a', b'.
} {
  intros (i & Him & a' & b' & Hi).
  revert lb i Him Hi.
  induction la as [| a]; intros; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  cbn in Him, Hi |-*.
  destruct i; [ now left | right ].
  apply Nat.succ_lt_mono in Him.
  now apply IHla in Hi.
}
Qed.

Theorem List_map2_ext_in : ∀ A B C (f g : A → B → C) la lb,
  (∀ ab, ab ∈ List.combine la lb → f (fst ab) (snd ab) = g (fst ab) (snd ab))
  → List_map2 f la lb = List_map2 g la lb.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
f_equal. {
  apply (Hab _ (or_introl eq_refl)).
}
apply IHla.
intros i Hi.
now apply Hab; right.
Qed.

Theorem List_in_combine_same :
  ∀ A (i j : A) l, (i, j) ∈ List.combine l l → i = j.
Proof.
intros * Hij.
induction l as [| a la]; [ easy | cbn in Hij ].
destruct Hij as [Hij| Hij]; [ now injection Hij; intros; subst i j | ].
now apply IHla.
Qed.

Theorem List_map2_diag : ∀ A B (f : A → A → B) la,
  List_map2 f la la = List.map (λ i, f i i) la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
now rewrite IHla.
Qed.

Theorem List_map2_map2_seq_l : ∀ {A B C} d (f : A → B → C) la lb,
  List_map2 f la lb =
    List_map2 (λ i b, f (List.nth i la d) b) (List.seq 0 (length la)) lb.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | ].
f_equal.
rewrite <- List.seq_shift.
rewrite List_map2_map_l.
apply IHla.
Qed.

Theorem List_map2_map2_seq_r : ∀ {A B C} d (f : A → B → C) la lb,
  List_map2 f la lb =
    List_map2 (λ a i, f a (List.nth i lb d)) la (List.seq 0 (length lb)).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
rewrite <- List.seq_shift.
rewrite List_map2_map_r.
apply IHla.
Qed.

Theorem List_map2_app_l : ∀ A B C l1 l2 l (f : A → B → C),
  List_map2 f (l1 ++ l2) l =
    List_map2 f l1 (List.firstn (length l1) l) ++
    List_map2 f l2 (List.skipn (length l1) l).
Proof.
intros.
revert l2 l.
induction l1 as [| a1]; intros; [ easy | cbn ].
destruct l as [| a]; [ now rewrite List_map2_nil_r | cbn ].
f_equal.
apply IHl1.
Qed.

Theorem List_map2_swap : ∀ A B C (f : A → B → C) la lb,
  List_map2 f la lb = List_map2 (λ a b, f b a) lb la.
Proof.
intros.
revert lb.
induction la as [| a]; intros; cbn; [ symmetry; apply List_map2_nil_r | ].
destruct lb as [| b]; [ easy | cbn ].
f_equal.
apply IHla.
Qed.

Theorem List_map2_rev_seq_r : ∀ A B (f : A → _ → B) la sta len,
  List_map2 f la (List.rev (List.seq sta len)) =
  List_map2 (λ a i, f a (2 * sta + len - 1 - i)) la (List.seq sta len).
Proof.
intros.
rewrite List_map2_swap; symmetry.
rewrite List_map2_swap; symmetry.
revert la sta.
induction len; intros; [ easy | ].
replace (2 * sta + S len - 1) with (2 * sta + len) by flia.
rewrite List.seq_S at 1.
cbn - [ List_map2 ].
rewrite Nat.add_0_r.
rewrite List.rev_app_distr.
cbn - [ List_map2 ].
cbn.
destruct la as [| a]; [ easy | ].
rewrite Nat.add_shuffle0, Nat.add_sub; f_equal.
rewrite IHlen.
rewrite <- List.seq_shift.
rewrite List_map2_map_l.
clear a.
apply List_map2_ext_in.
intros (i, a) Hia; cbn.
f_equal; flia.
Qed.

Theorem List_map_seq : ∀ A (f : _ → A) sta len,
  List.map f (List.seq sta len) =
    List.map (λ i, f (sta + i)) (List.seq 0 len).
Proof.
intros.
revert sta.
induction len; intros; [ easy | cbn ].
symmetry.
rewrite <- List.seq_shift, List.map_map.
rewrite Nat.add_0_r; f_equal.
symmetry.
rewrite IHlen.
apply List.map_ext_in.
intros i Hi.
now rewrite Nat.add_succ_comm.
Qed.

Theorem List_map2_map_min :
  ∀ {A B C} ad bd la lb (f : A → B → C),
  List_map2 f la lb =
    List.map (λ i, f (List.nth i la ad) (List.nth i lb bd))
      (List.seq 0 (min (length la) (length lb))).
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | ].
destruct lb as [| b]; [ easy | ].
cbn - [ List.nth ].
do 2 rewrite List_nth_0_cons.
f_equal.
rewrite List_map_seq.
rewrite IHla.
apply List.map_ext_in.
intros i Hi.
do 2 rewrite List_nth_succ_cons.
easy.
Qed.

Theorem List_map2_app_app :
  ∀ A B C la lb lc ld (f : A → B → C),
  length la = length lb
  → List_map2 f (la ++ lc) (lb ++ ld) =
    List_map2 f la lb ++ List_map2 f lc ld.
Proof.
intros * Hab.
revert lb lc ld Hab.
induction la as [| a]; intros; cbn. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab; f_equal.
now apply IHla.
Qed.

Theorem List_rev_map2 : ∀ A B C (f : A → B → C) la lb,
  length la = length lb
  → List.rev (List_map2 f la lb) = List_map2 f (List.rev la) (List.rev lb).
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ easy | cbn ].
destruct lb as [| b]; cbn; [ symmetry; apply List_map2_nil_r | ].
cbn in Hab; apply Nat.succ_inj in Hab.
rewrite (IHla _ Hab).
rewrite List_map2_app_l.
rewrite List.firstn_app.
do 2 rewrite List.length_rev.
rewrite Hab, Nat.sub_diag; cbn.
rewrite List.app_nil_r.
rewrite <- (List.length_rev lb).
rewrite List.firstn_all.
f_equal.
rewrite List.length_rev.
rewrite List.skipn_app.
rewrite List.length_rev, Nat.sub_diag; cbn.
rewrite <- (List.length_rev lb).
rewrite List.skipn_all.
easy.
Qed.

Theorem List_eq_map2_nil : ∀ A B C (f : A → B → C) la lb,
  List_map2 f la lb = [] → la = [] ∨ lb = [].
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros; [ now left | right ].
cbn in Hab.
now destruct lb.
Qed.

(* end List_map2 *)

Definition bool_of_sumbool {A B : Prop} (P : sumbool A B) :=
  match P with
  | left _ _ => true
  | right _ _ => false
  end.

Definition sumbool_or {A B C D : Prop} (P : sumbool A B) (Q : sumbool C D) :=
  orb (bool_of_sumbool P) (bool_of_sumbool Q).

Definition sumbool_and {A B C D : Prop} (P : sumbool A B) (Q : sumbool C D) :=
  andb (bool_of_sumbool P) (bool_of_sumbool Q).

Notation "a ∨∨ b" := (sumbool_or a b) (at level 85).
Notation "a ∧∧ b" := (sumbool_and a b) (at level 80).

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_succ_sub_succ_r : ∀ a b, b < a → a - b = S (a - S b).
Proof. intros * Hba; flia Hba. Qed.

(** ** binomial *)

Fixpoint binomial n k :=
  match k with
  | 0 => 1
  | S k' =>
      match n with
      | 0 => 0
      | S n' => binomial n' k' + binomial n' k
     end
  end.

Theorem binomial_succ_succ : ∀ n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. easy. Qed.

Theorem binomial_lt : ∀ n k, n < k → binomial n k = 0.
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; [ now destruct k | cbn ].
destruct k; [ flia Hnk | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | easy ].
rewrite Nat.add_0_l.
apply IHn; flia Hnk.
Qed.

Theorem binomial_succ_diag_r : ∀ n, binomial n (S n) = 0.
Proof.
intros.
apply binomial_lt; flia.
Qed.

(* end binomial *)

Theorem fold_not : ∀ (P : Prop), not P → P → False.
Proof. easy. Qed.

Theorem Tauto_match_nat_same : ∀ A a (b : A),
  match a with 0 => b | S _ => b end = b.
Proof. now intros; destruct a. Qed.
