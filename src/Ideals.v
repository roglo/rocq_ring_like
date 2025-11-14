(** * Ideals

Ideals as a ring-like algebra.
*)

(* ideals on a RingLike *)

Set Nested Proofs Allowed.
Require Import Stdlib.Arith.Arith.
Import List.ListNotations.
Require Import Utf8 Core Misc Utils IterAdd.

(* ideal: non empty set type with some properties *)

Record ideal {T} {ro : ring_like_op T} := mk_ip
  { i_subset : T → Prop;
    i_zero : i_subset 0%L;
    i_add x y : i_subset x → i_subset y → i_subset (x + y)%L;
    i_mul_l t x : i_subset x → i_subset (t * x)%L;
    i_mul_r x t : i_subset x → i_subset (x * t)%L }.

Declare Scope ideal_scope.
Delimit Scope ideal_scope with I.
Bind Scope ideal_scope with ideal.

Arguments ideal T {ro}.
Arguments i_subset {T ro} i%_I a%_L.

Notation "x '∈' I" := (i_subset I x) (at level 70) : ideal_scope.

Class ideal_ctx T {ro : ring_like_op T} :=
  { ix_os : rngl_has_opp_or_psub T = true }.

Ltac destruct_ix :=
  set (Hos := ix_os).

(* to be moved somewhere else *)

Theorem forall_pair {A B} {P : A → B → Prop} :
  (∀ a b, P a b) ↔ (∀ ab, P (fst ab) (snd ab)).
Proof.
split; intros * H *; [ apply H | ].
apply (H (a, b)).
Qed.

Theorem forall_pair_in {A B P l} :
  (∀ ab : A * B, (fst ab, snd ab) ∈ l → P ab) ↔
  (∀ ab : A * B, ab ∈ l → P ab).
Proof.
intros.
now split; intros H * Hab; apply H; destruct ab.
Qed.

Theorem forall_in_seq {A B} da db la lb (P : A → B → Prop) :
  length la = length lb →
  (∀ i,
   i ∈ List.seq 0 (length la) → P (List.nth i la da) (List.nth i lb db)) ↔
  (∃ lab, la = List.map fst lab ∧ lb = List.map snd lab ∧
   ∀ ab, ab ∈ lab → P (fst ab) (snd ab)).
Proof.
intros * Hlab.
split; intros Hp. {
  exists (List.combine la lb).
  split. {
    clear P Hp.
    revert lb Hlab.
    induction la as [| a]; intros; [ easy | ].
    destruct lb; [ easy | ].
    cbn in Hlab |-*.
    apply Nat.succ_inj in Hlab.
    f_equal.
    now apply IHla.
  }
  split. {
    clear P Hp.
    revert la Hlab.
    induction lb as [| b]; intros. {
      apply List.length_zero_iff_nil in Hlab.
      now subst la.
    }
    destruct la; [ easy | ].
    cbn in Hlab |-*.
    apply Nat.succ_inj in Hlab.
    f_equal.
    now apply IHlb.
  }
  intros (a, b) Hab.
  apply (List.In_nth _ _ (da, db)) in Hab.
  destruct Hab as (i & Hi & Hab).
  rewrite List.length_combine in Hi.
  rewrite List.combine_nth in Hab; [ | easy ].
  injection Hab; clear Hab; intros; subst a b; cbn.
  apply Hp.
  apply List.in_seq.
  apply Nat.min_glb_lt_iff in Hi.
  easy.
} {
  intros i Hi.
  destruct Hp as (lab & Hla & Hlb & Hp).
  subst la lb.
  clear Hlab.
  apply List.in_seq in Hi.
  rewrite List.length_map in Hi.
  rewrite (List_map_nth' (da, db) da); [ | easy ].
  rewrite (List_map_nth' (da, db) db); [ | easy ].
  apply Hp.
  now apply List.nth_In.
}
Qed.

(* end to be added *)

(* for propositional and functional extensionalities *)
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.FunctionalExtensionality.
(* provides the axioms:
- propositional_extensionality :
     ∀ P Q : Prop, P ↔ Q → P = Q.
- functional_extensionality_dep :
     ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
     (∀ x : A, f x = g x)
     → f = g
*)

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ix : ideal_ctx T}.

(* 0 and 1 *)

Theorem I_zero_add a b : a = 0%L → b = 0%L → (a + b = 0)%L.
Proof. intros; subst; apply rngl_add_0_l. Qed.

Theorem I_zero_mul_l a b : b = 0%L → (a * b = 0)%L.
Proof.
destruct_ix.
intros; subst; apply (rngl_mul_0_r Hos).
Qed.

Theorem I_zero_mul_r a b : a = 0%L → (a * b = 0)%L.
Proof.
destruct_ix.
intros; subst; apply (rngl_mul_0_l Hos).
Qed.

(* addition *)

Definition I_add_subset I J z :=
  ∃ x y, (x ∈ I)%I ∧ (y ∈ J)%I ∧ z = (x + y)%L.

Arguments I_add_subset (I J)%_I z%_L.

Theorem I_add_zero I J : I_add_subset I J 0%L.
Proof.
exists 0%L, 0%L.
split; [ apply i_zero | ].
split; [ apply i_zero | ].
symmetry; apply rngl_add_0_l.
Qed.

Theorem I_add_add I J :
  ∀ x y, I_add_subset I J x → I_add_subset I J y → I_add_subset I J (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (x1 & x2 & Hx & Hx1 & Hx2).
destruct Hy as (y1 & y2 & Hy & Hy1 & Hy2).
subst x y.
exists (x1 + y1)%L, (x2 + y2)%L.
split; [ now apply i_add | ].
split; [ now apply i_add | ].
do 2 rewrite rngl_add_assoc.
progress f_equal.
apply rngl_add_add_swap.
Qed.

Theorem I_add_mul_l I J :
  ∀ x y, I_add_subset I J y → I_add_subset I J (x * y).
Proof.
intros * H.
destruct H as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (x * x1)%L, (x * x2)%L.
split; [ now apply i_mul_l | ].
split; [ now apply i_mul_l | ].
apply rngl_mul_add_distr_l.
Qed.

Theorem I_add_mul_r I J :
  ∀ x y, I_add_subset I J x → I_add_subset I J (x * y).
Proof.
intros * H.
destruct H as (x1 & x2 & Hx & Hx1 & Hx2); subst.
exists (x1 * y)%L, (x2 * y)%L.
split; [ now apply i_mul_r | ].
split; [ now apply i_mul_r | ].
apply rngl_mul_add_distr_r.
Qed.

(* multiplication *)

Definition I_mul_subset_prop I J z lxy :=
  length lxy ≠ 0 ∧
  (∀ x y, (x, y) ∈ lxy → (x ∈ I)%I ∧ (y ∈ J)%I) ∧
  z = ∑ ((x, y) ∈ lxy), x * y.

Definition I_mul_subset I J z := ∃ lxy, I_mul_subset_prop I J z lxy.

Arguments I_mul_subset (I J)%_I z%_L.

Theorem I_mul_zero I J : I_mul_subset I J 0%L.
Proof.
destruct_ix.
exists [(0, 0)%L].
split; [ easy | ].
split. {
  cbn; intros x y Hxy; destruct Hxy as [Hxy| ]; [ | easy ].
  injection Hxy; clear Hxy; intros; subst x y.
  split; apply i_zero.
}
symmetry.
progress unfold iter_list; cbn.
rewrite (rngl_mul_0_l Hos).
apply rngl_add_0_l.
Qed.

Theorem I_mul_add I J :
  ∀ x y, I_mul_subset I J x → I_mul_subset I J y → I_mul_subset I J (x + y)%L.
Proof.
intros * Hx Hy.
destruct Hx as (lab1 & Hlab1 & Hab1 & Hx).
destruct Hy as (lab2 & Hlab2 & Hab2 & Hy).
subst x y.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (lab1 ++ lab2).
rewrite List.length_app.
split; [ flia Hlab1 Hlab2 | ].
split. {
  intros x y Hxy.
  apply List.in_app_or in Hxy.
  now destruct Hxy; [ apply Hab1 | apply Hab2 ].
}
do 3 rewrite rngl_summation_list_pair.
symmetry; apply rngl_summation_list_app.
Qed.

Theorem I_mul_mul_l I J :
  ∀ x y, I_mul_subset I J y → I_mul_subset I J (x * y).
Proof.
destruct_ix.
intros * (lxy & Hlxy & Hab & Hz).
subst y; rename x into t.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (List.map (λ '(x, y), (t * x, y)%L) lxy).
rewrite List.length_map.
split; [ easy | ].
split. {
  intros x' y' Hxy'.
  apply List.in_map_iff in Hxy'.
  destruct Hxy' as ((x, y) & H & Hxy').
  injection H; clear H; intros; subst x' y'.
  specialize (Hab _ _ Hxy').
  now split; [ apply i_mul_l | ].
}
do 2 rewrite rngl_summation_list_pair.
rewrite (rngl_mul_summation_list_distr_l Hos).
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros (x, y) Hxy; cbn.
apply rngl_mul_assoc.
Qed.

Theorem I_mul_mul_r I J :
  ∀ x y, I_mul_subset I J x → I_mul_subset I J (x * y).
Proof.
destruct_ix.
intros * (lxy & Hlxy & Hab & Hz).
subst x; rename y into t.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
exists (List.map (λ '(x, y), (x, y * t)%L) lxy).
rewrite List.length_map.
split; [ easy | ].
split. {
  intros x y Hxy.
  apply List.in_map_iff in Hxy.
  destruct Hxy as ((x', y') & H & Hxy).
  injection H; clear H; intros; subst x y.
  specialize (Hab _ _ Hxy).
  now split; [ | apply i_mul_r ].
}
do 2 rewrite rngl_summation_list_pair.
rewrite (rngl_mul_summation_list_distr_r Hos).
rewrite rngl_summation_list_map.
apply rngl_summation_list_eq_compat.
intros (x, y) Hxy; cbn.
symmetry; apply rngl_mul_assoc.
Qed.

(* *)

Definition I_zero : ideal T :=
  {| i_subset a := a = 0%L;
     i_zero := eq_refl;
     i_add := I_zero_add;
     i_mul_l := I_zero_mul_l;
     i_mul_r := I_zero_mul_r |}.

Definition I_one : ideal T :=
  {| i_subset a := True;
     i_zero := I;
     i_add _ _ _ _ := I;
     i_mul_l _ _ _ := I;
     i_mul_r _ _ _ := I |}.

Definition I_add (I J : ideal T) : ideal T :=
  {| i_subset := I_add_subset I J;
     i_zero := I_add_zero I J;
     i_add := I_add_add I J;
     i_mul_l := I_add_mul_l I J;
     i_mul_r := I_add_mul_r I J |}.

Definition I_mul (I J : ideal T) : ideal T :=
  {| i_subset := I_mul_subset I J;
     i_zero := I_mul_zero I J;
     i_add := I_mul_add I J;
     i_mul_l := I_mul_mul_l I J;
     i_mul_r := I_mul_mul_r I J |}.

(* ideal ring like op *)

Definition I_ring_like_op : ring_like_op (ideal T) :=
  {| rngl_zero := I_zero;
     rngl_one := I_one;
     rngl_add := I_add;
     rngl_mul := I_mul;
     rngl_opt_opp_or_psub := None;
     rngl_opt_inv_or_pdiv := None;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := None;
     rngl_opt_leb := None |}.

End a.

Notation "0" := I_zero : ideal_scope.
Notation "1" := I_one : ideal_scope.
Notation "I + J" := (I_add I J) : ideal_scope.
Notation "I * J" := (I_mul I J) : ideal_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ix : ideal_ctx T}.

Theorem eq_ideal_eq : ∀ I J,
  i_subset I = i_subset J
  ↔ I = J.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct I.
destruct J.
cbn in *.
subst.
f_equal.
apply proof_irrelevance.
apply proof_irrelevance.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Theorem I_add_subset_comm I J z : I_add_subset I J z = I_add_subset J I z.
Proof.
progress unfold I_add_subset.
apply propositional_extensionality.
split; intros (x & y & H1 & H2 & H3). {
  exists y, x.
  now rewrite rngl_add_comm.
} {
  exists y, x.
  now rewrite rngl_add_comm.
}
Qed.

Theorem I_add_comm : ∀ I J, (I + J)%I = (J + I)%I.
Proof.
intros.
apply eq_ideal_eq.
apply functional_extensionality_dep.
intros z.
apply I_add_subset_comm.
Qed.

Theorem I_add_subset_assoc_l I J K x z :
  (x ∈ I)%I → (z ∈ J + K)%I → I_add_subset (I + J) K (x + z)%L.
Proof.
intros H1 H2.
cbn in H2.
progress unfold I_add_subset; cbn.
progress unfold I_add_subset in H2.
progress unfold I_add_subset.
destruct H2 as (y & t & H & H2 & H3); subst z.
rename t into z.
move y before x; move z before y.
exists (x + y)%L, z.
split; [ now exists x, y | ].
split; [ easy | ].
apply rngl_add_assoc.
Qed.

Theorem I_add_subset_assoc I J K x :
  I_add_subset I (J + K) x = I_add_subset (I + J) K x.
Proof.
destruct_ix.
apply propositional_extensionality.
split; intros (y & z & H & H1 & H2); subst x. {
  now apply I_add_subset_assoc_l.
} {
  rewrite I_add_subset_comm.
  rewrite I_add_comm.
  rewrite rngl_add_comm.
  apply I_add_subset_assoc_l; [ easy | ].
  now rewrite I_add_comm.
}
Qed.

Theorem I_add_assoc : ∀ I J K, (I + (J + K))%I = ((I + J) + K)%I.
Proof.
intros.
apply eq_ideal_eq.
apply functional_extensionality_dep.
intros x; cbn.
apply I_add_subset_assoc.
Qed.

Theorem I_add_subset_0_l I x : I_add_subset 0 I x = (x ∈ I)%I.
Proof.
destruct_ix.
progress unfold I_add_subset; cbn.
apply propositional_extensionality.
split. {
  intros (y & z & H & H1 & H2); subst x y.
  now rewrite rngl_add_0_l.
} {
  intros H1.
  exists 0%L, x.
  now rewrite rngl_add_0_l.
}
Qed.

Theorem I_add_0_l I : (0 + I)%I = I.
Proof.
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_add_subset_0_l.
Qed.

Theorem forall_exists_exists_forall {A B} (da : A) (db : B) P Q la :
  (∀ a, a ∈ la → P a ∧ ∃ n, Q a n)
  ↔ ∃ lb, length lb = length la ∧
    ∀ i,
    i ∈ List.seq 0 (length lb)
    → P (List.nth i la da) ∧ Q (List.nth i la da) (List.nth i lb db).
Proof.
intros.
split. {
  intros Ha.
  induction la as [| a]; [ now exists [] | ].
  assert (H : ∀ a, a ∈ la → P a ∧ ∃ n, Q a n). {
    intros b Hb.
    apply Ha.
    now right.
  }
  specialize (IHla H); clear H.
  destruct IHla as (nl & H1 & H2).
  destruct (Ha a (List.in_eq _ _)) as (HP & na & Hna).
  exists (na :: nl).
  split; [ now cbn; f_equal | ].
  intros i Hi.
  destruct i; [ easy | cbn ].
  apply H2.
  apply List.in_seq in Hi.
  apply List.in_seq.
  destruct Hi as (_, Hi); cbn in Hi.
  split; [ easy | ].
  now apply Nat.succ_lt_mono in Hi.
} {
  intros (lb & H1 & H2) * Ha.
  apply (List.In_nth _ _ da) in Ha.
  destruct Ha as (n & Hna & Ha).
  subst a.
  specialize (H2 n).
  assert (H : n ∈ List.seq 0 (length lb)). {
    rewrite H1.
    now apply List.in_seq.
  }
  specialize (H2 H); clear H.
  split; [ easy | ].
  now exists (List.nth n lb db).
}
Qed.

Theorem I_subset_mul_assoc_l :
  ∀ I J K x y z, (x ∈ I → y ∈ J → z ∈ K → x * y * z ∈ I * J * K)%I.
Proof.
intros * Ha Hb Hc.
exists [(x * y, z)]%L.
split; [ easy | ].
split. {
  intros x' y' Hxy.
  destruct Hxy as [Hxy| Hxy]; [ | easy ].
  injection Hxy; clear Hxy; intros; subst x' y'.
  split; [ | now apply Hc; left ].
  exists [(x, y)].
  split; [ easy | ].
  split. {
    intros x' y' Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    now injection Hxy; clear Hxy; intros; subst x y.
  }
  progress unfold iter_list; cbn; symmetry.
  apply rngl_add_0_l.
}
progress unfold iter_list; cbn; symmetry.
apply rngl_add_0_l.
Qed.

Theorem I_subset_mul_assoc_r :
  ∀ I J K x y z, (x ∈ I → y ∈ J → z ∈ K → x * y * z ∈ I * (J * K))%I.
Proof.
intros * Ha Hb Hc.
exists [(x, y * z)]%L.
split; [ easy | ].
split. {
  intros x' y' Hxy.
  destruct Hxy as [Hxy| Hxy]; [ | easy ].
  injection Hxy; clear Hxy; intros; subst x' y'.
  split; [ easy | ].
  exists [(y, z)].
  split; [ easy | ].
  split. {
    intros x' y' Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    now injection Hxy; clear Hxy; intros; subst x' y'.
  }
  progress unfold iter_list; cbn; symmetry.
  apply rngl_add_0_l.
}
progress unfold iter_list; cbn; symmetry.
rewrite rngl_add_0_l.
apply rngl_mul_assoc.
Qed.

Theorem I_subset_sum_mul_assoc_l {A} :
  ∀ I J K li (f g h : A → T),
  (∀ i, i ∈ li → (f i ∈ I)%I)
  → (∀ i, i ∈ li → (g i ∈ J)%I)
  → (∀ i, i ∈ li → (h i ∈ K)%I)
  → (∑ (i ∈ li), f i * g i * h i ∈ I * J * K)%I.
Proof.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  apply i_zero.
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i, i ∈ li → (f i ∈ I)%I). {
  now intros i Hi; apply Ha; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (g i ∈ J)%I). {
  now intros i Hi; apply Hb; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (h i ∈ K)%I). {
  now intros i Hi; apply Hc; right.
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
clear - Ha Hb Hc.
apply I_subset_mul_assoc_l.
now apply Ha; left.
now apply Hb; left.
now apply Hc; left.
Qed.

Theorem I_subset_sum_mul_assoc_r {A} :
  ∀ I J K li (f g h : A → T),
  (∀ i, i ∈ li → (f i ∈ I)%I)
  → (∀ i, i ∈ li → (g i ∈ J)%I)
  → (∀ i, i ∈ li → (h i ∈ K)%I)
  → (∑ (i ∈ li), f i * g i * h i ∈ I * (J * K))%I.
Proof.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  apply i_zero.
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i, i ∈ li → (f i ∈ I)%I). {
  now intros i Hi; apply Ha; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (g i ∈ J)%I). {
  now intros i Hi; apply Hb; right.
}
specialize (IHli H); clear H.
assert (H : ∀ i, i ∈ li → (h i ∈ K)%I). {
  now intros i Hi; apply Hc; right.
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
clear - Ha Hb Hc.
apply I_subset_mul_assoc_r.
now apply Ha; left.
now apply Hb; left.
now apply Hc; left.
Qed.

Theorem I_subset_sum_sum_mul_assoc_l {A B} :
  ∀ I J K li lj (f g h : A → B → T),
  (∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ I)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ J)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ K)%I)
  → (∑ (i ∈ li), ∑ (j ∈ lj i), f i j * g i j * h i j ∈ I * J * K)%I.
Proof.
destruct_ix.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  exists [(0, 0)]%L.
  split; [ easy | ].
  split. {
    intros x y Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    injection Hxy; clear Hxy; intros; subst x y.
    split; apply i_zero.
  }
  rewrite rngl_summation_list_pair; symmetry.
  rewrite rngl_summation_list_only_one.
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ I)%I). {
  now intros * Hi Hj; apply Ha; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ J)%I). {
  now intros * Hi Hj; apply Hb; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ K)%I). {
  now intros * Hi Hj; apply Hc; [ right | ].
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
apply I_subset_sum_mul_assoc_l.
now intros i Hi; apply Ha; [ left | ].
now intros i Hi; apply Hb; [ left | ].
now intros i Hi; apply Hc; [ left | ].
Qed.

Theorem I_subset_sum_sum_mul_assoc_r {A B} :
  ∀ I J K li lj (f g h : A → B → T),
  (∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ I)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ J)%I)
  → (∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ K)%I)
  → (∑ (i ∈ li), ∑ (j ∈ lj i), f i j * g i j * h i j ∈ I * (J * K))%I.
Proof.
destruct_ix.
intros * Ha Hb Hc.
induction li as [| i1]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  exists [(0, 0)]%L.
  split; [ easy | ].
  split. {
    intros x y Hxy.
    destruct Hxy as [Hxy| Hxy]; [ | easy ].
    injection Hxy; clear Hxy; intros; subst x y.
    split; apply i_zero.
  }
  rewrite rngl_summation_list_pair; symmetry.
  rewrite rngl_summation_list_only_one.
  apply (rngl_mul_0_l Hos).
}
rewrite rngl_summation_list_cons.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (f i j ∈ I)%I). {
  now intros * Hi Hj; apply Ha; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (g i j ∈ J)%I). {
  now intros * Hi Hj; apply Hb; [ right | ].
}
specialize (IHli H); clear H.
assert (H : ∀ i j, i ∈ li → j ∈ lj i → (h i j ∈ K)%I). {
  now intros * Hi Hj; apply Hc; [ right | ].
}
specialize (IHli H); clear H.
apply i_add; [ | apply IHli ].
apply I_subset_sum_mul_assoc_r.
now intros i Hi; apply Ha; [ left | ].
now intros i Hi; apply Hb; [ left | ].
now intros i Hi; apply Hc; [ left | ].
Qed.

(* I_mul_subset I (J * K) z → I_mul_subset (I * J) K z *)
Theorem I_subset_mul_assoc_l_mul_assoc_r I J K :
  ∀ z, (z ∈ I * (J * K) → z ∈ (I * J) * K)%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_mul_subset in Ht.
destruct Ht as (lx_yz & Hlx_yz & Ha_bc & Ht).
remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
rewrite rngl_summation_list_pair in Ht.
remember (∑ (x_yz ∈ _), _) as x in Ht; subst x. (* renaming *)
specialize ((proj1 forall_pair) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
specialize ((proj1 forall_pair_in) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
apply (forall_exists_exists_forall (0, 0)%L []) in Ha_bc.
destruct Ha_bc as (llyz & Hllyz & Hxyz).
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move Hn before n; symmetry in Hlx_yz.
move Hlx_yz before Hllyz.
move llyz before lx_yz.
rewrite Hllyz in Hxyz.
set (P u v := (fst u ∈ I)%I ∧ I_mul_subset_prop J K (snd u) v).
specialize (forall_in_seq (0, 0)%L [] lx_yz llyz P) as H1.
rewrite Hlx_yz, Hllyz in H1.
specialize (H1 eq_refl).
subst P; cbn in H1.
specialize (proj1 H1) as H2; clear H1.
specialize (H2 Hxyz).
clear Hxyz; rename H2 into Hxyz.
destruct Hxyz as (lxyz & Hllyzm & Hlx_yzm & Hxyz).
subst lx_yz llyz.
move Hllyz before Hlx_yz.
rewrite List.length_map in Hlx_yz, Hllyz.
clear Hlx_yz; rename Hllyz into Hlxyz.
rewrite rngl_summation_list_map in Ht.
remember (∀ xyz, _) as x in Hxyz; subst x. (* renaming *)
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
assert (∀ xyz, xyz ∈ lxyz → snd (fst xyz) = ∑ ((y, z) ∈ snd xyz), y * z). {
  intros * H.
  now specialize (Hxyz _ H) as (Ha & Hllxyz & Hbc & H1).
}
erewrite rngl_summation_list_eq_compat in Ht; [ | now intros; rewrite H ].
clear H.
cbn in Ht.
erewrite rngl_summation_list_eq_compat in Ht. 2: {
  intros i Hi.
  rewrite rngl_summation_list_pair.
  rewrite (rngl_mul_summation_list_distr_l Hos).
  erewrite rngl_summation_list_eq_compat. 2: {
    intros j Hj.
    rewrite rngl_mul_assoc.
    reflexivity.
  }
  remember (∑ (yz ∈ _), _) as x in |-*; subst x. (* renaming *)
  reflexivity.
}
clear - Ht Hxyz.
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
subst t.
apply I_subset_sum_sum_mul_assoc_l. {
  intros * Hi Hj.
  now specialize (Hxyz _ Hi).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
}
Qed.

(* I_mul_subset (I * J) K z → I_mul_subset I (J * K) z *)
Theorem I_subset_mul_assoc_l_mul_assoc_l I J K :
  ∀ z, (z ∈ (I * J) * K → z ∈ I * (J * K))%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_mul_subset in Ht.
destruct Ht as (lx_yz & Hlx_yz & Ha_bc & Ht).
remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
rewrite rngl_summation_list_pair in Ht.
remember (∑ (x_yz ∈ _), _) as x in Ht; subst x. (* renaming *)
specialize ((proj1 forall_pair) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
specialize ((proj1 forall_pair_in) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
assert (H : ∀ ab, ab ∈ lx_yz → (snd ab ∈ K)%I ∧ I_mul_subset I J (fst ab)). {
  intros ab Hab.
  now specialize (Ha_bc ab Hab).
}
apply (forall_exists_exists_forall (0, 0)%L []) in H.
clear Ha_bc; rename H into Ha_bc.
destruct Ha_bc as (llyz & Hllyz & Hxyz).
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move Hn before n; symmetry in Hlx_yz.
move Hlx_yz before Hllyz.
move llyz before lx_yz.
rewrite Hllyz in Hxyz.
set (P u v := (snd u ∈ K)%I ∧ I_mul_subset_prop I J (fst u) v).
specialize (forall_in_seq (0, 0)%L [] lx_yz llyz P) as H1.
rewrite Hlx_yz, Hllyz in H1.
specialize (H1 eq_refl).
subst P; cbn in H1.
specialize (proj1 H1) as H2; clear H1.
specialize (H2 Hxyz).
clear Hxyz; rename H2 into Hxyz.
destruct Hxyz as (lxyz & Hllyzm & Hlx_yzm & Hxyz).
subst lx_yz llyz.
move Hllyz before Hlx_yz.
rewrite List.length_map in Hlx_yz, Hllyz.
clear Hlx_yz; rename Hllyz into Hlxyz.
rewrite rngl_summation_list_map in Ht.
remember (∀ xyz, _) as x in Hxyz; subst x. (* renaming *)
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
assert (∀ xyz, xyz ∈ lxyz → fst (fst xyz) = ∑ ((y, z) ∈ snd xyz), y * z). {
  intros * H.
  now specialize (Hxyz _ H) as (Ha & Hllxyz & Hbc & H1).
}
erewrite rngl_summation_list_eq_compat in Ht; [ | now intros; rewrite H ].
clear H.
cbn in Ht.
erewrite rngl_summation_list_eq_compat in Ht. 2: {
  intros i Hi.
  rewrite rngl_summation_list_pair.
  rewrite (rngl_mul_summation_list_distr_r Hos).
  remember (∑ (yz ∈ _), _) as x in |-*; subst x. (* renaming *)
  reflexivity.
}
clear - Ht Hxyz.
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
subst t.
apply I_subset_sum_sum_mul_assoc_r. {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  specialize (Hxyz _ Hi).
  destruct Hxyz as (_, H).
  destruct H as (lli & H1 & H2).
  destruct j as (j, k).
  now specialize (H1 j k Hj).
} {
  intros * Hi Hj.
  now specialize (Hxyz _ Hi).
}
Qed.

Theorem I_mul_subset_assoc I J K x :
  I_mul_subset I (J * K) x = I_mul_subset (I * J) K x.
Proof.
apply propositional_extensionality.
split.
apply I_subset_mul_assoc_l_mul_assoc_r.
apply I_subset_mul_assoc_l_mul_assoc_l.
Qed.

Theorem I_mul_assoc I J K : (I * (J * K))%I = ((I * J) * K)%I.
Proof.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_mul_subset_assoc.
Qed.

Theorem I_mul_subset_1_l I : ∀ x, I_mul_subset 1 I x = (x ∈ I)%I.
Proof.
destruct_ix.
intros.
apply propositional_extensionality.
split. {
  intros (lxy & Hlxy & H1 & H); subst x.
  rewrite rngl_summation_list_pair.
  induction lxy as [| (x, y)]; [ easy | ].
  clear Hlxy.
  destruct (Nat.eq_dec (length lxy) 0) as [Hnz| Hnz]. {
    apply List.length_zero_iff_nil in Hnz.
    subst lxy.
    rewrite rngl_summation_list_only_one.
    apply i_mul_l; cbn.
    now apply (H1 x y); left.
  }
  specialize (IHlxy Hnz).
  rewrite rngl_summation_list_cons; cbn.
  apply i_add. {
    apply i_mul_l.
    now apply (H1 x y); left.
  }
  apply IHlxy.
  intros x' y' Hxy'.
  now apply H1; right.
} {
  intros Hax.
  exists [(1%L, x)].
  split; [ easy | ].
  split. {
    intros y z Hyz.
    destruct Hyz as [Hy| Hy]; [ | easy ].
    now injection Hy; clear Hy; intros; subst y z.
  }
  rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_only_one.
  cbn; symmetry.
  apply rngl_mul_1_l.
}
Qed.

Theorem I_mul_1_l : ∀ I : ideal T, (1 * I)%I = I.
Proof.
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
intros.
apply I_mul_subset_1_l.
Qed.

(* I_mul_subset I (J + K) t → I_mul_subset (I * J) (I * K) t *)
Theorem I_mul_subset_add_distr_l_1 I J K :
  ∀ t, (t ∈ I * (J + K) → t ∈ I * J + I * K)%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_mul_subset in Ht.
destruct Ht as (lx_yz & Hlx_yz & Ha_bc & Ht).
remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
rewrite rngl_summation_list_pair in Ht.
remember (∑ (x_yz ∈ _), _) as x in Ht; subst x. (* renaming *)
specialize ((proj1 forall_pair) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
specialize ((proj1 forall_pair_in) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
apply (forall_exists_exists_forall (0, 0) 0)%L in Ha_bc.
destruct Ha_bc as (la & Hla & Hxyz).
set
  (P u v :=
     (fst v ∈ I)%I ∧ ∃ y : T, (u ∈ J)%I ∧ (y ∈ K)%I ∧ snd v = (u + y)%L).
specialize (forall_in_seq 0%L (0, 0)%L la lx_yz P Hla) as H1.
specialize (proj1 H1 Hxyz) as H2.
subst P; clear H1 Hxyz; rename H2 into Hxyz.
destruct Hxyz as (lxyz & Hlaxyz & Hlxxyz & Hxyz).
specialize (@forall_exists_exists_forall (T * (T * T)) T) as H1.
specialize (H1 (0, (0, 0))%L 0%L).
specialize (H1 (λ ab, (fst (snd ab) ∈ I)%I)).
cbn in H1.
specialize
  (H1 (λ ab y, (fst ab ∈ J)%I ∧ (y ∈ K)%I ∧ snd (snd ab) = (fst ab + y)%L)).
cbn in H1.
specialize (proj1 (H1 lxyz) Hxyz) as (lb & Hlb & H).
clear Hxyz H1; rename H into Hxyz.
move lb before la.
move Hlb before Hla.
move lxyz before lx_yz.
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move la before lxyz; move lb before la.
symmetry in Hlx_yz.
move Hla before Hlx_yz; move Hlb before Hla.
assert (Hlxyz : length lxyz = n). {
  rewrite <- Hlx_yz.
  rewrite Hlxxyz; symmetry.
  apply List.length_map.
}
move Hn before n.
move Hlxyz after Hla.
rewrite Hlxyz in Hlb.
set
  (P u v :=
     (fst (snd v) ∈ I)%I ∧ (fst v ∈ J)%I ∧ (u ∈ K)%I ∧
     snd (snd v) = (fst v + u)%L).
specialize (forall_in_seq 0%L (0, (0, 0))%L) as H1.
specialize (H1 lb lxyz P).
rewrite Hlxyz in H1.
specialize (H1 Hlb).
subst P.
cbn in H1.
specialize ((proj1 H1) Hxyz) as (lxyz' & Hlbxyz & Hlxxyz' & H).
clear Hxyz H1; rename H into Hxyz.
move lxyz' before lxyz.
subst lxyz.
rename lxyz' into lxyz.
rewrite List.map_map in Hlxxyz.
rewrite List.map_map in Hlaxyz.
subst lx_yz.
rewrite List.length_map in Hlx_yz, Hlxyz.
clear Hlx_yz.
rewrite rngl_summation_list_map in Ht.
remember (∀ xyz, _) as x in Hxyz; subst x. (* renaming *)
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
clear la Hla Hlaxyz.
clear lb Hlb Hlbxyz.
subst t.
clear n Hn Hlxyz.
induction lxyz as [| xyzt]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  apply i_zero.
}
rewrite rngl_summation_list_cons.
cbn - [ i_subset ].
apply i_add. 2: {
  apply IHlxyz.
  intros * Hxyz'.
  now apply Hxyz; right.
}
specialize (Hxyz xyzt).
assert (H : xyzt ∈ xyzt :: lxyz) by now left.
specialize (Hxyz H); clear H.
destruct Hxyz as (Ha & Hb & Hc & Ht).
rewrite Ht.
rewrite rngl_mul_add_distr_l.
apply i_add. {
  cbn.
  progress unfold I_add_subset.
  exists (fst (snd (snd xyzt)) * fst (snd xyzt))%L, 0%L.
  rewrite rngl_add_0_r.
  split. {
    exists [(fst (snd (snd xyzt)), fst (snd xyzt))].
    split; [ easy | ].
    split. {
      intros x y Hxy.
      destruct Hxy as [Hxy| ]; [ | easy ].
      now injection Hxy; clear Hxy; intros; subst x y.
    }
    rewrite rngl_summation_list_pair.
    now rewrite rngl_summation_list_only_one.
  }
  split; [ apply i_zero | easy ].
} {
  cbn.
  progress unfold I_add_subset.
  exists 0%L, (fst (snd (snd xyzt)) * fst xyzt)%L.
  rewrite rngl_add_0_l.
  split; [ apply i_zero | ].
  split; [ | easy ].
  exists [(fst (snd (snd xyzt)), fst xyzt)].
  split; [ easy | ].
  split. {
    intros x y Hxy.
    destruct Hxy as [Hxy| ]; [ | easy ].
    now injection Hxy; clear Hxy; intros; subst x y.
  }
  rewrite rngl_summation_list_pair.
  now rewrite rngl_summation_list_only_one.
}
Qed.

(* I_mul_subset (I + J) K x → I_add_subset (I * K) (J * K) x *)
Theorem I_mul_subset_add_distr_r_1 I J K :
  ∀ t, (t ∈ (I + J) * K → t ∈ I * K + J * K)%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_mul_subset in Ht.
destruct Ht as (lx_yz & Hlx_yz & Ha_bc & Ht).
remember (∀ x yz, _) as x in Ha_bc; subst x. (* renaming *)
rewrite rngl_summation_list_pair in Ht.
remember (∑ (x_yz ∈ _), _) as x in Ht; subst x. (* renaming *)
specialize ((proj1 forall_pair) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
specialize ((proj1 forall_pair_in) Ha_bc) as H1.
cbn in H1.
clear Ha_bc; rename H1 into Ha_bc.
assert (H : ∀ ab, ab ∈ lx_yz → (snd ab ∈ K)%I ∧ I_add_subset I J (fst ab)). {
  intros ab Hab.
  now specialize (Ha_bc ab Hab).
}
clear Ha_bc; rename H into Ha_bc.
apply (forall_exists_exists_forall (0, 0) 0)%L in Ha_bc.
destruct Ha_bc as (la & Hla & Hxyz).
set
  (P u v :=
     (snd v ∈ K)%I ∧ ∃ y : T, (u ∈ I)%I ∧ (y ∈ J)%I ∧ fst v = (u + y)%L).
specialize (forall_in_seq 0%L (0, 0)%L la lx_yz P Hla) as H1.
progress unfold P in H1.
cbn in H1.
specialize (proj1 H1 Hxyz) as H2.
subst P; clear H1 Hxyz; rename H2 into Hxyz.
destruct Hxyz as (lxyz & Hlaxyz & Hlxxyz & Hxyz).
specialize (@forall_exists_exists_forall (T * (T * T)) T) as H1.
specialize (H1 (0, (0, 0))%L 0%L).
specialize (H1 (λ ab, (snd (snd ab) ∈ K)%I)).
cbn in H1.
specialize
  (H1 (λ ab y, (fst ab ∈ I)%I ∧ (y ∈ J)%I ∧ fst (snd ab) = (fst ab + y)%L)).
cbn in H1.
specialize (proj1 (H1 lxyz) Hxyz) as (lb & Hlb & H).
clear Hxyz H1; rename H into Hxyz.
move lb before la.
move Hlb before Hla.
move lxyz before lx_yz.
remember (length lx_yz) as n eqn:Hn.
rename Hlx_yz into H; rename Hn into Hlx_yz; rename H into Hn.
move la before lxyz; move lb before la.
symmetry in Hlx_yz.
move Hla before Hlx_yz; move Hlb before Hla.
assert (Hlxyz : length lxyz = n). {
  rewrite <- Hlx_yz.
  rewrite Hlxxyz; symmetry.
  apply List.length_map.
}
move Hn before n.
move Hlxyz after Hla.
rewrite Hlxyz in Hlb.
set
  (P u v :=
     (snd (snd v) ∈ K)%I ∧ (fst v ∈ I)%I ∧ (u ∈ J)%I ∧
     fst (snd v) = (fst v + u)%L).
specialize (forall_in_seq 0%L (0, (0, 0))%L) as H1.
specialize (H1 lb lxyz P).
rewrite Hlxyz in H1.
specialize (H1 Hlb).
subst P.
cbn in H1.
specialize ((proj1 H1) Hxyz) as (lxyz' & Hlbxyz & Hlxxyz' & H).
clear Hxyz H1; rename H into Hxyz.
move lxyz' before lxyz.
subst lxyz.
rename lxyz' into lxyz.
rewrite List.map_map in Hlxxyz.
rewrite List.map_map in Hlaxyz.
subst lx_yz.
rewrite List.length_map in Hlx_yz, Hlxyz.
clear Hlx_yz.
rewrite rngl_summation_list_map in Ht.
remember (∀ xyz, _) as x in Hxyz; subst x. (* renaming *)
remember (∑ (xyz ∈ _), _) as x in Ht; subst x. (* renaming *)
clear la Hla Hlaxyz.
clear lb Hlb Hlbxyz.
subst t.
clear n Hn Hlxyz.
induction lxyz as [| xyzt]. {
  rewrite rngl_summation_list_empty; [ | easy ].
  apply i_zero.
}
rewrite rngl_summation_list_cons.
cbn - [ i_subset ].
apply i_add. 2: {
  apply IHlxyz.
  intros * Hxyz'.
  now apply Hxyz; right.
}
specialize (Hxyz xyzt).
assert (H : xyzt ∈ xyzt :: lxyz) by now left.
specialize (Hxyz H); clear H.
destruct Hxyz as (Ha & Hb & Hc & Ht).
rewrite Ht.
rewrite rngl_mul_add_distr_r.
apply i_add. {
  cbn.
  progress unfold I_add_subset.
  exists (fst (snd xyzt) * snd (snd (snd xyzt)))%L, 0%L.
  rewrite rngl_add_0_r.
  split. {
    exists [(fst (snd xyzt), snd (snd (snd xyzt)))].
    split; [ easy | ].
    split. {
      intros x y Hxy.
      destruct Hxy as [Hxy| ]; [ | easy ].
      now injection Hxy; clear Hxy; intros; subst x y.
    }
    rewrite rngl_summation_list_pair.
    now rewrite rngl_summation_list_only_one.
  }
  split; [ apply i_zero | easy ].
} {
  cbn.
  progress unfold I_add_subset.
  exists 0%L, (fst xyzt * snd (snd (snd xyzt)))%L.
  rewrite rngl_add_0_l.
  split; [ apply i_zero | ].
  split; [ | easy ].
  exists [(fst xyzt, snd (snd (snd xyzt)))].
  split; [ easy | ].
  split. {
    intros x y Hxy.
    destruct Hxy as [Hxy| ]; [ | easy ].
    now injection Hxy; clear Hxy; intros; subst x y.
  }
  rewrite rngl_summation_list_pair.
  now rewrite rngl_summation_list_only_one.
}
Qed.

Theorem I_mul_subset_add_distr_l_2_lemma I J K lab :
  length lab ≠ 0
  → (∀ x y, (x, y) ∈ lab → (x ∈ I)%I ∧ (y ∈ J)%I)
  → (∑ ((x, y) ∈ lab), x * y ∈ I * (J + K))%I.
Proof.
intros Hlab Hab; cbn.
induction lab as [| (x, y) lxy]; [ easy | clear Hlab ].
destruct lxy as [| (x', y')]. {
  exists [(x, y)].
  split; [ easy | ].
  split; [ | easy ].
  intros x' y' H.
  destruct H as [H| ]; [ | easy ].
  injection H; clear H; intros; subst x' y'.
  split; [ now apply (Hab x y); left | ].
  cbn.
  progress unfold I_add_subset.
  exists y, 0%L.
  rewrite rngl_add_0_r.
  split; [ now apply (Hab x y); left | ].
  split; [ apply i_zero | easy ].
}
specialize (IHlxy (Nat.neq_succ_0 _)).
rewrite rngl_summation_list_pair.
rewrite rngl_summation_list_cons; cbn.
rewrite <- rngl_summation_list_pair.
assert (H : ∀ x y, (x, y) ∈ (x', y') :: lxy → (x ∈ I ∧ y ∈ J)%I). {
  intros x'' y'' Hxy.
  now apply Hab; right.
}
specialize (IHlxy H); clear H.
destruct IHlxy as (lxy' & Hlxy' & H3 & H4).
exists ((x, y) :: lxy').
split; [ easy | ].
rewrite H4.
split. {
  intros x'' y'' Hxy.
  destruct Hxy as [Hxy| Hxy]; [ | now apply H3 ].
  injection Hxy; clear Hxy; intros; subst x'' y''.
  specialize (Hab x y) as H1.
  split; [ now apply H1; left | ].
  exists y, 0%L.
  rewrite rngl_add_0_r.
  split; [ now apply H1; left | ].
  split; [ apply i_zero | easy ].
}
do 2 rewrite rngl_summation_list_pair.
now rewrite rngl_summation_list_cons.
Qed.

Theorem I_mul_subset_add_distr_r_2_lemma I J K lab :
  length lab ≠ 0
  → (∀ x y : T, (x, y) ∈ lab → (x ∈ I)%I ∧ (y ∈ K)%I)
  → (∑ ((x, y) ∈ lab), x * y ∈ (I + J) * K)%I.
Proof.
intros Hlab Hab; cbn.
induction lab as [| (x, y) lxy]; [ easy | clear Hlab ].
destruct lxy as [| (x', y')]. {
  exists [(x, y)].
  split; [ easy | ].
  split; [ | easy ].
  intros x' y' H.
  destruct H as [H| ]; [ | easy ].
  injection H; clear H; intros; subst x' y'.
  split; [ | now apply (Hab x y); left ].
  cbn.
  progress unfold I_add_subset.
  exists x, 0%L.
  rewrite rngl_add_0_r.
  split; [ now apply (Hab x y); left | ].
  split; [ apply i_zero | easy ].
}
specialize (IHlxy (Nat.neq_succ_0 _)).
rewrite rngl_summation_list_pair.
rewrite rngl_summation_list_cons; cbn.
rewrite <- rngl_summation_list_pair.
assert (H : ∀ x y, (x, y) ∈ (x', y') :: lxy → (x ∈ I ∧ y ∈ K)%I). {
  intros x'' y'' Hxy.
  now apply Hab; right.
}
specialize (IHlxy H); clear H.
destruct IHlxy as (lxy' & Hlxy' & H3 & H4).
exists ((x, y) :: lxy').
split; [ easy | ].
rewrite H4.
split. {
  intros x'' y'' Hxy.
  destruct Hxy as [Hxy| Hxy]; [ | now apply H3 ].
  injection Hxy; clear Hxy; intros; subst x'' y''.
  specialize (Hab x y) as H1.
  split; [ | now apply H1; left ].
  exists x, 0%L.
  rewrite rngl_add_0_r.
  split; [ now apply H1; left | ].
  split; [ apply i_zero | easy ].
}
do 2 rewrite rngl_summation_list_pair.
now rewrite rngl_summation_list_cons.
Qed.

(* I_mul_subset (I * J) (I * K) t → I_mul_subset I (J + K) t *)
Theorem I_mul_subset_add_distr_l_2 I J K :
  ∀ t, (t ∈ I * J + I * K → t ∈ I * (J + K))%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_add_subset in Ht.
destruct Ht as (xy & xz & Hxy & Hxz & Ht).
cbn in Hxy, Hxz.
destruct Hxy as (lab & Hlab & Hab & Hxy).
destruct Hxz as (lac & Hlac & Hac & Hxz).
move lac before lab; move Hlac before Hlab.
move Hac before Hab.
remember (∀ x z, _) as x in Hac; subst x. (* renaming *)
remember (∑ ((x, z) ∈ _), _) as x in Hxz; subst x. (* renaming *)
subst xy xz t.
apply i_add. {
  now apply I_mul_subset_add_distr_l_2_lemma.
} {
  rewrite I_add_comm.
  now apply I_mul_subset_add_distr_l_2_lemma.
}
Qed.

(* I_add_subset (I * K) (J * K) x → I_mul_subset (I + J) K x *)
Theorem I_mul_subset_add_distr_r_2 I J K :
  ∀ t, (t ∈ I * K + J * K → t ∈ (I + J) * K)%I.
Proof.
destruct_ix.
intros t Ht.
cbn in Ht.
progress unfold I_add_subset in Ht.
destruct Ht as (xy & xz & Hxy & Hxz & Ht).
cbn in Hxy, Hxz.
destruct Hxy as (lab & Hlab & Hab & Hxy).
destruct Hxz as (lac & Hlac & Hac & Hxz).
move lac before lab; move Hlac before Hlab.
move Hac before Hab.
remember (∀ x z, _) as x in Hac; subst x. (* renaming *)
remember (∑ ((x, z) ∈ _), _) as x in Hxz; subst x. (* renaming *)
subst xy xz t.
apply i_add. {
  now apply I_mul_subset_add_distr_r_2_lemma.
} {
  rewrite I_add_comm.
  now apply I_mul_subset_add_distr_r_2_lemma.
}
Qed.

Theorem I_mul_subset_add_distr_l I J K x :
  I_mul_subset I (J + K) x = I_add_subset (I * J) (I * K) x.
Proof.
apply propositional_extensionality.
split.
apply I_mul_subset_add_distr_l_1.
apply I_mul_subset_add_distr_l_2.
Qed.

Theorem I_mul_subset_add_distr_r I J K x :
  I_mul_subset (I + J) K x = I_add_subset (I * K) (J * K) x.
Proof.
apply propositional_extensionality.
split.
apply I_mul_subset_add_distr_r_1.
apply I_mul_subset_add_distr_r_2.
Qed.

Theorem I_mul_add_distr_l I J K : (I * (J + K))%I = (I * J + I * K)%I.
Proof.
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_mul_subset_add_distr_l.
Qed.

Theorem I_mul_add_distr_r I J K : ((I + J) * K)%I = (I * K + J * K)%I.
Proof.
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
apply I_mul_subset_add_distr_r.
Qed.

Theorem I_mul_subset_comm :
  rngl_mul_is_comm T = true →
  ∀ I J x, I_mul_subset I J x = I_mul_subset J I x.
Proof.
intros Hic *.
progress unfold I_mul_subset.
progress unfold I_mul_subset_prop.
apply propositional_extensionality.
split; intros (lxy & Hlxy & H1 & H). {
  exists (List.map (λ xy, (snd xy, fst xy)) lxy).
  rewrite List.length_map.
  split; [ easy | ].
  split. {
    intros y z Hyz.
    apply List.in_map_iff in Hyz.
    destruct Hyz as ((u, v) & Hu & Huv).
    injection Hu; clear Hu; intros; subst u v.
    rewrite and_comm.
    now apply H1.
  }
  subst x.
  do 2 rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_map; cbn.
  apply rngl_summation_list_eq_compat.
  intros.
  apply (rngl_mul_comm Hic).
} {
  exists (List.map (λ xy, (snd xy, fst xy)) lxy).
  rewrite List.length_map.
  split; [ easy | ].
  split. {
    intros y z Hyz.
    apply List.in_map_iff in Hyz.
    destruct Hyz as ((u, v) & Hu & Huv).
    injection Hu; clear Hu; intros; subst u v.
    rewrite and_comm.
    now apply H1.
  }
  subst x.
  do 2 rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_map; cbn.
  apply rngl_summation_list_eq_compat.
  intros.
  apply (rngl_mul_comm Hic).
}
Qed.

Theorem I_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ I J : ideal T, (I * J)%I = (J * I)%I
  else not_applicable.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
intros.
apply (I_mul_subset_comm Hic).
Qed.

Theorem I_mul_subset_1_r I : ∀ x, I_mul_subset I 1 x = (x ∈ I)%I.
Proof.
destruct_ix.
intros.
apply propositional_extensionality.
split. {
  intros (lxy & Hlxy & H1 & H); subst x.
  rewrite rngl_summation_list_pair.
  induction lxy as [| (x, y)]; [ easy | ].
  clear Hlxy.
  destruct (Nat.eq_dec (length lxy) 0) as [Hnz| Hnz]. {
    apply List.length_zero_iff_nil in Hnz.
    subst lxy.
    rewrite rngl_summation_list_only_one.
    apply i_mul_r; cbn.
    now apply (H1 x y); left.
  }
  specialize (IHlxy Hnz).
  rewrite rngl_summation_list_cons; cbn.
  apply i_add. {
    apply i_mul_r.
    now apply (H1 x y); left.
  }
  apply IHlxy.
  intros x' y' Hxy'.
  now apply H1; right.
} {
  intros Hax.
  exists [(x, 1%L)].
  split; [ easy | ].
  split. {
    intros y z Hyz.
    destruct Hyz as [Hy| Hy]; [ | easy ].
    now injection Hy; clear Hy; intros; subst y z.
  }
  rewrite rngl_summation_list_pair.
  rewrite rngl_summation_list_only_one.
  cbn; symmetry.
  apply rngl_mul_1_r.
}
Qed.

Theorem I_opt_mul_1_r :
  if rngl_mul_is_comm T then not_applicable else ∀ I : ideal T, (I * 1)%I = I.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
symmetry in Hic.
destruct ic; [ easy | ].
intros.
apply eq_ideal_eq; cbn.
apply functional_extensionality_dep.
intros.
apply I_mul_subset_1_r.
Qed.

Theorem I_opt_mul_add_distr_r :
  if rngl_mul_is_comm T then not_applicable
  else ∀ I J K : ideal T, ((I + J) * K)%I = (I * K + J * K)%I.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic.
symmetry in Hic.
destruct ic; [ easy | ].
apply I_mul_add_distr_r.
Qed.

Theorem I_opt_integral I J :
  (I * J)%I = 0%I → I = 0%I ∨ J = 0%I ∨ True ∨ True.
Proof. now intros; right; right; left. Qed.

Theorem I_characteristic_prop :
  let roi := I_ring_like_op in
  if Nat.b2n (rngl_characteristic T =? 1) =? 0 then
    ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else
   (∀ i : nat,
      0 < i < Nat.b2n (rngl_characteristic T =? 1) → rngl_of_nat i ≠ 0%L)
   ∧ rngl_of_nat (Nat.b2n (rngl_characteristic T =? 1)) = 0%L.
Proof.
destruct_ix.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  rewrite Hc1; cbn.
  split; [ intros i Hi; flia Hi | ].
  rewrite I_add_comm, I_add_0_l.
  apply eq_ideal_eq.
  cbn.
  apply functional_extensionality_dep.
  intros x; symmetry.
  rewrite (H1 x).
  cbn.
  now apply propositional_extensionality.
}
apply Nat.eqb_neq in Hc1.
rewrite Hc1; cbn - [ rngl_of_nat ].
apply Nat.eqb_neq in Hc1.
intros n H.
specialize (rngl_1_neq_0 Hc1) as H1.
rewrite rngl_of_nat_succ in H.
cbn in H.
apply eq_ideal_eq in H.
apply (f_equal (λ f, f 1%L)) in H.
cbn in H.
rewrite <- H in H1; clear H.
apply H1; clear H1.
exists 1%L, 0%L.
rewrite rngl_add_0_r.
split; [ easy | ].
split; [ | easy ].
apply i_zero.
Qed.

Definition I_ring_like_prop : ring_like_prop (ideal T) :=
  let roi := I_ring_like_op in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := Nat.b2n (rngl_characteristic T =? 1);
     rngl_add_comm := I_add_comm;
     rngl_add_assoc := I_add_assoc;
     rngl_add_0_l := I_add_0_l;
     rngl_mul_assoc := I_mul_assoc;
     rngl_mul_1_l := I_mul_1_l;
     rngl_mul_add_distr_l := I_mul_add_distr_l;
     rngl_opt_mul_comm := I_opt_mul_comm;
     rngl_opt_mul_1_r := I_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := I_opt_mul_add_distr_r;
     rngl_opt_add_opp_diag_l := NA;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := I_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA;
     rngl_characteristic_prop := I_characteristic_prop |}.

End a.
