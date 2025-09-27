(** * Lap_algebra

This module defines a ring-like algebra over polynomials represented by
lists ("lap" stands for _list as polynomial_). For example, the polynomial
[ax² + bx + c] is represented as the list [[c; b; a]].

This module does not check whether the leading coefficient is non-zero.
That is enforced in the actual polynomial implementation
[[RingLike.Polynomial_algebra]].

See the module [[RingLike.Core]] for the general description
of the ring-like library.

Usage:
<<
    Require Import RingLike.Lap_algebra.
>>
*)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
Import List.ListNotations Init.Nat.
Open Scope list.

Require Import Core Misc Utils.
Require Import Iter_Add.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

(* normalization: lap not ending with 0s *)

Fixpoint strip_0s la :=
  match la with
  | [] => []
  | a :: la' => if (a =? 0)%L then strip_0s la' else la
  end.

Definition lap_norm la := List.rev (strip_0s (List.rev la)).

Lemma strip_0s_app : ∀ la lb,
  strip_0s (la ++ lb) =
  match strip_0s la with
  | [] => strip_0s lb
  | lc => lc ++ lb
  end.
Proof.
intros.
revert lb.
induction la as [| a]; intros; [ easy | cbn ].
destruct (a =? 0)%L; [ apply IHla | easy ].
Qed.

(* *)

Definition lap_zero : list T := [].
Definition lap_one : list T := [1%L].

(* addition *)

Definition lap_add la lb :=
  List_map2 rngl_add
    (la ++ List.repeat 0%L (length lb - length la))
    (lb ++ List.repeat 0%L (length la - length lb)).

Theorem fold_lap_add :
  ∀ la lb,
  List_map2 rngl_add (la ++ List.repeat 0%L (length lb - length la))
    (lb ++ List.repeat 0%L (length la - length lb)) =
  lap_add la lb.
Proof. easy. Qed.

(* multiplication *)

Fixpoint lap_convol_mul la lb i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%L ::
      lap_convol_mul la lb (S i) len1
  end.

Definition lap_mul la lb :=
  match la with
  | [] => []
  | _ =>
      match lb with
      | [] => []
      | _ => lap_convol_mul la lb 0 (length la + length lb - 1)
      end
  end.

(* *)

Definition lap_opt_one :=
  match rngl_opt_one T with
  | Some one => Some [one]
  | None => None
  end.

End a.

Declare Scope lap_scope.
Delimit Scope lap_scope with lap.

Arguments lap_add {T ro} (la lb)%_lap.
Arguments lap_convol_mul {T ro} (la lb)%_lap (i len)%_nat.
Arguments lap_mul {T ro} (la lb)%_lap.
Arguments lap_norm {T ro} la%_lap.

Notation "0" := lap_zero : lap_scope.
Notation "1" := lap_one : lap_scope.
Notation "a + b" := (lap_add a b) : lap_scope.
Notation "a * b" := (lap_mul a b) : lap_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Heo : rngl_has_eq_dec_or_order T = true).

Theorem lap_add_0_l : ∀ la, (0 + la)%lap = la.
Proof.
intros; cbn.
rewrite Nat.sub_0_r, List.app_nil_r.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_add_0_l; f_equal.
Qed.

Theorem lap_add_0_r : ∀ la, (la + 0)%lap = la.
Proof.
intros.
unfold lap_add; cbn.
rewrite Nat.sub_0_r, List.app_nil_r.
induction la as [| a]; [ easy | cbn ].
now rewrite rngl_add_0_r; f_equal.
Qed.

Theorem lap_mul_0_l : ∀ la, (0 * la = 0)%lap.
Proof. easy. Qed.

Theorem lap_mul_0_r : ∀ la, (la * 0 = 0)%lap.
Proof. now intros; destruct la. Qed.

Theorem eq_lap_mul_0 : ∀ la lb, (la * lb = 0)%lap → la = 0%lap ∨ lb = 0%lap.
Proof.
intros * Hab.
destruct la as [| a]; [ now left | right ].
destruct lb as [| b]; [ easy | exfalso ].
cbn in Hab.
now rewrite Nat.add_succ_r in Hab.
Qed.

(* *)

Theorem lap_add_length : ∀ la lb,
  length (la + lb)%lap = max (length la) (length lb).
Proof.
intros.
unfold lap_add.
rewrite List_length_map2.
do 2 rewrite List.length_app, List.repeat_length.
apply min_add_sub_max.
Qed.

(* lap opposite or subtraction *)

(* cannot define opposite or subtraction because [1]-[1] returns
   [0], instead of [] *)
Definition lap_opt_opp_or_psub :
  option ((list T → list T) + (list T → list T → list T)) :=
  None.

(* lap quotient *)

Definition lap_opt_inv_or_pdiv :
  option ((list T → list T) + (list T → list T → list T)) :=
  None.

(* *)

Fixpoint lap_all_0 zero (eqb : T → T → bool) (la : list T) :=
  match la with
  | [] => true
  | a :: la' => if eqb a zero then lap_all_0 zero eqb la' else false
  end.

Fixpoint lap_eqb zero (eqb : T → _) (la lb : list T) :=
  match la with
  | [] => lap_all_0 zero eqb lb
  | a :: la' =>
      match lb with
      | [] => lap_all_0 zero eqb la
      | b :: lb' => if eqb a b then lap_eqb zero eqb la' lb' else false
      end
  end.

Theorem lap_eq_dec : ∀ la lb : list T, {la = lb} + {la ≠ lb}.
Proof.
intros.
remember (lap_eqb rngl_zero rngl_eqb la lb) as x eqn:Hx.
symmetry in Hx.
destruct x. {
  revert lb Hx.
  induction la as [| a]; intros. {
    cbn in Hx.
    induction lb as [| b]; [ now left | now right ].
  }
  cbn in Hx.
  destruct lb as [| b]; [ now right | ].
  remember (a =? b)%L as ab eqn:Hab.
  symmetry in Hab.
  destruct ab; [ | easy ].
  apply (rngl_eqb_eq Heo) in Hab.
  subst b.
  specialize (IHla _ Hx).
  destruct IHla as [IHla| IHla]; [ now subst lb; left | ].
  right.
  now intros H; injection H; intros.
} {
  right.
  intros H; subst lb.
  induction la as [| a]; [ easy | ].
  cbn in Hx.
  rewrite (rngl_eqb_refl Heo) in Hx.
  congruence.
}
Qed.

(* lap ring-like operators *)

Definition lap_ring_like_op : ring_like_op (list T) :=
  {| rngl_zero := [];
     rngl_add := lap_add;
     rngl_mul := lap_mul;
     rngl_opt_one := lap_opt_one;
     rngl_opt_opp_or_psub := lap_opt_opp_or_psub;
     rngl_opt_inv_or_pdiv := lap_opt_inv_or_pdiv;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := Some lap_eq_dec;
     rngl_opt_leb := None |}.

(* commutativity of addition *)

Theorem lap_add_comm : ∀ al1 al2,
  (al1 + al2)%lap = (al2 + al1)%lap.
Proof.
intros al1 al2.
unfold lap_add.
rewrite List_map2_swap.
apply List_map2_ext_in.
intros (a, b) Hab; cbn.
apply rngl_add_comm.
Qed.

(* associativity of addition *)

Theorem List_map2_rngl_add_0_l :
  ∀ la, List_map2 rngl_add (List.repeat 0%L (length la)) la = la.
Proof.
intros.
induction la as [| la]; [ easy | cbn ].
now rewrite rngl_add_0_l; f_equal.
Qed.

Theorem List_map2_rngl_add_0_r :
  ∀ la, List_map2 rngl_add la (List.repeat 0%L (length la)) = la.
Proof.
intros.
induction la as [| la]; [ easy | cbn ].
now rewrite rngl_add_0_r; f_equal.
Qed.

Theorem lap_add_assoc : ∀ al1 al2 al3,
  (al1 + (al2 + al3))%lap = (al1 + al2 + al3)%lap.
Proof.
intros al1 al2 al3.
revert al2 al3.
induction al1; intros; [ now do 2 rewrite lap_add_0_l | ].
cbn.
destruct al2. {
  cbn.
  rewrite Nat.sub_0_r, List.app_nil_r.
  rewrite List_length_map2, List.repeat_length, Nat.min_id.
  rewrite List_length_map2, List.app_nil_r, List.repeat_length.
  rewrite Nat.min_id.
  rewrite List_map2_rngl_add_0_l.
  rewrite rngl_add_0_r.
  remember (al3 ++ _) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]; [ easy | ].
  f_equal.
  now rewrite List_map2_rngl_add_0_r.
}
destruct al3. {
  cbn.
  rewrite rngl_add_assoc; f_equal.
  do 2 rewrite List_length_map2.
  rewrite List.app_nil_r, List.repeat_length, Nat.min_id.
  rewrite List_map2_rngl_add_0_r, List.app_nil_r.
  do 2 rewrite List.length_app, List.repeat_length.
  rewrite fold_lap_add.
  rewrite min_add_sub_max.
  rewrite <- lap_add_length.
  now rewrite List_map2_rngl_add_0_r.
}
cbn.
rewrite rngl_add_assoc; f_equal.
do 2 rewrite List_length_map2.
do 4 rewrite List.length_app, List.repeat_length.
do 2 rewrite min_add_sub_max.
do 2 rewrite fold_lap_add.
do 2 rewrite <- lap_add_length.
do 2 rewrite fold_lap_add.
apply IHal1.
Qed.

(* associativity of multiplication *)

Theorem eq_lap_norm_eq_length : ∀ la lb,
  lap_norm la = lap_norm lb
  → length la = length lb
  → la = lb.
Proof.
intros * Hll Hlen.
unfold lap_norm in Hll.
apply List.rev_inj in Hll.
setoid_rewrite <- List.length_rev in Hlen.
enough (H : List.rev la = List.rev lb) by now apply List.rev_inj in H.
remember (List.rev la) as l; clear la Heql; rename l into la.
remember (List.rev lb) as l; clear lb Heql; rename l into lb.
revert la Hll Hlen.
induction lb as [| b]; intros. {
  now apply List.length_zero_iff_nil in Hlen.
}
destruct la as [| a]; [ easy | ].
cbn in Hll, Hlen.
apply Nat.succ_inj in Hlen.
do 2 rewrite if_bool_if_dec in Hll.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
  apply (rngl_eqb_eq Heo) in Haz; subst a.
  destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
    apply (rngl_eqb_eq Heo) in Hbz; subst b.
    f_equal.
    now apply IHlb.
  }
  exfalso; clear - Hbz Hll Hlen.
  assert (H : length la ≤ length lb) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction la as [| a]; [ easy | ].
  cbn in Hll.
  rewrite if_bool_if_dec in Hll.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    cbn in Hlen.
    clear a Haz.
    apply IHla; [ easy | flia Hlen ].
  }
  rewrite Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
  exfalso; clear b Hbz.
  clear - Haz Hll Hlen.
  assert (H : length lb ≤ length la) by flia Hlen.
  clear Hlen; rename H into Hlen.
  induction lb as [| b]; [ easy | ].
  cbn in Hll.
  rewrite if_bool_if_dec in Hll.
  destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
    cbn in Hlen.
    clear b Hbz.
    apply IHlb; [ easy | flia Hlen ].
  }
  rewrite <- Hll in Hlen; cbn in Hlen.
  flia Hlen.
}
easy.
Qed.

Theorem lap_convol_mul_length : ∀ la lb i len,
  length (lap_convol_mul la lb i len) = len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | ].
cbn.
now rewrite IHlen.
Qed.

Theorem list_nth_lap_eq : ∀ la lb,
  (∀ i, (List.nth i la 0 = List.nth i lb 0)%L)
  → lap_norm la = lap_norm lb.
Proof.
intros la lb Hi.
unfold lap_norm; f_equal.
revert lb Hi.
induction la as [| a]; intros. {
  induction lb as [| b]; [ reflexivity | ].
  specialize (Hi 0) as H; cbn in H.
  subst b; cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (List.rev lb)) as lc eqn:Hlc; symmetry in Hlc.
  rewrite (rngl_eqb_refl Heo).
  destruct lc as [| c]; [ easy | ].
  assert (H : lap_norm [] = lap_norm lb). {
    unfold lap_norm; cbn.
    cbn in IHlb.
    change (List.rev [] = List.rev (strip_0s (List.rev lb))).
    f_equal.
    rewrite Hlc.
    apply IHlb.
    intros i; cbn; rewrite Tauto_match_nat_same.
    now specialize (Hi (S i)); cbn in Hi.
  }
  cbn in H.
  unfold lap_norm in H.
  rewrite Hlc in H.
  symmetry in H.
  now apply List_eq_rev_nil in H.
} {
  cbn.
  rewrite strip_0s_app.
  remember (strip_0s (List.rev la)) as lc eqn:Hlc; symmetry in Hlc.
  destruct lc as [| c]. {
    assert (Hla : ∀ i, List.nth i la 0%L = 0%L). {
      intros i.
      clear - ro rp Heo Hlc.
      revert i.
      induction la as [| a]; intros; cbn. {
        now rewrite Tauto_match_nat_same.
      }
      destruct i. {
        cbn in Hlc.
        rewrite strip_0s_app in Hlc; cbn in Hlc.
        remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
        destruct lb as [| b]; [ | easy ].
        rewrite if_bool_if_dec in Hlc.
        destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
        now apply (rngl_eqb_eq Heo) in Haz.
      }
      apply IHla.
      cbn in Hlc.
      rewrite strip_0s_app in Hlc; cbn in Hlc.
      remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
      destruct lb as [| b]; [ easy | easy ].
    }
    cbn.
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
      apply (rngl_eqb_eq Heo) in Haz.
      assert (Hlb : ∀ i, List.nth i lb 0%L = 0%L). {
        intros.
        rewrite <- Hi; cbn.
        destruct i; [ easy | ].
        apply Hla.
      }
      clear - ro rp Heo Hlb.
      induction lb as [| b]; [ easy | cbn ].
      specialize (Hlb 0) as H1; cbn in H1; subst b.
      rewrite strip_0s_app; cbn.
      rewrite (rngl_eqb_refl Heo).
      rewrite <- IHlb; [ easy | ].
      intros i.
      now specialize (Hlb (S i)).
    }
    apply (rngl_eqb_neq Heo) in Haz.
    destruct lb as [| b]; [ now specialize (Hi 0); cbn in Hi | cbn ].
    rewrite strip_0s_app; cbn.
    remember (strip_0s (List.rev lb)) as ld eqn:Hld; symmetry in Hld.
    destruct ld as [| d]. {
      rewrite if_bool_if_dec.
      destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
        apply (rngl_eqb_eq Heo) in Hbz; subst b.
        now specialize (Hi 0).
      }
      f_equal.
      now specialize (Hi 0).
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, List.nth i la 0%L = List.nth i lb 0%L). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  destruct lb as [| b]. {
    specialize (IHla []).
    assert (H : ∀ i : nat, List.nth i la 0%L = List.nth i [] 0%L). {
      intros i; cbn; rewrite Tauto_match_nat_same.
      now specialize (Hi (S i)).
    }
    now specialize (IHla H).
  }
  cbn.
  rewrite strip_0s_app; cbn.
  remember (strip_0s (List.rev lb)) as ld eqn:Hld; symmetry in Hld.
  destruct ld as [| d]. {
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
      apply (rngl_eqb_eq Heo) in Hbz; subst b.
      specialize (IHla lb).
      assert (H : ∀ i : nat, List.nth i la 0%L = List.nth i lb 0%L). {
        intros i.
        now specialize (Hi (S i)); cbn in Hi.
      }
      specialize (IHla H); clear H.
      now rewrite Hld in IHla.
    }
    specialize (IHla lb).
    assert (H : ∀ i : nat, List.nth i la 0%L = List.nth i lb 0%L). {
      intros i.
      now specialize (Hi (S i)); cbn in Hi.
    }
    specialize (IHla H); clear H.
    now rewrite Hld in IHla.
  }
  specialize (Hi 0) as H1; cbn in H1; subst b.
  do 2 rewrite List.app_comm_cons; f_equal.
  rewrite <- Hld.
  apply IHla.
  now intros i; specialize (Hi (S i)).
}
Qed.

Theorem eq_lap_convol_mul_nil : ∀ la lb i len,
  lap_convol_mul la lb i len = [] → len = 0.
Proof. now intros; induction len. Qed.

Theorem list_nth_lap_convol_mul_aux :
  rngl_has_opp_or_psub T = true →
  ∀ la lb n i len,
  List.length la + List.length lb - 1 = (i + len)%nat
  → (List.nth n (lap_convol_mul la lb i len) 0%L =
     ∑ (j = 0, n + i),
     List.nth j la 0 * List.nth (n + i - j) lb 0)%L.
Proof.
intros Hos * Hlen.
revert la lb i n Hlen.
induction len; intros. {
  cbn.
  rewrite Nat.add_0_r in Hlen.
  rewrite all_0_rngl_summation_0; [ now destruct n | ].
  intros j (_, Hj).
  destruct (le_dec (length la) j) as [H1| H1]. {
    rewrite List.nth_overflow; [ | easy ].
    apply (rngl_mul_0_l Hos).
  }
  destruct (le_dec (length lb) (n + i - j)) as [H2| H2]. {
    rewrite (List.nth_overflow _ _ H2).
    now apply rngl_mul_0_r.
  }
  exfalso; apply H2; clear Hj H2.
  apply Nat.nle_gt in H1; subst i.
  flia H1.
}
cbn.
destruct n; [ easy | ].
rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hlen.
rewrite IHlen; [ | easy ].
now rewrite Nat.add_succ_r, <- Nat.add_succ_l.
Qed.

Theorem list_nth_lap_convol_mul :
  rngl_has_opp_or_psub T = true →
  ∀ la lb i len,
  len = length la + length lb - 1
  → (List.nth i (lap_convol_mul la lb 0 len) 0 =
     ∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%L.
Proof.
intros Hos * Hlen.
symmetry in Hlen.
rewrite (list_nth_lap_convol_mul_aux Hos); [ | easy ].
now rewrite Nat.add_0_r.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_r :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc k,
   (∑ (i = 0, k),
      List.nth i lc 0 *
      List.nth (k - i) (lap_convol_mul la lb 0 (length la + length lb - 1))
        0 =
    ∑ (i = 0, k),
      List.nth (k - i) lc 0 *
      ∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0)%L.
Proof.
intros Hos la lb lc k.
rewrite rngl_summation_rtl.
apply rngl_summation_eq_compat; intros i (_, Hi).
rewrite Nat.add_0_r.
progress f_equal.
rewrite Nat.sub_sub_distr; [ | easy | easy ].
rewrite Nat.sub_diag.
now apply list_nth_lap_convol_mul.
Qed.

Theorem summation_mul_list_nth_lap_convol_mul_l :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc k,
  ∑ (i = 0, k),
    List.nth i (lap_convol_mul la lb 0 (length la + length lb - 1)) 0 *
    List.nth (k - i) lc 0 =
  ∑ (i = 0, k),
    (∑ (j = 0, i), List.nth j la 0 * List.nth (i - j) lb 0) *
    List.nth (k - i) lc 0.
Proof.
intros Hos la lb lc k.
apply rngl_summation_eq_compat; intros i (_, Hi).
f_equal.
now rewrite list_nth_lap_convol_mul.
Qed.

Theorem lap_norm_mul_assoc :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc, lap_norm (la * (lb * lc)) = lap_norm (la * lb * lc).
Proof.
intros Hos la lb lc.
unfold lap_mul.
destruct lc as [| c]. {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]; [ easy | cbn ].
  now rewrite <- Nat.add_succ_comm.
}
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
apply list_nth_lap_eq; intros k.
remember (lap_convol_mul la' lb' 0 (length la' + length lb' - 1)) as ld
  eqn:Hld.
remember (lap_convol_mul lb' lc' 0 (length lb' + length lc' - 1)) as le
  eqn:Hle.
symmetry in Hld, Hle.
destruct ld as [| d]. {
  destruct le as [| e]; [ easy | cbn ].
  rewrite Tauto_match_nat_same.
  move e before c.
  apply eq_lap_convol_mul_nil in Hld.
  apply Nat.sub_0_le in Hld.
  remember (length la' + length lb') as len eqn:Hlen.
  symmetry in Hlen.
  destruct len. {
    apply Nat.eq_add_0 in Hlen.
    now subst la'.
  }
  destruct len; [ clear Hld | flia Hld ].
  apply Nat.eq_add_1 in Hlen.
  destruct Hlen as [Hlen| Hlen]; [ now rewrite Hlb' in Hlen | ].
  now rewrite Hla' in Hlen.
}
destruct le as [| e]. {
  cbn; rewrite Tauto_match_nat_same.
  move d before c.
  apply eq_lap_convol_mul_nil in Hle.
  apply Nat.sub_0_le in Hle.
  remember (length lb' + length lc') as len eqn:Hlen.
  symmetry in Hlen.
  destruct len. {
    apply Nat.eq_add_0 in Hlen.
    now subst lb'.
  }
  destruct len; [ clear Hle | flia Hle ].
  apply Nat.eq_add_1 in Hlen.
  destruct Hlen as [Hlen| Hlen]; [ now rewrite Hlc' in Hlen | ].
  now rewrite Hlb' in Hlen.
}
rewrite (list_nth_lap_convol_mul Hos); [ | easy ].
rewrite (list_nth_lap_convol_mul Hos); [ | easy ].
rewrite <- Hld, <- Hle.
rewrite (summation_mul_list_nth_lap_convol_mul_r Hos).
rewrite (summation_mul_list_nth_lap_convol_mul_l Hos).
move d before c; move e before d.
move lb' before la'; move ld before lc; move lc' before lb'.
move le before ld.
symmetry.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite rngl_mul_summation_distr_r; [ | easy ].
  remember (∑ (j = 0, i), _) as x; subst x.
  easy.
}
cbn.
rewrite rngl_summation_depend_summation_exch.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    now rewrite <- rngl_mul_assoc.
  }
  cbn.
  rewrite <- rngl_mul_summation_distr_l; [ | easy ].
  remember (∑ (j = _, _), _) as x; subst x.
  easy.
}
cbn.
symmetry.
rewrite rngl_summation_rtl.
erewrite rngl_summation_eq_compat. 2: {
  intros i Hi.
  rewrite Nat.add_0_r.
  rewrite Nat.sub_sub_distr; [ | easy | easy ].
  rewrite Nat.sub_diag, Nat.add_0_l.
  easy.
}
cbn.
apply rngl_summation_eq_compat.
intros i Hi.
f_equal.
symmetry.
rewrite (rngl_summation_shift i); [ | easy ].
rewrite Nat.sub_diag.
remember (∑ (j = _, _), _) as x; subst x.
erewrite rngl_summation_eq_compat. 2: {
  intros j Hj.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite Nat.sub_add_distr.
  rewrite Nat_sub_sub_swap.
  easy.
}
easy.
Qed.

Theorem lap_mul_assoc :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc, (la * (lb * lc))%lap = (la * lb * lc)%lap.
Proof.
intros Hos *.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]; [ easy | ].
  destruct lc as [| c]. {
    now cbn; destruct (lap_convol_mul _ _ _ _).
  }
  cbn.
  do 4 (rewrite Nat.add_succ_r; cbn); f_equal.
  rewrite rngl_summation_only_one; cbn.
  rewrite rngl_summation_only_one; cbn.
  do 4 rewrite lap_convol_mul_length.
  apply Nat.add_assoc.
}
apply (lap_norm_mul_assoc Hos).
Qed.

(* multiplication by 1 *)

Theorem lap_convol_mul_const_l :
  rngl_has_opp_or_psub T = true →
  ∀ a la i len,
  length la = i + len
  → lap_convol_mul [a] la i len =
    List.map (λ b, (a * b)%L) (List.skipn i la).
Proof.
intros Hos * Hlen.
revert i Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen; rewrite <- Hlen.
  now rewrite List.skipn_all.
}
cbn - [ List.nth ].
rewrite rngl_summation_split_first; [ | easy ].
rewrite all_0_rngl_summation_0. 2: {
  intros j Hj.
  destruct j; [ flia Hj | cbn ].
  rewrite Tauto_match_nat_same.
  apply (rngl_mul_0_l Hos).
}
rewrite Nat.sub_0_r, rngl_add_0_r; cbn.
rewrite IHlen; [ | now rewrite Nat.add_succ_r in Hlen ].
symmetry.
rewrite (List_skipn_is_cons 0%L); [ easy | flia Hlen ].
Qed.

Theorem lap_convol_mul_const_r :
  rngl_has_opp_or_psub T = true →
  ∀ a la i len,
  length la = i + len
  → lap_convol_mul la [a] i len =
    List.map (λ b, (b * a)%L) (List.skipn i la).
Proof.
intros Hos * Hlen.
revert i Hlen.
induction len; intros. {
  rewrite Nat.add_0_r in Hlen; rewrite <- Hlen.
  now rewrite List.skipn_all.
}
cbn - [ List.nth ].
rewrite rngl_summation_split_last; [ | easy ].
rewrite all_0_rngl_summation_0. 2: {
  intros j Hj.
  replace (i - (j - 1)) with (S (i - j)) by flia Hj; cbn.
  rewrite Tauto_match_nat_same.
  apply (rngl_mul_0_r Hos).
}
rewrite Nat.sub_diag, rngl_add_0_l; cbn.
rewrite IHlen; [ | flia Hlen ].
symmetry.
rewrite (List_skipn_is_cons 0%L); [ easy | flia Hlen ].
Qed.

Theorem lap_mul_const_l :
  rngl_has_opp_or_psub T = true →
  ∀ a la, ([a] * la)%lap = List.map (λ b : T, (a * b)%L) la.
Proof.
intros Hos *.
unfold lap_mul.
destruct la as [| b]; [ easy | ].
now rewrite (lap_convol_mul_const_l Hos).
Qed.

Theorem lap_mul_const_r :
  rngl_has_opp_or_psub T = true →
  ∀ a la, (la * [a])%lap = List.map (λ b : T, (b * a)%L) la.
Proof.
intros Hos *.
unfold lap_mul.
destruct la as [| b]; [ easy | ].
rewrite Nat.add_sub.
now rewrite (lap_convol_mul_const_r Hos).
Qed.

(* distributivity *)

Fixpoint lap_convol_mul_add_l (al1 al2 al3 : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i),
       (List.nth j al1 0 + List.nth j al2 0) *
       List.nth (i - j) al3 0)%L ::
       lap_convol_mul_add_l al1 al2 al3 (S i) len1
  end.

Fixpoint lap_convol_mul_add_r (al1 al2 al3 : list T) i len :=
  match len with
  | O => []
  | S len1 =>
      (∑ (j = 0, i),
       List.nth j al1 0 *
       (List.nth (i - j) al2 0 + List.nth (i - j) al3 0))%L ::
       lap_convol_mul_add_r al1 al2 al3 (S i) len1
  end.

Theorem lap_convol_mul_succ : ∀ la lb i len,
  lap_convol_mul la lb i (S len) =
  lap_convol_mul la lb i len ++
    [∑ (j = 0, i + len),
     List.nth j la 0 * List.nth (i + len - j) lb 0]%L.
Proof.
intros.
cbn.
revert i.
induction len; intros. {
  now rewrite Nat.add_0_r.
}
cbn.
f_equal.
specialize (IHlen (S i)).
cbn in IHlen.
rewrite Nat.add_succ_r.
apply IHlen.
Qed.

Theorem lap_norm_app_0_r : ∀ la lb,
  (∀ i, List.nth i lb 0%L = 0%L)
  → lap_norm (la ++ lb) = lap_norm la.
Proof.
intros * Hlb.
unfold lap_norm; f_equal.
induction la as [| a]. {
  cbn; symmetry.
  induction lb as [| b]; [ easy | cbn ].
  rewrite strip_0s_app.
  rewrite <- IHlb. 2: {
    intros i.
    now specialize (Hlb (S i)).
  }
  specialize (Hlb 0); cbn in Hlb; rewrite Hlb; cbn.
  now rewrite rngl_eqb_refl.
}
cbn.
do 2 rewrite strip_0s_app.
now rewrite IHla.
Qed.

Theorem lap_convol_mul_more :
  rngl_has_opp_or_psub T = true →
  ∀ n la lb i len,
  length la + length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul la lb i len) =
    lap_norm (lap_convol_mul la lb i (len + n)).
Proof.
intros Hos * Habl.
induction n; [ rewrite Nat.add_0_r; reflexivity | idtac ].
rewrite Nat.add_succ_r.
rewrite lap_convol_mul_succ.
rewrite IHn.
symmetry; apply lap_norm_app_0_r.
intros j.
rewrite all_0_rngl_summation_0. {
  destruct j; [ easy | now destruct j ].
}
clear j.
intros j (_, Hj).
destruct (le_dec (length la) j) as [H1| H1]. {
  rewrite List.nth_overflow; [ | easy ].
  apply (rngl_mul_0_l Hos).
} {
  apply Nat.nle_gt in H1.
  destruct (le_dec (length lb) (i + (len + n) - j)) as [H2| H2]. {
    rewrite (List.nth_overflow _ _ H2).
    now apply rngl_mul_0_r.
  } {
    exfalso; apply H2; clear H2.
    flia Habl H1.
  }
}
Qed.

(* *)

Theorem lap_norm_List_map2_app_app_idemp_l :
  ∀ f, (∀ a, f a 0%L = a) →
  ∀ la lb,
  lap_norm
    (List_map2 f
       (lap_norm la ++ List.repeat 0%L (length lb - length (lap_norm la)))
       (lb ++ List.repeat 0%L (length (lap_norm la) - length lb))) =
  lap_norm
    (List_map2 f (la ++ List.repeat 0%L (length lb - length la))
       (lb ++ List.repeat 0%L (length la - length lb))).
Proof.
intros * Hf *.
unfold lap_norm; f_equal.
revert la.
induction lb as [| b]; intros. {
  cbn.
  do 2 rewrite List.app_nil_r, Nat.sub_0_r.
  rewrite List_rev_map2. 2: {
    unfold lap_norm.
    now rewrite List.repeat_length, List.length_rev.
  }
  rewrite List_rev_map2; [ | symmetry; apply List.repeat_length ].
  do 2 rewrite List.rev_repeat.
  unfold lap_norm.
  rewrite List.rev_involutive, List.length_rev.
  rewrite <- (List.length_rev la).
  remember (List.rev la) as lb eqn:Hlb.
  clear la Hlb.
  rename lb into la.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Heo) in Haz; subst a.
  rewrite Hf.
  rewrite (rngl_eqb_refl Heo).
  apply IHla.
}
destruct la as [| a]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHlb.
remember (strip_0s (List.rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Heo) in Haz.
    subst a; cbn.
    rewrite List.app_nil_r, Nat.sub_0_r.
    now rewrite strip_0s_app.
  }
  cbn.
  now rewrite strip_0s_app.
}
cbn.
rewrite List.rev_app_distr; cbn.
now rewrite strip_0s_app.
Qed.

(* *)

Theorem lap_add_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la + lb) = lap_norm (la + lb).
Proof.
intros.
apply lap_norm_List_map2_app_app_idemp_l.
apply rngl_add_0_r.
Qed.

Theorem lap_add_norm_idemp_r : ∀ la lb,
  lap_norm (la + lap_norm lb) = lap_norm (la + lb).
Proof.
intros.
rewrite lap_add_comm.
rewrite lap_add_norm_idemp_l.
f_equal; apply lap_add_comm.
Qed.

(* *)

Theorem list_nth_lap_add : ∀ k la lb,
  (List.nth k (lap_add la lb) 0 =
   List.nth k la 0 + List.nth k lb 0)%L.
Proof.
intros k la lb.
revert la lb.
induction k; intros. {
  destruct la as [| a]; cbn. {
    rewrite rngl_add_0_l, Nat.sub_0_r, List.app_nil_r.
    f_equal.
    apply List_map2_rngl_add_0_l.
  }
  destruct lb as [| b]; cbn; [ now rewrite rngl_add_0_r | ].
  easy.
} {
  destruct la as [| a]; cbn. {
    rewrite rngl_add_0_l, Nat.sub_0_r, List.app_nil_r.
    f_equal.
    apply List_map2_rngl_add_0_l.
  }
  destruct lb as [| b]; cbn. {
    rewrite List.app_nil_r, rngl_add_0_r.
    f_equal.
    apply List_map2_rngl_add_0_r.
  }
  apply IHk.
}
Qed.

Theorem lap_convol_mul_lap_add_r : ∀ la lb lc i len,
  lap_convol_mul la (lb + lc) i len = lap_convol_mul_add_r la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat; intros j (_, Hj).
f_equal.
now rewrite list_nth_lap_add.
Qed.

Theorem lap_add_lap_convol_mul_r : ∀ la lb lc i len,
  (lap_convol_mul la lb i len + lap_convol_mul la lc i len)%lap =
  lap_convol_mul_add_r la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ easy | cbn ].
rewrite <- IHlen; f_equal.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros j (_, Hj).
now rewrite rngl_mul_add_distr_l.
Qed.

Theorem lap_norm_mul_add_distr_l :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc, lap_norm (la * (lb + lc)) = lap_norm (la * lb + la * lc).
Proof.
intros Hos la lb lc.
unfold lap_mul.
destruct la as [| a]; [ easy | ].
destruct lb as [| b]; [ now do 2 rewrite lap_add_0_l | ].
destruct lc as [| c]. {
  cbn.
  rewrite rngl_add_0_r.
  do 2 rewrite List.app_nil_r.
  do 3 rewrite Nat.sub_0_r.
  now do 2 rewrite List_map2_rngl_add_0_r.
}
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length la' + length (lap_add lb' lc') - 1) as labc.
remember (length la' + length lb' - 1) as lab.
remember (length la' + length lc' - 1) as lac.
rewrite Heqlabc.
remember (lap_add lb' lc') as lbc.
symmetry in Heqlbc.
destruct lbc as [| bc]. {
  cbn.
  now subst lb' lc'.
}
rewrite <- Heqlbc in Heqlabc |-*.
rewrite (lap_convol_mul_more Hos) with (n := (lab + lac)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lac)%nat); [ | flia ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlac.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lab)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlac.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add_r.
now rewrite lap_add_lap_convol_mul_r.
Qed.

Theorem lap_mul_add_distr_l :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc, (la * (lb + lc))%lap = (la * lb + la * lc)%lap.
Proof.
intros Hos la lb lc.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]; [ easy | ].
  destruct lb as [| b]. {
    rewrite lap_mul_0_r.
    now do 2 rewrite lap_add_0_l.
  }
  destruct lc as [| c]. {
    rewrite lap_mul_0_r.
    now do 2 rewrite lap_add_0_r.
  }
  cbn.
  do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
  do 2 rewrite lap_convol_mul_length.
  do 2 rewrite List_length_map2.
  do 4 rewrite List.length_app.
  do 2 rewrite lap_convol_mul_length.
  do 4 rewrite List.repeat_length.
  do 2 rewrite min_add_sub_max.
  now rewrite Nat.add_max_distr_l.
}
apply (lap_norm_mul_add_distr_l Hos).
Qed.

(* optional multiplication commutativity *)

Theorem lap_convol_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ l1 l2 i len,
  lap_convol_mul l1 l2 i len = lap_convol_mul l2 l1 i len.
Proof.
intros Hic l1 l2 i len.
revert i.
induction len; intros; [ easy | cbn ].
rewrite IHlen; f_equal.
rewrite rngl_summation_rtl.
apply rngl_summation_eq_compat; intros j (_, Hj).
rewrite Nat.add_0_r.
rewrite (rngl_mul_comm Hic).
rewrite Nat.sub_sub_distr; [ | easy | easy ].
now rewrite Nat.sub_diag, Nat.add_0_l.
Qed.

Theorem lap_mul_comm :
  rngl_mul_is_comm T = true →
  ∀ la lb, (la * lb)%lap = (lb * la)%lap.
Proof.
intros Hic la lb.
unfold lap_mul.
destruct la as [| a]; [ now destruct lb | cbn ].
rewrite <- Nat.add_succ_comm; cbn.
rewrite (Nat.add_comm (length lb)).
now rewrite lap_convol_mul_comm.
Qed.

Theorem lap_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ a b : list T, (a * b)%lap = (b * a)%lap
  else not_applicable.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply (lap_mul_comm Hic).
Qed.

(* multiplication with 1 *)

Theorem lap_opt_mul_1_l : let rol := lap_ring_like_op in
  rngl_has_opp_or_psub T = true →
  if rngl_has_1 (list T) then ∀ la : list T, (1 * la)%L = la
  else not_applicable.
Proof.
intros * Hos *.
remember (rngl_has_1 (list T)) as onl eqn:Honl; symmetry in Honl.
destruct onl; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honl |-*.
  progress unfold rol in Honl; cbn in Honl.
  progress unfold lap_opt_one in Honl.
  now destruct rngl_opt_one.
}
intros; cbn.
replace (@rngl_one (list T) rol) with [@rngl_one T ro]. 2: {
  progress unfold rngl_one; cbn.
  progress unfold lap_opt_one; cbn.
  progress unfold rngl_has_1 in Hon.
  now destruct rngl_opt_one.
}
rewrite (lap_mul_const_l Hos).
induction la as [| a]; [ easy | cbn ].
f_equal; [ | apply IHla ].
apply (rngl_mul_1_l Hon).
Qed.

Theorem lap_opt_mul_1_r : let rol := lap_ring_like_op in
  rngl_has_opp_or_psub T = true →
  if rngl_mul_is_comm T then not_applicable
  else
   if rngl_has_1 (list T) then ∀ la : list T, (la * 1)%L = la
   else not_applicable.
Proof.
intros * Hos.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ easy | ].
remember (rngl_has_1 (list T)) as onl eqn:Honl; symmetry in Honl.
destruct onl; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honl |-*.
  progress unfold rol in Honl; cbn in Honl.
  progress unfold lap_opt_one in Honl.
  now destruct rngl_opt_one.
}
intros; cbn.
replace (@rngl_one (list T) rol) with [@rngl_one T ro]. 2: {
  progress unfold rngl_one; cbn.
  progress unfold lap_opt_one; cbn.
  progress unfold rngl_has_1 in Hon.
  now destruct rngl_opt_one.
}
rewrite (lap_mul_const_r Hos).
induction la as [| a]; [ easy | cbn ].
f_equal; [ | apply IHla ].
apply (rngl_mul_1_r Hon).
Qed.

(* *)

Theorem lap_convol_mul_lap_add_l : ∀ la lb lc i len,
  lap_convol_mul (la + lb) lc i len = lap_convol_mul_add_l la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat; intros j (_, Hj).
f_equal.
now rewrite list_nth_lap_add.
Qed.

Theorem lap_add_lap_convol_mul_l : ∀ la lb lc i len,
  (lap_convol_mul la lc i len + lap_convol_mul lb lc i len)%lap =
  lap_convol_mul_add_l la lb lc i len.
Proof.
intros la lb lc i len.
revert la lb lc i.
induction len; intros; [ easy | cbn ].
rewrite <- IHlen; f_equal.
rewrite <- rngl_summation_add_distr.
apply rngl_summation_eq_compat; intros j (_, Hj).
now rewrite rngl_mul_add_distr_r.
Qed.

Theorem lap_norm_mul_add_distr_r :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc : list T,
  lap_norm ((la + lb) * lc) = lap_norm (la * lc + lb * lc).
Proof.
intros Hos la lb lc.
unfold lap_mul.
destruct la as [| a]; [ now do 2 rewrite lap_add_0_l | ].
destruct lb as [| b]. {
  cbn.
  destruct lc as [| c]; [ easy | ].
  cbn; rewrite Nat.sub_0_r.
  rewrite rngl_add_0_r, List.app_nil_r, List_length_map2, List.repeat_length.
  rewrite Nat.min_id, Nat.sub_0_r, lap_add_0_r.
  now rewrite List_map2_rngl_add_0_r.
}
destruct lc as [| c]; [ easy | ].
move b before a; move c before b.
remember (a :: la) as la' eqn:Hla'.
remember (b :: lb) as lb' eqn:Hlb'.
remember (c :: lc) as lc' eqn:Hlc'.
remember (length (lap_add la' lb') + length lc' - 1) as labc.
remember (length la' + length lc' - 1) as lac.
remember (length lb' + length lc' - 1) as lbc.
rewrite Heqlabc.
remember (lap_add la' lb') as lab.
symmetry in Heqlab.
destruct lab as [| ab]; [ now subst la' lb' | ].
rewrite <- Heqlab in Heqlabc |-*.
rewrite (lap_convol_mul_more Hos) with (n := (lac + lbc)%nat). 2: {
  subst; flia.
}
rewrite <- Heqlabc.
symmetry.
rewrite Heqlab.
rewrite <- lap_add_norm_idemp_l.
rewrite (lap_convol_mul_more Hos (labc + lbc)); [ | now subst lac ].
rewrite <- Heqlab.
rewrite lap_add_norm_idemp_l.
rewrite lap_add_comm.
rewrite <- lap_add_norm_idemp_l.
rewrite Heqlbc.
rewrite (lap_convol_mul_more Hos) with (n := (labc + lac)%nat); [ | flia ].
rewrite lap_add_norm_idemp_l.
rewrite <- Heqlbc.
rewrite Nat.add_comm.
rewrite lap_add_comm.
rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_comm, Nat.add_assoc.
symmetry.
rewrite lap_convol_mul_lap_add_l.
now rewrite lap_add_lap_convol_mul_l.
Qed.

Theorem lap_mul_add_distr_r :
  rngl_has_opp_or_psub T = true →
  ∀ la lb lc, ((la + lb) * lc)%lap = (la * lc + lb * lc)%lap.
Proof.
intros Hos la lb lc.
apply eq_lap_norm_eq_length. 2: {
  destruct la as [| a]. {
    rewrite lap_mul_0_l.
    now do 2 rewrite lap_add_0_l.
  }
  destruct lb as [| b]. {
    rewrite lap_mul_0_l.
    now do 2 rewrite lap_add_0_r.
  }
  cbn.
  destruct lc as [| c]; [ easy | ].
  cbn; do 3 rewrite Nat.sub_0_r.
  do 3 (rewrite Nat.add_succ_r; cbn); f_equal.
  rewrite lap_convol_mul_length.
  do 2 rewrite List_length_map2.
  do 4 rewrite List.length_app, List.repeat_length.
  do 2 rewrite lap_convol_mul_length.
  do 2 rewrite min_add_sub_max.
  now rewrite Nat.add_max_distr_r.
}
apply (lap_norm_mul_add_distr_r Hos).
Qed.

Theorem lap_opt_mul_add_distr_r :
  rngl_has_opp_or_psub T = true →
  if rngl_mul_is_comm T then not_applicable
  else ∀ a b c, ((a + b) * c)%lap = (a * c + b * c)%lap.
Proof.
intros Hos.
destruct rngl_mul_is_comm; [ easy | ].
apply (lap_mul_add_distr_r Hos).
Qed.

(* *)

Theorem lap_polyn_integral :
  let rol := lap_ring_like_op in
  ∀ la lb : list T,
  (la * lb)%L = 0%L
  → la = 0%L ∨ lb = 0%L ∨ rngl_is_zero_divisor la ∨ rngl_is_zero_divisor lb.
Proof.
intros * Hab.
now right; right; left.
Qed.

(* *)

Theorem lap_characteristic_prop :
  let rol := lap_ring_like_op in
  if rngl_has_1 (list T) then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_1 (list T)) as onl eqn:Honl; symmetry in Honl.
destruct onl; [ | easy ].
assert (Hon : rngl_has_1 T = true). {
  progress unfold rngl_has_1 in Honl |-*.
  progress unfold rol in Honl; cbn in Honl.
  progress unfold lap_opt_one in Honl.
  now destruct (rngl_opt_one T).
}
specialize rngl_opt_characteristic_prop as H1.
intros i.
remember (S i) as j eqn:Hj.
rewrite Hon in H1.
progress unfold rol.
progress unfold lap_ring_like_op.
progress unfold lap_opt_one.
progress unfold rngl_has_1 in Hon.
progress unfold rngl_has_1 in Honl; cbn in Honl.
progress unfold lap_opt_one in Honl.
rewrite if_bool_if_dec in H1.
destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
  apply Nat.eqb_eq in Hcz.
  intros.
  specialize (H1 i) as H2.
  rewrite <- Hj in H2.
  destruct (rngl_opt_one T) as [one| ]; [ | easy ].
  intros H3; apply H2; clear H2.
  destruct j; [ easy | ].
  remember [one] as x; cbn in H3; subst x.
  unfold lap_add in H3.
  cbn - [ List_map2 "-" ] in H3.
  apply List_eq_map2_nil in H3.
  destruct H3 as [H3| H3]; [ easy | ].
  apply List.app_eq_nil in H3.
  destruct H3 as (H2, H3).
  now rewrite H2 in H3.
}
destruct H1 as (H1, H2).
destruct (rngl_opt_one T); [ | easy ].
subst j; cbn.
now destruct (List.fold_right lap_add [] (List.repeat [t] i)).
Qed.

(* lap ring-like properties *)

Definition lap_ring_like_prop (Hos : rngl_has_opp_or_psub T = true) :
    ring_like_prop (list T) :=
  let rol := lap_ring_like_op in
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := 0;
     rngl_add_comm := lap_add_comm;
     rngl_add_assoc := lap_add_assoc;
     rngl_add_0_l := lap_add_0_l;
     rngl_mul_assoc := lap_mul_assoc Hos;
     rngl_opt_mul_1_l := lap_opt_mul_1_l Hos;
     rngl_mul_add_distr_l := lap_mul_add_distr_l Hos;
     rngl_opt_mul_comm := lap_opt_mul_comm;
     rngl_opt_mul_1_r := lap_opt_mul_1_r Hos;
     rngl_opt_mul_add_distr_r := lap_opt_mul_add_distr_r Hos;
     rngl_opt_add_opp_diag_l := NA;
     rngl_opt_add_sub := NA;
     rngl_opt_sub_add_distr := NA;
     rngl_opt_sub_0_l := NA;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := NA;
     rngl_opt_integral := lap_polyn_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := lap_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

End a.
