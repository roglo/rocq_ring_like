(** * Polynomial_algebra

This module defines a ring-like algebra over polynomials represented by
lists whose leading coefficient is non-zero. For example, the polynomial
[ax² + bx + c] is represented as the list [[c; b; a]] together with the
proof that [a≠0].

This module uses a version with lists [[RingLike.Lap_algebra]]
where the leading coefficient is not constrained.

See the module [[RingLike.Core]] for the general description
of the ring-like library.

Usage:
<<
    Require Import RingLike.Polynomial_algebra.
>>
*)

Set Nested Proofs Allowed.

Require Import Stdlib.Arith.Arith.
Import List.ListNotations Init.Nat.

Require Import Utf8 Core Misc Utils IterAdd Lap_algebra.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Theorem strip_0s_idemp : ∀ la, strip_0s (strip_0s la) = strip_0s la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
now rewrite Haz.
Qed.

Definition lap_psub la lb :=
  List_map2 rngl_psub
    (la ++ List.repeat 0%L (length lb - length la))
    (lb ++ List.repeat 0%L (length la - length lb)).

Definition lap_opp la := List.map rngl_opp la.

Definition lap_sub la lb :=
  if rngl_has_opp T then lap_add la (lap_opp lb)
  else if rngl_has_psub T then lap_psub la lb
  else List.repeat 0%L (max (length la) (length lb)).

Theorem fold_lap_psub :
  ∀ la lb,
  List_map2 rngl_psub (la ++ List.repeat 0%L (length lb - length la))
    (lb ++ List.repeat 0%L (length la - length lb)) =
  lap_psub la lb.
Proof. easy. Qed.

Theorem fold_lap_opp : ∀ la, List.map rngl_opp la = lap_opp la.
Proof. easy. Qed.

Theorem fold_lap_norm : ∀ la, List.rev (strip_0s (List.rev la)) = lap_norm la.
Proof. easy. Qed.

(* euclidean division *)

Definition rlap_pdiv_rem_nb_iter (la lb : list T) :=
  S (length la).

Definition rlap_pdiv_rem_step (rla rlb : list T) :=
  match rlb with
  | [] => (None, []) (* division by zero *)
  | b :: rlb' =>
      match rla with
      | [] => (None, [])
      | a :: rla' =>
          if length rla' <? length rlb' then (None, rla)
          else
            let cq := (a / b)%L in
            let rlr := lap_sub rla' (List.map (λ cb, (cb * cq)%L) rlb') in
            (Some cq, rlr)
      end
  end.

Fixpoint rlap_pdiv_rem_loop it (rla rlb : list T) : list T * list T :=
  match it with
  | 0 => ([], [rngl_of_nat 97]) (* algo err: not enough iterations *)
  | S it' =>
      let (q, rlr) := rlap_pdiv_rem_step rla rlb in
      match q with
      | Some cq =>
           let (rlq', rlr') := rlap_pdiv_rem_loop it' rlr rlb in
           (cq :: rlq', rlr')
      | None => ([], rlr)
      end
  end.

Definition rlap_pdiv_rem rla rlb :=
  rlap_pdiv_rem_loop (rlap_pdiv_rem_nb_iter rla rlb) rla rlb.

Definition lap_pdiv_rem la lb :=
  let (rlq, rlr) := rlap_pdiv_rem (List.rev la) (List.rev lb) in
  (List.rev rlq, List.rev (strip_0s rlr)).

Definition lap_pdiv la lb :=
  let (rlq, rlr) := rlap_pdiv_rem (List.rev la) (List.rev lb) in
  List.rev rlq.

Definition lap_rem la lb :=
  let (rlq, rlr) := rlap_pdiv_rem (List.rev la) (List.rev lb) in
  List.rev (strip_0s rlr).

End a.

Arguments lap_psub {T ro} (la lb)%_lap.

Notation "- a" := (lap_opp a) : lap_scope.
Notation "a - b" := (lap_sub a b) : lap_scope.
Notation "a / b" := (lap_pdiv a b) : lap_scope.
Notation "a 'mod' b" := (lap_rem a b) : lap_scope.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hos : rngl_has_opp_or_psub T = true).
Context (Hed : rngl_has_eq_dec T = true).

Theorem List_map2_rngl_psub_0_r :
  rngl_has_psub T = true →
  ∀ n la,
  n = length la
  → List_map2 rngl_psub la (List.repeat 0%L n) = la.
Proof.
intros Hsu * Hn; subst n.
induction la as [| la]; [ easy | cbn ].
now rewrite (rngl_psub_0_r Hsu); f_equal.
Qed.

Theorem lap_psub_0_r :
  rngl_has_psub T = true →
  ∀ la, lap_psub la 0 = la.
Proof.
intros Hsu *.
unfold lap_psub.
rewrite Nat.sub_0_r; cbn.
rewrite List.app_nil_r.
now apply (List_map2_rngl_psub_0_r Hsu).
Qed.

(* *)

Theorem strip_0s_length_le : ∀ l, length (strip_0s l) ≤ length l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
destruct (a =? 0)%L; cbn; [ | easy ].
flia IHl.
Qed.

Theorem lap_psub_length : ∀ la lb,
  length (lap_psub la lb) = max (length la) (length lb).
Proof.
intros.
unfold lap_psub.
rewrite List_length_map2.
do 2 rewrite List.length_app, List.repeat_length.
apply min_add_sub_max.
Qed.

Theorem lap_opp_length : ∀ la, length (- la)%lap = length la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
f_equal; apply IHla.
Qed.

Theorem lap_sub_length : ∀ la lb,
  length (la - lb)%lap = max (length la) (length lb).
Proof.
intros.
unfold lap_sub.
destruct rngl_has_opp; [ now rewrite lap_add_length, lap_opp_length | ].
destruct rngl_has_psub; [ now rewrite lap_psub_length | ].
now rewrite List.repeat_length.
Qed.

(* *)

Theorem rlap_pdiv_rem_step_None : ∀ la lb lr,
  rlap_pdiv_rem_step la lb = (None, lr)
  → lb = [] ∧ lr = [] ∨ la = [] ∧ lr = [] ∨ length la < length lb ∧ lr = la.
Proof.
intros * Hrl.
destruct lb as [| b]. {
  injection Hrl; clear Hrl; intros; subst.
  now left.
}
destruct la as [| a]. {
  injection Hrl; clear Hrl; intros; subst.
  now right; left.
}
cbn - [ "<?" ] in Hrl |-*; right; right.
rewrite if_ltb_lt_dec in Hrl.
destruct (lt_dec _ _) as [Hab| Hab]; [ | easy ].
injection Hrl; clear Hrl; intros; subst lr.
split; [ | easy ].
now apply Nat.succ_lt_mono in Hab.
Qed.

Theorem rlap_pdiv_rem_step_length_r_a : ∀ rla rlb rlr cq,
  rlap_pdiv_rem_step rla rlb = (Some cq, rlr)
  → S (length rlr) = length rla.
Proof.
intros * Hrab.
unfold rlap_pdiv_rem_step in Hrab.
destruct rlb as [| b]; [ easy | ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrab.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrab; clear Hrab; intros; subst cq rlr.
rewrite lap_sub_length, List.length_map.
now rewrite max_l.
Qed.

Theorem rlap_rem_loop_prop : ∀ it rla rlb rlq rlr,
  rlb ≠ []
  → rlap_pdiv_rem_loop it rla rlb = (rlq, rlr)
  → S (length rla) ≤ it
  → length rlr < length rlb.
Proof.
intros * Hbz Hqr Hit.
revert rla rlq rlr Hqr Hit.
induction it; intros; [ easy | ].
cbn in Hqr.
remember (rlap_pdiv_rem_step rla rlb) as qr eqn:Hqr'; symmetry in Hqr'.
destruct qr as (q, rlr').
destruct q as [cq| ]. 2: {
  injection Hqr; clear Hqr; intros; subst rlq rlr'.
  apply rlap_pdiv_rem_step_None in Hqr'.
  destruct Hqr' as [(H1, H2)| Hqr]; [ easy | ].
  destruct Hqr as [(H1, H2)| Hqr]. {
    subst rla rlr.
    destruct rlb; [ easy | ].
    cbn; easy.
  }
  now destruct Hqr as (H1, H2); subst rlr.
}
remember (rlap_pdiv_rem_loop it rlr' rlb) as qr eqn:Hqr''.
symmetry in Hqr''.
destruct qr as (rlq', rlr'').
injection Hqr; clear Hqr; intros; subst rlq rlr''.
apply IHit in Hqr''; [ easy | ].
apply rlap_pdiv_rem_step_length_r_a in Hqr'.
rewrite Hqr'.
now apply Nat.succ_le_mono in Hit.
Qed.

Theorem lap_mul_length : ∀ la lb,
  length (la * lb)%lap =
    match length la with
    | 0 => 0
    | S a =>
        match length lb with
        | 0 => 0
        | S b => S (a + b)
        end
    end.
Proof.
intros.
unfold lap_mul.
destruct la; [ easy | ].
destruct lb; [ easy | ].
rewrite lap_convol_mul_length; cbn.
now rewrite Nat.add_succ_r, Nat.sub_0_r.
Qed.

Theorem lap_norm_List_map2_app_app_idemp_r :
  ∀ f, (∀ a, f a 0%L = a) →
  ∀ la lb,
  lap_norm
    (List_map2 f (la ++ List.repeat 0%L (length (lap_norm lb) - length la))
       (lap_norm lb ++ List.repeat 0%L (length la - length (lap_norm lb)))) =
  lap_norm
    (List_map2 f (la ++ List.repeat 0%L (length lb - length la))
       (lb ++ List.repeat 0%L (length la - length lb))).
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hf *.
unfold lap_norm; f_equal.
revert lb.
induction la as [| a]; intros. {
  cbn.
  do 2 rewrite List.app_nil_r, Nat.sub_0_r.
  rewrite List.length_rev.
  rewrite fold_lap_norm.
  rewrite List_rev_map2. 2: {
    unfold lap_norm.
    now rewrite List.repeat_length, List.length_rev.
  }
  rewrite List_rev_map2; [ | apply List.repeat_length ].
  do 2 rewrite List.rev_repeat.
  unfold lap_norm.
  rewrite List.rev_involutive.
  rewrite <- (List.length_rev lb).
  remember (List.rev lb) as la eqn:Hla.
  clear lb Hla.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Heo) in Haz; subst a.
  rewrite Hf.
  rewrite (rngl_eqb_refl Heo).
  apply IHla.
}
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite strip_0s_app; cbn.
rewrite <- IHla.
remember (strip_0s (List.rev lb)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hbz| Hbz]. {
    cbn.
    apply (rngl_eqb_eq Heo) in Hbz.
    subst b; cbn.
    rewrite List.app_nil_r, Hf, Nat.sub_0_r.
    rewrite List_rev_map2; [ | symmetry; apply List.repeat_length ].
    rewrite List.rev_repeat.
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

Theorem lap_psub_norm_idemp_l :
  rngl_has_psub T = true →
  ∀ la lb,
  lap_norm (lap_psub (lap_norm la) lb) = lap_norm (lap_psub la lb).
Proof.
intros Hsu.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
apply (lap_norm_List_map2_app_app_idemp_l Heo).
apply (rngl_psub_0_r Hsu).
Qed.

Theorem lap_psub_norm_idemp_r :
  rngl_has_psub T = true →
  ∀ la lb,
  lap_norm (lap_psub la (lap_norm lb)) = lap_norm (lap_psub la lb).
Proof.
intros Hsu *.
apply lap_norm_List_map2_app_app_idemp_r.
apply (rngl_psub_0_r Hsu).
Qed.

(* *)

Theorem lap_mul_1_l :
  ∀ la, (1 * la)%lap = la.
Proof.
intros *.
unfold lap_one.
rewrite (lap_mul_const_l Hos).
induction la as [| a]; [ easy | cbn ].
rewrite rngl_mul_1_l; f_equal.
apply IHla.
Qed.

Theorem lap_mul_1_r :
  ∀ la, (la * 1)%lap = la.
Proof.
intros *.
unfold lap_one.
rewrite (lap_mul_const_r Hos).
induction la as [| a]; [ easy | cbn ].
rewrite rngl_mul_1_r; f_equal.
apply IHla.
Qed.

(* *)

Theorem last_lap_convol_mul_last :
  ∀ la lb a b i len d,
  len ≠ 0
  → length la + length lb + 1 = i + len
  → List.last (lap_convol_mul (la ++ [a]) (lb ++ [b]) i len) d = (a * b)%L.
Proof.
intros * Hlen Hlab.
revert la lb i Hlab.
induction len; intros; [ easy | clear Hlen ].
cbn.
destruct len. {
  cbn.
  rewrite rngl_summation_split3 with (j := length la); [ | flia Hlab ].
  rewrite List.app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  replace (i - length la) with (length lb) by flia Hlab.
  rewrite List.app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn.
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite (List.nth_overflow (lb ++ [b])). 2: {
      rewrite List.length_app; cbn; flia Hlab Hj.
    }
    apply (rngl_mul_0_r Hos).
  }
  rewrite rngl_add_0_l.
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite (List.nth_overflow (la ++ [a])). 2: {
      now rewrite List.length_app.
    }
    apply (rngl_mul_0_l Hos).
  }
  apply rngl_add_0_r.
}
rewrite IHlen; [ easy | easy | flia Hlab ].
Qed.

Theorem last_lap_mul :
  ∀ la lb, List.last (la * lb)%lap 0%L = (List.last la 0 * List.last lb 0)%L.
Proof.
intros.
unfold lap_mul.
destruct la as [| a] using List.rev_ind. {
  now symmetry; apply (rngl_mul_0_l Hos).
}
clear IHla.
destruct lb as [| b] using List.rev_ind. {
  cbn.
  rewrite rngl_mul_0_r; [ | easy ].
  now destruct (la ++ [a]).
}
clear IHlb.
move b before a.
remember (la ++ [a]) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]; [ now apply List.app_eq_nil in Hlc | ].
remember (lb ++ [b]) as ld eqn:Hld.
symmetry in Hld.
destruct ld as [| d]; [ now apply List.app_eq_nil in Hld | ].
rewrite <- Hlc, <- Hld.
clear c d lc ld Hlc Hld.
do 2 rewrite List.last_last.
do 2 rewrite List.length_app.
cbn.
apply (last_lap_convol_mul_last); flia.
Qed.

(* *)

Theorem List_map2_rngl_psub_diag :
  ∀ la, List_map2 rngl_psub la la = List.repeat 0%L (length la).
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
f_equal; [ | apply IHla ].
now apply rngl_psub_diag.
Qed.

Theorem lap_opt_add_sub :
  rngl_has_psub T = true →
  ∀ la lb : list T,
  (la + lb - lb)%lap = la ++ List.repeat 0%L (length lb - length la).
Proof.
intros Hsu *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_psub in Hsu.
  destruct rngl_opt_opp_or_psub; [ now destruct s | easy ].
}
move Hop after Hsu.
unfold lap_sub.
rewrite Hop, Hsu.
unfold lap_add, lap_psub.
rewrite List_length_map2.
do 2 rewrite List.length_app, List.repeat_length.
rewrite min_add_sub_max.
rewrite <- Nat.sub_min_distr_l.
rewrite Nat.sub_diag, Nat.min_0_r.
rewrite <- Nat.sub_max_distr_r.
rewrite Nat.sub_diag, Nat.max_0_r.
destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  do 2 rewrite List.app_nil_r.
  revert lb Hab.
  induction la as [| a]; intros; cbn. {
    rewrite Nat.sub_0_r.
    rewrite List_map2_rngl_add_0_l.
    now apply List_map2_rngl_psub_diag.
  }
  destruct lb as [| b]; [ easy | cbn ].
  cbn in Hab.
  apply Nat.succ_le_mono in Hab.
  f_equal; [ | now apply IHla ].
  specialize (rngl_add_sub Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab.
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  do 2 rewrite List.app_nil_r.
  revert lb Hab.
  induction la as [| a]; intros; [ easy | cbn ].
  destruct lb as [| b]; cbn. {
    rewrite rngl_add_0_r.
    rewrite (rngl_psub_0_r Hsu); f_equal.
    rewrite List_map2_rngl_add_0_r.
    now apply (List_map2_rngl_psub_0_r Hsu).
  }
  cbn in Hab.
  apply Nat.succ_le_mono in Hab.
  f_equal; [ | now apply IHla ].
  specialize (rngl_add_sub Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
}
Qed.

Theorem lap_psub_add_distr :
  rngl_has_psub T = true →
  ∀ la lb lc, lap_psub la (lb + lc) = lap_psub (lap_psub la lb) lc.
Proof.
intros Hsu *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_psub in Hsu.
  destruct rngl_opt_opp_or_psub; [ now destruct s | easy ].
}
move Hop after Hsu.
unfold lap_psub, lap_add.
do 2 rewrite List_length_map2.
do 4 rewrite List.length_app, List.repeat_length.
do 2 rewrite <- Nat.sub_min_distr_r.
destruct (le_dec (length lb) (length lc)) as [Hbc| Hbc]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
  rewrite List.app_nil_r, Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite Nat.min_id.
  destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
    rewrite (proj2 (Nat.sub_0_le _ _) Hab).
    rewrite List.app_nil_r, Nat.add_0_r.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    do 2 rewrite Nat.min_id.
    rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
    assert (Hac : length la ≤ length lc) by now transitivity (length lb).
    rewrite (proj2 (Nat.sub_0_le _ _) Hac).
    do 2 rewrite List.app_nil_r.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite (Nat.add_sub_assoc (length la)); [ | easy ].
    rewrite (Nat.add_comm (length la)), Nat.add_sub, Nat.min_id.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    apply List_map2_ext_in.
    intros (i, j) Hi; cbn.
    assert (H : i = j) by now apply List_in_combine_same in Hi.
    subst j.
    apply List.in_combine_l in Hi.
    apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
    do 2 rewrite List_nth_app_repeat_r.
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      rewrite List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite List_nth_app_repeat_r.
    destruct (lt_dec i (length lb)) as [Hilb| Hilb]. {
      rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
        rewrite List.length_app, List.repeat_length.
        rewrite Nat.add_sub_assoc; [ | easy ].
        now rewrite Nat.add_comm, Nat.add_sub.
      }
      rewrite List_nth_app_repeat_r.
      specialize (rngl_sub_add_distr Hos) as H1.
      unfold rngl_sub in H1.
      rewrite Hop, Hsu in H1.
      apply H1.
    }
    apply Nat.nlt_ge in Hilb.
    assert (Hila : length la ≤ i) by now transitivity (length lb).
    rewrite List.nth_overflow; [ | easy ].
    rewrite List.nth_overflow; [ | easy ].
    rewrite rngl_add_0_l.
    rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
      rewrite List_length_map2, List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    }
    easy.
  }
  apply Nat.nle_gt in Hab.
  apply Nat.lt_le_incl in Hab.
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite List.app_nil_r, Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite Nat.min_id.
  destruct (le_dec (length la) (length lc)) as [Hac| Hac]. {
    rewrite (proj2 (Nat.sub_0_le _ _) Hac).
    do 2 rewrite List.app_nil_r.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    rewrite (List_map2_map2_seq_r 0%L).
    rewrite (List_map2_map2_seq_l 0%L).
    rewrite List.length_app, List.repeat_length.
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
    rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
    rewrite Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.add_comm, Nat.add_sub.
    symmetry.
    apply List_map2_ext_in.
    intros (i, j) Hi; cbn.
    assert (H : i = j) by now apply List_in_combine_same in Hi.
    subst j.
    apply List.in_combine_l in Hi.
    apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
    do 2 rewrite List_nth_app_repeat_r.
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      rewrite List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite List_nth_app_repeat_r.
    destruct (lt_dec i (length la)) as [Hila| Hila]. {
      rewrite (List_map2_nth 0%L 0%L); [ | easy | ]. 2: {
        rewrite List.length_app, List.repeat_length.
        rewrite Nat.add_sub_assoc; [ | easy ].
        now rewrite Nat.add_comm, Nat.add_sub.
      }
      rewrite List_nth_app_repeat_r.
      specialize (rngl_sub_add_distr Hos) as H1.
      unfold rngl_sub in H1.
      rewrite Hop, Hsu in H1.
      apply H1.
    }
    apply Nat.nlt_ge in Hila.
    assert (Hilb : length lb ≤ i) by now transitivity (length la).
    rewrite List.nth_overflow; [ | easy ].
    rewrite List.nth_overflow; [ | easy ].
    rewrite rngl_add_0_l.
    rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
      rewrite List_length_map2, List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
    }
    easy.
  }
  apply Nat.nle_gt in Hac.
  apply Nat.lt_le_incl in Hac.
  rewrite (proj2 (Nat.sub_0_le _ _) Hac).
  do 2 rewrite List.app_nil_r.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite List.length_app, List_length_map2, List.length_app.
  do 2 rewrite List.repeat_length.
  rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
  rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite List.length_app, List.repeat_length.
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
  rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  apply List_map2_ext_in.
  intros (i, j) Hi; cbn.
  assert (H : i = j) by now apply List_in_combine_same in Hi.
  subst j.
  apply List.in_combine_l in Hi.
  apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
  do 2 rewrite List_nth_app_repeat_r.
  rewrite (List_map2_nth 0%L 0%L _ _ la); [ | easy | ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  destruct (lt_dec i (length lc)) as [Hilc| Hilc]. {
    rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
      rewrite List.length_app, List.repeat_length.
      rewrite Nat.add_sub_assoc; [ | easy ].
      now rewrite Nat.add_comm, Nat.add_sub.
    }
    rewrite List_nth_app_repeat_r.
    specialize (rngl_sub_add_distr Hos) as H1.
    unfold rngl_sub in H1.
    rewrite Hop, Hsu in H1.
    apply H1.
  }
  apply Nat.nlt_ge in Hilc.
  assert (Hilb : length lb ≤ i) by now transitivity (length lc).
  rewrite (List.nth_overflow lc); [ | easy ].
  rewrite (List.nth_overflow lb); [ | easy ].
  do 2 rewrite (rngl_psub_0_r Hsu).
  rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
    rewrite List_length_map2, List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
  }
  rewrite (rngl_psub_0_r Hsu).
  easy.
}
apply Nat.nle_gt in Hbc.
apply Nat.lt_le_incl in Hbc.
rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
rewrite List.app_nil_r, Nat.add_0_r.
rewrite Nat.add_sub_assoc; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
do 2 rewrite Nat.min_id.
destruct (le_dec (length la) (length lb)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _) Hab).
  rewrite List.app_nil_r, Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  do 2 rewrite Nat.min_id.
  rewrite (proj2 (Nat.sub_0_le _ _) Hbc).
  do 2 rewrite List.app_nil_r.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  rewrite (List_map2_map2_seq_r 0%L).
  rewrite (List_map2_map2_seq_l 0%L).
  rewrite List.length_app, List.repeat_length.
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite (Nat.add_sub_assoc (length la)); [ | easy ].
  rewrite (Nat.add_comm (length la)), Nat.add_sub, Nat.min_id.
  rewrite (Nat.add_sub_assoc (length lc)); [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  symmetry.
  apply List_map2_ext_in.
  intros (i, j) Hi; cbn.
  assert (H : i = j) by now apply List_in_combine_same in Hi.
  subst j.
  apply List.in_combine_l in Hi.
  apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
  do 2 rewrite List_nth_app_repeat_r.
  rewrite (List_map2_nth 0%L 0%L); [ | easy | ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  rewrite (List_map2_nth 0%L 0%L); [ | | easy ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  specialize (rngl_sub_add_distr Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
}
apply Nat.nle_gt in Hab.
apply Nat.lt_le_incl in Hab.
assert (Hca : length lc ≤ length la) by now transitivity (length lb).
rewrite (proj2 (Nat.sub_0_le _ _) Hab).
rewrite List.app_nil_r, Nat.add_0_r.
rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
rewrite (proj2 (Nat.sub_0_le _ _) Hca).
rewrite List.app_nil_r, Nat.min_id.
rewrite (List_map2_map2_seq_l 0%L).
rewrite (List_map2_map2_seq_r 0%L).
rewrite List.length_app, List.repeat_length.
rewrite List_length_map2.
rewrite List.length_app, List.repeat_length.
rewrite (Nat.add_sub_assoc (length lc)); [ | easy ].
rewrite (Nat.add_comm (length lc)), Nat.add_sub, Nat.min_id.
rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
rewrite (Nat.add_comm (length lb)), Nat.add_sub.
symmetry.
rewrite (List_map2_map2_seq_r 0%L).
rewrite (List_map2_map2_seq_l 0%L).
rewrite List.length_app, List.repeat_length.
rewrite List_length_map2, List.length_app, List.repeat_length.
rewrite (Nat.add_sub_assoc (length lb)); [ | easy ].
rewrite (Nat.add_comm (length lb)), Nat.add_sub, Nat.min_id.
rewrite Nat.add_sub_assoc; [ | easy ].
rewrite Nat.add_comm, Nat.add_sub.
symmetry.
apply List_map2_ext_in.
intros (i, j) Hi; cbn.
assert (H : i = j) by now apply List_in_combine_same in Hi.
subst j.
apply List.in_combine_l in Hi.
apply List.in_seq in Hi; destruct Hi as (_, Hi); cbn in Hi.
do 2 rewrite List_nth_app_repeat_r.
rewrite (List_map2_nth 0%L 0%L _ _ la); [ | easy | ]. 2: {
  rewrite List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  now rewrite Nat.add_comm, Nat.add_sub.
}
rewrite List_nth_app_repeat_r.
destruct (lt_dec i (length lb)) as [Hilb| Hilb]. {
  rewrite (List_map2_nth 0%L 0%L); [ | easy | ]. 2: {
    rewrite List.length_app, List.repeat_length.
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite List_nth_app_repeat_r.
  specialize (rngl_sub_add_distr Hos) as H1.
  unfold rngl_sub in H1.
  rewrite Hop, Hsu in H1.
  apply H1.
}
apply Nat.nlt_ge in Hilb.
assert (Hilc : length lc ≤ i) by now transitivity (length lb).
rewrite (List.nth_overflow lc); [ | easy ].
rewrite (List.nth_overflow lb); [ | easy ].
do 2 rewrite (rngl_psub_0_r Hsu).
rewrite (List.nth_overflow (List_map2 _ _ _)). 2: {
  rewrite List_length_map2, List.length_app, List.repeat_length.
  rewrite Nat.add_sub_assoc; [ | easy ].
  now rewrite Nat.add_comm, Nat.add_sub, Nat.min_id.
}
rewrite (rngl_psub_0_r Hsu).
easy.
Qed.

Theorem lap_opt_sub_add_distr :
  rngl_has_psub T = true →
  ∀ la lb lc : list T, (la - (lb + lc))%lap = (la - lb - lc)%lap.
Proof.
intros Hsu *.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  move Hsu at bottom.
  unfold rngl_has_opp in Hop.
  unfold rngl_has_psub in Hsu.
  destruct rngl_opt_opp_or_psub; [ now destruct s | easy ].
}
move Hop after Hsu.
unfold lap_sub.
rewrite Hop, Hsu.
apply (lap_psub_add_distr Hsu).
Qed.

(* *)

Theorem lap_mul_opp_r :
  rngl_has_opp T = true →
  ∀ la lb, (la * - lb = - (la * lb))%lap.
Proof.
intros Hop *.
unfold lap_opp, lap_mul.
destruct la as [| a]; [ easy | cbn ].
destruct lb as [| b]; [ easy | cbn ].
do 2 rewrite Nat.sub_0_r.
rewrite List.length_map.
remember 0 as i in |-*; clear Heqi.
remember (length la + S (length lb)) as len; clear Heqlen.
revert i.
induction len; intros; [ easy | cbn ].
f_equal; [ | apply IHlen ].
rewrite (rngl_opp_summation Hop).
apply rngl_summation_eq_compat.
intros j Hj.
destruct j. {
  rewrite Nat.sub_0_r.
  rewrite <- (rngl_mul_opp_r Hop); f_equal.
  destruct i; [ easy | cbn ].
  destruct (lt_dec i (length lb)) as [Hilb| Hilb]. 2: {
    apply Nat.nlt_ge in Hilb.
    rewrite List.nth_overflow; [ | now rewrite List.length_map ].
    rewrite List.nth_overflow; [ | easy ].
    symmetry; apply (rngl_opp_0 Hop).
  }
  now rewrite (List_map_nth' 0%L).
}
rewrite <- (rngl_mul_opp_r Hop); f_equal.
destruct (i - S j) as [| k]; [ easy | ].
destruct (lt_dec k (length lb)) as [Hklb| Hklb]. 2: {
  apply Nat.nlt_ge in Hklb.
  rewrite List.nth_overflow; [ | now rewrite List.length_map ].
  rewrite List.nth_overflow; [ | easy ].
  symmetry; apply (rngl_opp_0 Hop).
}
now rewrite (List_map_nth' 0%L).
Qed.

Theorem lap_mul_sub_distr_l :
  rngl_has_opp T = true →
  ∀ la lb lc, (la * (lb - lc))%lap = (la * lb - la * lc)%lap.
Proof.
intros Hop.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
unfold lap_sub.
rewrite <- (lap_mul_opp_r Hop).
rewrite Hop.
apply (lap_mul_add_distr_l Heo Hos).
Qed.

(* *)

Definition is_empty_list {A} (la : list A) :=
  match la with [] => true | _ => false end.
Definition has_polyn_prop {T} {ro : ring_like_op T} (la : list T) :=
  (is_empty_list la || (List.last la 0 ≠? 0)%L)%bool.

Theorem rlap_rem_prop : ∀ rla rlb rlq rlr,
  rlb ≠ []
  → rlap_pdiv_rem rla rlb = (rlq, rlr)
  → List.length rlr < List.length rlb.
Proof.
intros * Hbz Hqr.
unfold rlap_pdiv_rem in Hqr.
remember (rlap_pdiv_rem_nb_iter rla rlb) as it eqn:Hit.
unfold rlap_pdiv_rem_nb_iter in Hit.
assert (H : S (List.length rla) ≤ it) by flia Hit.
now apply rlap_rem_loop_prop in Hqr.
Qed.

Theorem lap_rem_length_lt :
  ∀ la lb lq lr : list T,
  lb ≠ []
  → has_polyn_prop lb = true
  → lap_pdiv_rem la lb = (lq, lr)
  → List.length lr < List.length lb.
Proof.
intros * Hbz Hbn Hab.
unfold lap_pdiv_rem in Hab.
remember (rlap_pdiv_rem (List.rev la) (List.rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr).
injection Hab; clear Hab; intros; subst lq lr.
apply rlap_rem_prop in Hqr. 2: {
  now intros H; apply List_eq_rev_nil in H.
}
rewrite List.length_rev in Hqr |-*.
eapply Nat.le_lt_trans; [ | apply Hqr ].
apply strip_0s_length_le.
Qed.

Theorem is_empty_list_empty : ∀ A (la : list A),
  is_empty_list la = true → la = [].
Proof.
intros * Ha.
unfold is_empty_list in Ha.
now destruct la.
Qed.

Theorem rlap_pdiv_prop :
  rngl_has_inv T = true →
  ∀ la lb lq lr,
  la = [] ∨ List.hd 0%L la ≠ 0%L
  → lb = [] ∨ List.hd 0%L lb ≠ 0%L
  → rlap_pdiv_rem la lb = (lq, lr)
  → lq = [] ∨ List.hd 0%L lq ≠ 0%L.
Proof.
intros Hiv.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Ha Hb Hab.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  specialize (rngl_characteristic_1 Hos Hch) as H1.
  destruct lq as [| q]; [ now left | right; cbn ].
  destruct Hb as [Hb| Hb]; [ now subst lb | ].
  destruct lb as [| b]; [ easy | cbn in Hb ].
  now specialize (H1 b).
}
unfold rlap_pdiv_rem in Hab.
remember (rlap_pdiv_rem_nb_iter _ _) as it eqn:Hit.
symmetry in Hit.
assert (H : rlap_pdiv_rem_nb_iter la lb ≤ it) by flia Hit.
move H before Hit; clear Hit; rename H into Hit.
destruct it; [ easy | ].
cbn in Hab.
remember (rlap_pdiv_rem_step la lb) as orlr eqn:Hor; symmetry in Hor.
destruct orlr as (o, rlr).
destruct o as [cq| ]. 2: {
  injection Hab; clear Hab; intros; subst lq lr.
  now left.
}
destruct lb as [| b]; [ easy | ].
destruct la as [| a]; [ easy | cbn ].
destruct Ha as [Ha| Ha]; [ easy | ].
destruct Hb as [Hb| Hb]; [ easy | ].
cbn in Ha, Hb.
cbn - [ "<?" ] in Hor.
rewrite if_ltb_lt_dec in Hor.
destruct (lt_dec _ _) as [Halb| Halb]; [ easy | ].
apply Nat.nlt_ge in Halb.
symmetry in Hor.
injection Hor; clear Hor; intros Hrlr Hcq.
rewrite <- Hcq in Hrlr.
remember (rlap_pdiv_rem_loop it rlr (b :: lb)) as rb eqn:Hrb.
symmetry in Hrb.
destruct rb as (lq', lr').
symmetry in Hab.
injection Hab; clear Hab; intros H1 Hlq; subst lr'.
rewrite Hlq; cbn.
rewrite Hcq.
right.
unfold rngl_div.
rewrite Hiv.
intros Hq.
apply (rngl_eq_mul_0_l Hos Hiq) in Hq; [ easy | ].
now apply (rngl_inv_neq_0 Hos Hiv).
Qed.

Theorem lap_convol_mul_1_l :
  ∀ la i len,
  List.length la = i + len
  → lap_convol_mul [1%L] la i len = List.skipn i la.
Proof.
intros * Hlen.
rewrite (lap_convol_mul_const_l Hos); [ | easy ].
erewrite List.map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_l.
}
apply List.map_id.
Qed.

Theorem lap_convol_mul_l_succ_l :
  ∀ la lb i len,
  lap_convol_mul (0%L :: la) lb (S i) len =
  lap_convol_mul la lb i len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | cbn ].
rewrite rngl_summation_split_first; [ | easy ].
rewrite rngl_summation_shift with (s := 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
rewrite (rngl_mul_0_l Hos), rngl_add_0_l.
f_equal.
apply IHlen.
Qed.

Definition lap_x_power n := List.repeat 0%L n ++ [1%L].

Theorem lap_repeat_0_app_is_mul_power_l :
  ∀ n la,
  la ≠ []
  → List.repeat 0%L n ++ la = (lap_x_power n * la)%lap.
Proof.
intros * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite rngl_summation_only_one.
  rewrite rngl_mul_1_l; f_equal.
  now rewrite (lap_convol_mul_1_l).
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
rewrite List.length_app, List.repeat_length; cbn.
rewrite Nat.sub_0_r, Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
rewrite lap_convol_mul_l_succ_l.
rewrite IHn; [ | easy ].
destruct n; [ easy | cbn ].
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos).
rewrite Nat.sub_0_r.
rewrite List.length_app, List.repeat_length; cbn.
rewrite lap_convol_mul_l_succ_l.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_l Hos); f_equal.
apply lap_convol_mul_l_succ_l.
Qed.

Theorem lap_convol_mul_1_r :
  ∀ la i len,
  List.length la = i + len
  → lap_convol_mul la [1%L] i len = List.skipn i la.
Proof.
intros * Hlen.
rewrite (lap_convol_mul_const_r Hos); [ | easy ].
erewrite List.map_ext_in. 2: {
  intros a Ha.
  now rewrite rngl_mul_1_r.
}
apply List.map_id.
Qed.

Theorem lap_convol_mul_r_succ_l :
  ∀ la lb i len,
  lap_convol_mul la (0%L :: lb) (S i) len =
  lap_convol_mul la lb i len.
Proof.
intros.
revert la lb i.
induction len; intros; [ easy | cbn ].
rewrite rngl_summation_split_last; [ | easy ].
rewrite rngl_summation_shift with (s := 1); [ | flia ].
rewrite Nat.sub_diag, Nat_sub_succ_1.
rewrite Nat.sub_diag.
rewrite (rngl_mul_0_r Hos), rngl_add_0_r.
rewrite IHlen; f_equal.
apply rngl_summation_eq_compat.
intros j Hj.
rewrite Nat.add_comm, Nat.add_sub; f_equal.
destruct j; [ now rewrite Nat.sub_0_r | ].
now replace (i - j) with (S (i - S j)) by flia Hj.
Qed.

Theorem lap_repeat_0_app_is_mul_power_r :
  ∀ n la,
  la ≠ []
  → List.repeat 0%L n ++ la = (la * lap_x_power n)%lap.
Proof.
intros * Haz.
revert la Haz.
induction n; intros. {
  destruct la as [| a]; [ easy | clear Haz; cbn ].
  rewrite Nat.sub_0_r, Nat.add_1_r; cbn.
  rewrite rngl_summation_only_one.
  rewrite rngl_mul_1_r; f_equal.
  now rewrite (lap_convol_mul_1_r).
}
cbn.
destruct la as [| a]; [ easy | clear Haz ].
cbn.
rewrite List.length_app, List.repeat_length, Nat.sub_0_r; cbn.
rewrite Nat.add_succ_r; cbn.
rewrite rngl_summation_only_one.
rewrite (rngl_mul_0_r Hos); f_equal.
rewrite IHn; [ | easy ].
rewrite lap_convol_mul_r_succ_l.
cbn.
destruct n; cbn; [ now rewrite Nat.sub_0_r | ].
now rewrite List.length_app, List.repeat_length, Nat.sub_0_r.
Qed.

Theorem lap_add_repeat_0_l : ∀ la len,
  len ≤ List.length la
  → (List.repeat 0%L len + la = la)%lap.
Proof.
intros * Hlen.
revert len Hlen.
induction la as [| a]; intros. {
  now apply Nat.le_0_r in Hlen; subst len.
}
cbn.
destruct len. {
  cbn - [ lap_add ].
  now rewrite lap_add_0_l.
}
cbn.
cbn in Hlen; apply Nat.succ_le_mono in Hlen.
rewrite rngl_add_0_l; f_equal.
now apply IHla.
Qed.

Theorem lap_add_repeat_0_r : ∀ la len,
  len ≤ List.length la
  → (la + List.repeat 0%L len = la)%lap.
Proof.
intros * Hlen.
rewrite lap_add_comm.
now apply lap_add_repeat_0_l.
Qed.

Theorem lap_add_app_app :
  ∀ la lb lc ld,
  List.length la = List.length lb
  → ((la ++ lc) + (lb ++ ld))%lap = (la + lb)%lap ++ (lc + ld)%lap.
Proof.
intros * Hab.
revert lb lc ld Hab.
induction la as [| a]; intros. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | ].
cbn in Hab.
apply Nat.succ_inj in Hab.
cbn; f_equal.
now apply IHla.
Qed.

Theorem rev_lap_add : ∀ la lb,
  List.length la = List.length lb
  → (List.rev (la + lb) = List.rev la + List.rev lb)%lap.
Proof.
intros * Hab.
revert lb Hab.
induction la as [| a]; intros. {
  cbn - [ lap_add ].
  now do 2 rewrite lap_add_0_l.
}
cbn.
destruct lb as [| b]; [ easy | ].
cbn in Hab |-*.
apply Nat.succ_inj in Hab.
do 2 rewrite fold_lap_add.
rewrite IHla; [ | easy ].
rewrite lap_add_app_app; [ easy | ].
now do 2 rewrite List.length_rev.
Qed.

Theorem lap_add_norm : ∀ la lb,
  (la + lb)%lap =
    ((la ++ List.repeat 0%L (List.length lb - List.length la)) +
     (lb ++ List.repeat 0%L (List.length la - List.length lb)))%lap.
Proof.
intros.
revert lb.
induction la as [| a]; intros. {
  cbn; rewrite Nat.sub_0_r, List.app_nil_r.
  rewrite fold_lap_add.
  rewrite List_map2_rngl_add_0_l.
  now symmetry; apply lap_add_repeat_0_l.
}
cbn.
destruct lb as [| b]. {
  cbn; rewrite List.app_nil_r, rngl_add_0_r; f_equal.
  rewrite fold_lap_add.
  rewrite List_map2_rngl_add_0_r.
  now symmetry; apply lap_add_repeat_0_r.
}
cbn; f_equal.
apply IHla.
Qed.

Theorem rev_lap_add_norm : ∀ la lb,
  List.rev (la + lb)%lap =
    ((List.repeat 0%L (List.length lb - List.length la) ++ List.rev la) +
     (List.repeat 0%L (List.length la - List.length lb) ++ List.rev lb))%lap.
Proof.
intros.
rewrite <- (List.rev_repeat (List.length lb - _)).
rewrite <- (List.rev_repeat (List.length la - _)).
do 2 rewrite <- List.rev_app_distr.
rewrite lap_add_norm.
apply rev_lap_add.
do 2 rewrite List.length_app, List.repeat_length.
destruct (le_dec (List.length lb) (List.length la)) as [Hab| Hab]. {
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite Nat.add_0_r, Nat.add_comm; symmetry.
  now apply Nat.sub_add.
} {
  apply Nat.nle_gt, Nat.lt_le_incl in Hab; symmetry.
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite Nat.add_0_r, Nat.add_comm; symmetry.
  now apply Nat.sub_add.
}
Qed.

Theorem lap_opp_app_distr : ∀ la lb,
  (- (la ++ lb) = (- la) ++ (- lb))%lap.
Proof.
intros.
unfold lap_opp.
now rewrite List.map_app.
Qed.

Theorem rev_lap_opp : ∀ la, (List.rev (- la) = - List.rev la)%lap.
Proof.
intros.
unfold lap_opp.
now rewrite List.map_rev.
Qed.

Theorem map_opp_repeat : ∀ (x : T) n,
  List.map rngl_opp (List.repeat x n) = List.repeat (rngl_opp x) n.
Proof.
intros.
induction n; [ easy | cbn ].
f_equal; apply IHn.
Qed.

Theorem rev_lap_sub : ∀ la lb,
  List.length la = List.length lb
  → (List.rev (la - lb) = List.rev la - List.rev lb)%lap.
Proof.
intros * Hab.
unfold lap_sub.
destruct rngl_has_opp. {
  rewrite rev_lap_add; [ | now rewrite lap_opp_length ].
  now rewrite rev_lap_opp.
}
destruct rngl_has_psub. 2: {
  do 2 rewrite List.length_rev.
  now rewrite List.rev_repeat.
}
revert lb Hab.
induction la as [| a]; intros; cbn. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab.
do 2 rewrite fold_lap_psub.
rewrite IHla; [ | easy ].
clear IHla.
rewrite <- (List.length_rev la) in Hab.
rewrite <- (List.length_rev lb) in Hab.
remember (List.rev la) as lc.
remember (List.rev lb) as ld.
clear la lb Heqlc Heqld.
rename lc into la; rename ld into lb.
revert lb Hab.
induction la as [| a']; intros; cbn. {
  now symmetry in Hab; apply List.length_zero_iff_nil in Hab; subst lb.
}
destruct lb as [| b']; [ easy | cbn ].
cbn in Hab; apply Nat.succ_inj in Hab.
now f_equal; apply IHla.
Qed.

Theorem lap_add_app_l : ∀ la lb lc,
  List.length lc ≤ List.length la
  → (((la ++ lb) + lc) = (la + lc) ++ lb)%lap.
Proof.
intros * Hca.
revert lb lc Hca.
induction la as [| a]; intros; cbn. {
  apply Nat.le_0_r, List.length_zero_iff_nil in Hca; subst lc.
  cbn.
  rewrite List.app_nil_r, Nat.sub_0_r.
  apply List_map2_rngl_add_0_r.
}
destruct lc as [| c]. {
  cbn.
  now do 2 rewrite List.app_nil_r, List_map2_rngl_add_0_r.
}
cbn.
cbn in Hca |-*; f_equal.
apply Nat.succ_le_mono in Hca.
now apply IHla.
Qed.

Theorem lap_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ la, (- la + la)%lap = List.repeat 0%L (List.length la).
Proof.
intros Hop *.
induction la as [| a]; [ easy | cbn ].
rewrite (rngl_add_opp_diag_l Hop).
now f_equal.
Qed.

Theorem lap_sub_add :
  rngl_has_opp T = true →
  ∀ la lb,
  List.length lb ≤ List.length la
  → (la - lb + lb = la)%lap.
Proof.
intros Hop * Hba.
unfold lap_sub.
rewrite Hop.
rewrite <- lap_add_assoc.
rewrite (lap_add_opp_diag_l Hop).
revert lb Hba.
induction la as [| a]; intros; cbn. {
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hba; subst lb.
}
destruct lb as [| b]. {
  rewrite List.app_nil_l, List.repeat_length; cbn.
  rewrite rngl_add_0_r, List.app_nil_r.
  now rewrite List_map2_rngl_add_0_r.
}
cbn in Hba |-*; apply Nat.succ_le_mono in Hba.
rewrite rngl_add_0_r; f_equal.
now apply IHla.
Qed.

Theorem rev_lap_sub_norm :
  ∀ la lb,
  List.rev (la - lb)%lap =
    ((List.repeat 0%L (List.length lb - List.length la) ++ List.rev la) -
     (List.repeat 0%L (List.length la - List.length lb) ++ List.rev lb))%lap.
Proof.
intros.
unfold lap_sub.
remember (rngl_has_opp T) as op eqn:Hop.
symmetry in Hop.
destruct op. {
  rewrite rev_lap_add_norm.
  rewrite lap_opp_length.
  f_equal.
  rewrite lap_opp_app_distr.
  rewrite rev_lap_opp.
  f_equal.
  unfold lap_opp.
  rewrite map_opp_repeat.
  now rewrite rngl_opp_0.
}
remember (rngl_has_psub T) as su eqn:Hsu.
symmetry in Hsu.
destruct su. {
  progress unfold lap_psub.
  rewrite List_rev_map2. 2: {
    do 2 rewrite List.length_app.
    do 2 rewrite List.repeat_length.
    flia.
  }
  do 2 rewrite List.length_app.
  do 2 rewrite List.repeat_length.
  do 2 rewrite List.length_rev.
  do 2 rewrite Nat.sub_add_distr.
  do 2 rewrite List.rev_app_distr.
  do 2 rewrite List.rev_repeat.
  progress replace (_ - _ + _ - _ - _) with 0 by flia.
  progress replace (_ - _ + _ - _ - _) with 0 by flia.
  cbn.
  do 2 rewrite List.app_nil_r.
  easy.
}
apply rngl_has_opp_or_psub_iff in Hos.
rewrite Hop, Hsu in Hos.
now destruct Hos.
Qed.

Theorem rlap_pdiv_rem_step_Some :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ rla rlb rlr cq,
  List.hd 0%L rlb ≠ 0%L
  → rlap_pdiv_rem_step rla rlb = (Some cq, rlr)
  → List.rev rla =
      (List.rev rlb *
         List.rev
           (cq :: List.repeat 0%L (List.length rla - List.length rlb)) +
       List.rev rlr)%lap ∧
    List.length rla = S (List.length rlr) ∧
    cq = (List.hd 0 rla / List.hd 0 rlb)%L.
Proof.
intros Hic Hop Hiv.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hbz Hrl.
destruct rlb as [| b]; [ easy | cbn in Hbz, Hrl ].
destruct rla as [| a]; [ easy | ].
rewrite if_bool_if_dec in Hrl.
destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
apply Nat.ltb_ge in Hab.
injection Hrl; clear Hrl; intros H1 H2; subst cq rlr.
remember (a / b)%L as cq eqn:Hcq.
move b before a.
cbn; rewrite List.rev_repeat.
rewrite (lap_repeat_0_app_is_mul_power_l); [ | easy ].
rewrite (lap_mul_assoc Heo Hos); cbn.
rewrite <- (lap_repeat_0_app_is_mul_power_r). 2: {
  now intros H; apply List.app_eq_nil in H.
}
rewrite (lap_mul_const_r Hos).
do 2 rewrite List.map_app; cbn.
rewrite List.map_repeat.
rewrite (rngl_mul_0_l Hos).
rewrite List.map_rev.
replace (b * cq)%L with (b * (a / b))%L by now rewrite Hcq.
rewrite <- List.rev_repeat at 1.
rewrite List.app_assoc.
rewrite <- List.rev_app_distr.
remember (List.map _ _ ++ List.repeat _ _) as rlc eqn:Hrlc.
rewrite rev_lap_sub_norm.
rewrite List.length_map.
remember (List.repeat _ _ ++ _) as x.
rewrite <- List.rev_repeat.
rewrite <- List.rev_app_distr.
rewrite <- Hrlc.
subst x.
rewrite (proj2 (Nat.sub_0_le _ _)); [ cbn | easy ].
assert (Hca : List.length rlc = List.length rla). {
  rewrite Hrlc, List.length_app, List.length_map, List.repeat_length.
  now rewrite Nat.add_comm, Nat.sub_add.
}
rewrite <- rev_lap_sub; [ | easy ].
rewrite lap_add_app_l. 2: {
  do 2 rewrite List.length_rev.
  rewrite lap_sub_length.
  now rewrite Hca, Nat.max_id.
}
rewrite lap_sub_length, List.length_map.
rewrite Nat.max_l; [ | easy ].
split; [ | easy ].
rewrite (rngl_mul_comm Hic b).
rewrite (rngl_div_mul Hiv _ _ Hbz).
f_equal.
specialize (strip_0s_length_le (rla - rlc)%lap) as Hrac.
remember (rla - rlc)%lap as rlac eqn:Hrlac.
symmetry in Hrlac.
rewrite <- Hrlac.
rewrite rev_lap_sub; [ | easy ].
rewrite lap_add_comm.
symmetry.
apply (lap_sub_add Hop).
do 2 rewrite List.length_rev.
now rewrite Hca.
Qed.

Theorem rlap_pdiv_rem_length :
  ∀ {it} {rla rlb : list T} rlq rlr,
  List.hd 0%L rlb ≠ 0%L
  → rlap_pdiv_rem_loop it rla rlb = (rlq, rlr)
  → S (List.length rla) ≤ it
  → List.length rlq = List.length rla - (List.length rlb - 1).
Proof.
intros * Hbn Hqr Hit.
destruct rlb as [| b]; [ easy | ].
cbn; rewrite Nat.sub_0_r.
cbn in Hbn.
revert rla rlq rlr Hqr Hit.
induction it; intros; [ easy | ].
apply Nat.succ_le_mono in Hit.
remember (b :: rlb) as l; cbn in Hqr; subst l.
remember (rlap_pdiv_rem_step rla (b :: rlb)) as qrlr eqn:Hqrlr.
symmetry in Hqrlr.
destruct qrlr as (q, rlr').
destruct q as [cq| ]. 2: {
  injection Hqr; clear Hqr; intros; subst rlq rlr; cbn.
  apply rlap_pdiv_rem_step_None in Hqrlr.
  destruct Hqrlr as [H1| H1]; [ easy | ].
  destruct H1 as [H1| H1]; [ now destruct H1; subst rla | ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ easy | ].
  destruct H1 as (H1, _); cbn in H1.
  now apply Nat.lt_succ_r.
}
generalize Hqrlr; intros Hb.
apply rlap_pdiv_rem_step_length_r_a in Hb.
remember (rlap_pdiv_rem_loop it _ _) as qr eqn:Hqr'.
symmetry in Hqr'.
destruct qr as (rlq', rlr'').
injection Hqr; clear Hqr; intros; subst rlq rlr; cbn.
generalize Hqr'; intros Hqr.
apply IHit in Hqr; [ | now rewrite Hb ].
rewrite <- Hb, Hqr.
destruct (le_dec (List.length rlb) (List.length rlr')) as [Hrr| Hrr]. {
  now symmetry; rewrite Nat.sub_succ_l.
}
apply Nat.nle_gt in Hrr.
rewrite (proj2 (Nat.sub_0_le _ _)); [ | flia Hrr ].
rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
apply Nat.succ_lt_mono in Hrr.
rewrite Hb in Hrr.
cbn - [ "<?" ] in Hqrlr.
destruct rla as [| a]; [ easy | ].
cbn in Hrr.
apply Nat.succ_lt_mono in Hrr.
apply Nat.ltb_lt in Hrr.
now rewrite Hrr in Hqrlr.
Qed.

Theorem lap_add_app_r : ∀ la lb lc,
  List.length la ≤ List.length lb
  → (la + (lb ++ lc) = (la + lb) ++ lc)%lap.
Proof.
intros * Hab.
revert lb lc Hab.
induction la as [| a]; intros; [ now do 2 rewrite lap_add_0_l | cbn ].
destruct lb as [| b]; [ easy | cbn ].
cbn in Hab; apply Nat.succ_le_mono in Hab.
f_equal.
now apply IHla.
Qed.

Theorem rlap_pdiv_rem_loop_prop :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ it (rla rlb rlq rlr : list T),
  List.hd 0%L rlb ≠ 0%L
  → rlap_pdiv_rem_loop it rla rlb = (rlq, rlr)
  → S (List.length rla) ≤ it
  → List.rev rla = (List.rev rlb * List.rev rlq + List.rev rlr)%lap.
Proof.
intros Hco Hop Hiv.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hbn Hqr Hit.
revert rla rlq rlr Hqr Hit.
induction it; intros; [ easy | ].
apply Nat.succ_le_mono in Hit.
cbn in Hqr.
remember (rlap_pdiv_rem_step rla rlb) as qrlr eqn:Hqrlr.
symmetry in Hqrlr.
destruct qrlr as (q, rlr').
destruct q as [cq| ]. 2: {
  injection Hqr; clear Hqr; intros; subst rlq rlr; cbn.
  rewrite lap_mul_0_r, lap_add_0_l.
  f_equal.
  destruct rlb as [| b]; [ easy | ].
  destruct rla as [| a]; [ now destruct rlb; injection Hqrlr; intros | ].
  cbn - [ "<?" ] in Hqrlr.
  destruct (List.length rla <? List.length rlb); [ | easy ].
  now injection Hqrlr.
}
generalize Hqrlr; intros Hqrlr'.
apply (rlap_pdiv_rem_step_Some Hco Hop Hiv) in Hqrlr'; [ | easy ].
destruct Hqrlr' as (Hqrlr' & Hra & Hcq).
remember (rlap_pdiv_rem_loop it _ _) as qr eqn:Hqr'.
symmetry in Hqr'.
destruct qr as (rlq', rlr'').
injection Hqr; clear Hqr; intros; subst rlq rlr.
rename rlq' into rlq; rename rlr' into rlr.
rename Hqr' into Hqr.
move rla after rlb.
move rlq before rlb.
move rlr before rlq.
generalize Hqr; intros Hqrb.
apply (rlap_pdiv_rem_length _ _ Hbn) in Hqrb; [ | flia Hra Hit ].
apply IHit in Hqr. 2: {
  etransitivity; [ | apply Hit ].
  apply Nat.le_succ_l.
  destruct rlb as [| b]; [ easy | ].
  cbn in Hqrlr.
  destruct rla as [| a]; [ easy | ].
  rewrite if_bool_if_dec in Hqrlr.
  destruct (Sumbool.sumbool_of_bool _) as [Hab| Hab]; [ easy | ].
  apply Nat.ltb_ge in Hab.
  injection Hqrlr; clear Hqrlr; intros; subst cq rlr.
  rewrite lap_sub_length.
  now cbn; rewrite List.length_map, Nat.max_l.
}
rewrite Hqrlr', Hqr.
rewrite lap_add_assoc.
f_equal; cbn.
rewrite List.rev_repeat.
rewrite <- (lap_mul_add_distr_l Heo Hos).
f_equal.
rewrite lap_add_comm.
rewrite lap_add_app_r; cycle 1. {
  rewrite List.length_rev, List.repeat_length.
  flia Hra Hqrb.
}
f_equal.
apply lap_add_repeat_0_r.
rewrite List.length_rev.
rewrite Hra, Hqrb.
destruct rlb as [| b]; [ easy | ].
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem all_0_all_rev_0 : ∀ A (d a : A) la,
  (∀ i, i < List.length la → List.nth i la d = a)
  ↔ (∀ i, i < List.length la → List.nth i (List.rev la) d = a).
Proof.
intros *.
split; intros H i Hi. {
  rewrite List.rev_nth; [ apply H | easy ].
  now apply Nat.sub_lt.
} {
  rewrite <- (List.rev_involutive la).
  rewrite List.rev_nth; [ apply H | now rewrite List.length_rev ].
  rewrite List.length_rev.
  now apply Nat.sub_lt.
}
Qed.

Theorem eq_strip_0s_nil : ∀ d la,
  strip_0s la = [] ↔ ∀ i, i < length la → List.nth i la d = 0%L.
Proof.
intros.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
split. {
  intros Hla * Hil.
  revert i Hil.
  induction la as [| a]; intros; [ now destruct i | cbn ].
  cbn in Hla.
  rewrite if_bool_if_dec in Hla.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ | easy ].
  apply (rngl_eqb_eq Heo) in Haz.
  destruct i; [ easy | cbn in Hil ].
  apply Nat.succ_lt_mono in Hil.
  now apply IHla.
} {
  intros Hla.
  induction la as [| a]; [ easy | cbn ].
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply IHla.
    intros i Hil.
    apply Nat.succ_le_mono in Hil.
    apply (Hla (S i) Hil).
  }
  apply (rngl_eqb_neq Heo) in Haz.
  now specialize (Hla 0 (Nat.lt_0_succ _)).
}
Qed.

Theorem eq_strip_0s_rev_nil : ∀ la,
  strip_0s (List.rev la) = [] ↔
    ∀ i, i < List.length la → List.nth i la 0%L = 0%L.
Proof.
intros.
split; intros Hla. {
  apply all_0_all_rev_0.
  rewrite <- List.length_rev.
  now apply (eq_strip_0s_nil 0%L).
} {
  apply (eq_strip_0s_nil 0%L).
  apply all_0_all_rev_0.
  now rewrite List.length_rev, List.rev_involutive.
}
Qed.

Theorem lap_add_rev_strip : ∀ la lb,
  List.length lb ≤ List.length la
  → (la + List.rev (strip_0s lb) = la + List.rev lb)%lap.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hba.
revert lb Hba.
induction la as [| a]; intros. {
  now apply Nat.le_0_r, List.length_zero_iff_nil in Hba; subst lb.
}
cbn.
remember (List.rev lb) as lc eqn:Hlc; symmetry in Hlc.
apply List_rev_symm in Hlc; subst lb.
destruct lc as [| c]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev lc)) as lb eqn:Hlb; symmetry in Hlb.
rewrite List.length_rev in Hba; cbn in Hba.
apply Nat.succ_le_mono in Hba.
destruct lb as [| b]. {
  cbn.
  rewrite List.length_rev.
  specialize (proj1 (eq_strip_0s_rev_nil _) Hlb) as H1.
  clear Hlb IHla.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Hcz| Hcz]. {
    apply (rngl_eqb_eq Heo) in Hcz; subst c; cbn.
    rewrite List.app_nil_r; f_equal.
    rewrite List_map2_rngl_add_0_r.
    rewrite fold_lap_add; symmetry.
    clear a.
    revert la Hba.
    induction lc as [| c]; intros; [ apply lap_add_0_r | cbn ].
    destruct la as [| a]; [ easy | ].
    cbn in Hba.
    apply Nat.succ_le_mono in Hba.
    specialize (H1 0 (Nat.lt_0_succ _)) as H2; cbn in H2.
    subst c; cbn; rewrite rngl_add_0_r; f_equal.
    apply IHlc; [ | easy ].
    intros i Hi.
    apply Nat.succ_lt_mono in Hi.
    specialize (H1 (S i) Hi).
    apply H1.
  } {
    cbn; f_equal; clear c Hcz.
    rewrite List.app_nil_r, Nat.sub_0_r.
    rewrite List_map2_rngl_add_0_r, fold_lap_add.
    symmetry.
    clear a.
    revert la Hba.
    induction lc as [| c]; intros; [ apply lap_add_0_r | cbn ].
    destruct la as [| a]; [ easy | ].
    cbn in Hba.
    apply Nat.succ_le_mono in Hba.
    specialize (H1 0 (Nat.lt_0_succ _)) as H2; cbn in H2.
    subst c; cbn; rewrite rngl_add_0_r; f_equal.
    apply IHlc; [ | easy ].
    intros i Hi.
    apply Nat.succ_lt_mono in Hi.
    now specialize (H1 (S i) Hi).
  }
}
rewrite <- Hlb.
rewrite List.rev_app_distr; cbn; f_equal.
do 2 rewrite fold_lap_add.
rewrite IHla; [ | now rewrite List.length_rev ].
now rewrite List.rev_involutive.
Qed.

Theorem lap_div_mod :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ la lb lq lr : list T,
  has_polyn_prop la = true
  → List.last lb 0%L ≠ 0%L
  → has_polyn_prop lr = true
  → lap_pdiv_rem la lb = (lq, lr)
  → la = (lb * lq + lr)%lap ∧
    List.length lr < List.length lb ∧
    has_polyn_prop lq = true.
Proof.
intros Hco Hop Hiv.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Ha Hb Hr Hab.
assert (Hrb : List.length lr < List.length lb). {
  eapply lap_rem_length_lt; [ | | apply Hab ]. {
    now intros H; subst lb.
  } {
    unfold has_polyn_prop.
    apply (rngl_eqb_neq Heo) in Hb.
    now rewrite Hb, Bool.orb_true_r.
  }
}
rewrite and_comm, and_assoc.
split; [ easy | ].
rewrite and_comm.
assert (Hbz : List.hd 0%L (List.rev lb) ≠ 0%L). {
  remember (List.rev lb) as lc eqn:Hlc; symmetry in Hlc.
  apply List_rev_symm in Hlc; subst lb.
  destruct lc as [| c]; [ easy | ].
  cbn in Hb.
  now rewrite List.last_last in Hb.
}
apply Bool.orb_true_iff in Hr.
destruct Hr as [Hr| Hr]. {
  apply is_empty_list_empty in Hr.
  subst lr.
  rewrite lap_add_0_r.
  unfold lap_pdiv_rem in Hab.
  remember (rlap_pdiv_rem _ _) as qr eqn:Hqr; symmetry in Hqr.
  destruct qr as (rlq, rlr).
  injection Hab; clear Hab; intros Hr H; subst lq.
  apply List_eq_rev_nil in Hr.
  generalize Hqr; intros Hqr'.
  apply (rlap_pdiv_prop Hiv) in Hqr'; cycle 1. {
    unfold has_polyn_prop in Ha.
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      apply is_empty_list_empty in Ha; subst la.
      now left.
    }
    right.
    apply (rngl_neqb_neq Heo) in Ha.
    now rewrite <- List_last_rev, List.rev_involutive.
  } {
    right.
    now rewrite <- List_last_rev, List.rev_involutive.
  }
  specialize (rlap_pdiv_rem_loop_prop Hco Hop Hiv) as H1.
  specialize (H1 (S (List.length (List.rev la)))).
  specialize (H1 (List.rev la) (List.rev lb) rlq rlr).
  specialize (H1 Hbz Hqr (Nat.le_refl _)).
  do 2 rewrite List.rev_involutive in H1.
  destruct Hqr' as [Hqr'| Hqr']. {
    subst rlq.
    cbn in H1 |-*.
    rewrite lap_mul_0_r.
    rewrite lap_mul_0_r, lap_add_0_l in H1.
    symmetry in H1; apply List_rev_symm in H1; subst rlr.
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      now apply is_empty_list_empty in Ha.
    }
    destruct la as [| a] using List.rev_ind; [ easy | ].
    rewrite List.last_last in Ha.
    rewrite List.rev_app_distr in Hr; cbn in Hr.
    apply Bool.negb_true_iff in Ha.
    now rewrite Ha in Hr.
  }
  rewrite <- lap_add_rev_strip in H1. {
    rewrite Hr in H1.
    cbn in H1.
    rewrite lap_add_0_r in H1.
    split; [ easy | ].
    apply Bool.orb_true_iff; right.
    rewrite List_last_rev.
    now apply (rngl_neqb_neq Heo).
  }
  rewrite lap_mul_length.
  destruct lb as [| b]; [ easy | ].
  remember (List.rev rlq) as lq eqn:Hlq; symmetry in Hlq.
  destruct lq as [| q]. {
    now apply List_eq_rev_nil in Hlq; subst rlq.
  }
  apply rlap_rem_prop in Hqr. 2: {
    intros H.
    now apply List_eq_rev_nil in H.
  }
  cbn.
  rewrite List.length_rev in Hqr; cbn in Hqr; flia Hqr.
}
unfold lap_pdiv_rem in Hab.
remember (rlap_pdiv_rem _ _) as qr eqn:Hqr; symmetry in Hqr.
destruct qr as (rlq, rlr).
injection Hab; clear Hab; intros; subst lq lr.
specialize (rlap_pdiv_rem_loop_prop Hco Hop Hiv) as H1.
specialize (H1 (S (List.length (List.rev la)))).
specialize (H1 (List.rev la) (List.rev lb) rlq rlr).
specialize (H1 Hbz Hqr (Nat.le_refl _)).
do 2 rewrite List.rev_involutive in H1.
rewrite List.length_rev in Hrb.
remember (List.rev rlq) as lq eqn:Hlq; symmetry in Hlq.
destruct lq as [| q]. {
  split; [ | easy ].
  rewrite lap_mul_0_r, lap_add_0_l in H1.
  rewrite lap_mul_0_r, lap_add_0_l.
  rewrite H1; f_equal; symmetry.
  destruct rlr as [| r]; [ easy | ].
  cbn in Hr |-*.
  rewrite if_bool_if_dec in Hr |-*.
  destruct (Sumbool.sumbool_of_bool _) as [Hrz| Hrz]; [ | easy ].
  apply (rngl_eqb_eq Heo) in Hrz.
  subst r.
  cbn in H1.
  apply Bool.orb_true_iff in Ha.
  destruct Ha as [Ha| Ha]. {
    apply is_empty_list_empty in Ha; subst la.
    now symmetry in H1; apply List.app_eq_nil in H1.
  }
  rewrite H1 in Ha.
  rewrite List.last_last in Ha.
  now apply rngl_neqb_neq in Ha.
}
rewrite lap_add_rev_strip. {
  split; [ easy | ].
  apply Bool.orb_true_iff; right.
  rewrite <- Hlq, List_last_rev.
  apply (rngl_neqb_neq Heo).
  apply (rlap_pdiv_prop Hiv) in Hqr; [ | | now right ]. 2: {
    apply Bool.orb_true_iff in Ha.
    destruct Ha as [Ha| Ha]. {
      apply is_empty_list_empty in Ha; subst la.
      now left.
    }
    right.
    rewrite <- List_last_rev, List.rev_involutive.
    now apply (rngl_neqb_neq Heo) in Ha.
  }
  destruct Hqr as [Hqr| Hqr]; [ now subst rlq | easy ].
}
rewrite lap_mul_length.
destruct lb as [| b]; [ easy | ].
cbn.
apply rlap_rem_prop in Hqr. 2: {
  intros H.
  now apply List_eq_rev_nil in H.
}
rewrite List.length_rev in Hqr; cbn in Hqr; flia Hqr.
Qed.

Arguments lap_pdiv_rem {T ro} (la lb)%_lap.

Theorem eq_strip_0s_cons : ∀ la lb b,
  strip_0s la = b :: lb
  → b ≠ 0%L ∧
    ∃ i,
    i < length la ∧
    (∀ j, j < i → List.nth j la 0%L = 0%L) ∧
    List.nth i la 0%L = b.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hab.
induction la as [| a]; [ easy | ].
cbn in Hab.
rewrite if_bool_if_dec in Hab.
destruct (Sumbool.sumbool_of_bool (a =? 0)%L) as [Haz| Haz]. {
  apply (rngl_eqb_eq Heo) in Haz; subst a.
  specialize (IHla Hab).
  destruct IHla as (Hbz & i & Hil & Hbef & Hi).
  split; [ easy | ].
  exists (S i).
  cbn - [ List.nth ].
  split; [ now apply -> Nat.succ_lt_mono | ].
  split; [ | easy ].
  intros j Hj.
  destruct j; [ easy | cbn ].
  apply Nat.succ_lt_mono in Hj.
  now apply Hbef.
}
injection Hab; clear Hab; intros; subst b lb.
apply (rngl_eqb_neq Heo) in Haz.
split; [ easy | ].
exists 0.
now cbn.
Qed.

Theorem polyn_norm_prop : ∀ la, has_polyn_prop (lap_norm la) = true.
Proof.
intros.
unfold has_polyn_prop, lap_norm.
induction la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]; cbn. {
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]; [ easy | cbn ].
  now apply Bool.negb_true_iff.
}
cbn in IHla.
rewrite List.last_last in IHla.
apply Bool.orb_true_iff in IHla.
apply Bool.orb_true_iff; right.
rewrite List.last_last.
destruct IHla as [H1| H1]; [ | easy ].
apply is_empty_list_empty in H1.
now apply List.app_eq_nil in H1.
Qed.

Theorem all_0_lap_norm_nil : ∀ la,
  (∀ i, List.nth i la 0%L = 0%L)
  ↔ lap_norm la = [].
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros *.
split; intros Hla. {
  induction la as [| a]; [ easy | cbn ].
  rewrite strip_0s_app.
  remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
  destruct lb as [| b]. {
    cbn.
    rewrite if_bool_if_dec.
    destruct (Sumbool.sumbool_of_bool _) as [H1| H1]; [ easy | exfalso ].
    apply (rngl_eqb_neq Heo) in H1.
    now specialize (Hla 0); cbn in Hla.
  }
  exfalso.
  assert (H : strip_0s (List.rev la) = []). {
    clear - rp Hed Hla.
    apply (eq_strip_0s_nil 0%L).
    intros i Hil.
    rewrite List.length_rev in Hil.
    rewrite List.rev_nth; [ | easy ].
    specialize (Hla (S (List.length la - S i))).
    now cbn in Hla.
  }
  now rewrite Hlb in H.
} {
  intros i.
  destruct (lt_dec i (List.length la)) as [Hila| Hila]. 2: {
    apply Nat.nlt_ge in Hila.
    now apply List.nth_overflow.
  }
  unfold lap_norm in Hla.
  apply List_eq_rev_nil in Hla.
  apply (eq_strip_0s_nil 0%L) with (i := List.length la - S i) in Hla. {
    rewrite List.rev_nth in Hla; [ | flia Hila ].
    rewrite <- Nat_succ_sub_succ_r in Hla; [ | easy ].
    rewrite Nat.sub_sub_distr in Hla; [ | flia Hila | easy ].
    now rewrite Nat.sub_diag, Nat.add_0_l in Hla.
  }
  now rewrite List.length_rev; apply Nat.sub_lt.
}
Qed.

Theorem lap_norm_app_repeat_0 : ∀ la,
  la =
    lap_norm la ++
    List.repeat 0%L (List.length la - List.length (lap_norm la)).
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
induction la as [| a]; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    apply (rngl_eqb_eq Heo) in Haz.
    cbn; subst a; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil 0%L _) Hlb) as H1.
      destruct (lt_dec i (List.length la)) as [Hila| Hila]. {
        rewrite <- (List.rev_involutive la).
        rewrite List.rev_nth; rewrite List.length_rev; [ | easy ].
        apply H1.
        now rewrite List.length_rev; apply Nat.sub_lt.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite List.nth_overflow.
    }
    rewrite H in IHla; cbn in IHla.
    now rewrite Nat.sub_0_r in IHla.
  } {
    cbn; f_equal.
    assert (H : lap_norm la = []). {
      apply all_0_lap_norm_nil.
      intros i.
      specialize (proj1 (eq_strip_0s_nil 0%L _) Hlb) as H1.
      destruct (lt_dec i (List.length la)) as [Hila| Hila]. {
        rewrite <- (List.rev_involutive la).
        rewrite List.rev_nth; rewrite List.length_rev; [ | easy ].
        apply H1.
        now rewrite List.length_rev; apply Nat.sub_lt.
      }
      apply Nat.nlt_ge in Hila.
      now rewrite List.nth_overflow.
    }
    now rewrite H in IHla; cbn in IHla.
  }
} {
  cbn.
  rewrite List.rev_app_distr; cbn; f_equal.
  replace (List.rev lb ++ [b]) with (List.rev (b :: lb)) by easy.
  rewrite <- Hlb.
  now rewrite fold_lap_norm.
}
Qed.

Theorem lap_norm_length_le : ∀ la, List.length (lap_norm la) ≤ List.length la.
Proof.
intros.
rewrite (lap_norm_app_repeat_0 la) at 2.
rewrite List.length_app; flia.
Qed.

Theorem lap_pdiv_is_norm :
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (lap_pdiv la lb) = true.
Proof.
intros Hiv.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Ha Hb.
unfold lap_pdiv.
remember (rlap_pdiv_rem (List.rev la) (List.rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr); cbn.
unfold has_polyn_prop.
apply Bool.orb_true_iff.
destruct rlq as [| q]; [ now left | right ].
cbn; rewrite List.last_last.
apply (rlap_pdiv_prop Hiv) in Hqr; cycle 1. {
  apply Bool.orb_true_iff in Ha.
  destruct Ha as [Ha| Ha]; [ now left; destruct la | right ].
  destruct la as [| a] using List.rev_ind. {
    cbn in Ha.
    now rewrite (rngl_eqb_refl Heo) in Ha.
  }
  rewrite List.last_last in Ha.
  rewrite List.rev_app_distr; cbn.
  now apply (rngl_neqb_neq Heo) in Ha.
} {
  unfold has_polyn_prop in Hb.
  apply Bool.orb_true_iff in Hb.
  destruct Hb as [Hb| Hb]; [ now left; destruct lb | right ].
  destruct lb as [| b] using List.rev_ind. {
    cbn in Hb.
    now rewrite (rngl_eqb_refl Heo) in Hb.
  }
  rewrite List.last_last in Hb.
  rewrite List.rev_app_distr; cbn.
  now apply (rngl_neqb_neq Heo) in Hb.
}
destruct Hqr as [Hqr| Hqr]; [ easy | ].
cbn in Hqr.
now apply (rngl_neqb_neq Heo).
Qed.

Theorem lap_rem_is_norm : ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (lap_rem la lb) = true.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Ha Hb.
unfold lap_rem.
remember (rlap_pdiv_rem (List.rev la) (List.rev lb)) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (rlq, rlr); cbn.
unfold has_polyn_prop.
destruct rlr as [| r]; [ easy | ].
cbn; rewrite if_bool_if_dec.
apply Bool.orb_true_iff.
destruct (Sumbool.sumbool_of_bool _) as [Hrz| Hrz]. {
  rewrite List_last_rev.
  remember (strip_0s rlr) as rl eqn:Hrl;symmetry in Hrl.
  destruct rl as [| a]; [ now left | right; cbn ].
  apply eq_strip_0s_cons in Hrl.
  now apply (rngl_neqb_neq Heo).
}
right; cbn; rewrite List.last_last.
now rewrite Hrz.
Qed.

(* addition to 0 *)

Theorem has_polyn_prop_lap_norm : ∀ la,
  has_polyn_prop la = true
  → lap_norm la = la.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * lapr.
unfold has_polyn_prop in lapr.
apply Bool.orb_true_iff in lapr.
destruct lapr as [lapr| lapr]; [ now destruct la | ].
apply (rngl_neqb_neq Heo) in lapr.
destruct la as [| a] using List.rev_ind; [ easy | cbn ].
clear IHla.
rewrite List.last_last in lapr.
unfold lap_norm.
rewrite List.rev_app_distr; cbn.
apply (rngl_eqb_neq Heo) in lapr.
rewrite lapr; cbn.
now rewrite List.rev_involutive.
Qed.

Theorem lap_convol_mul_0_l : ∀ la lb i len,
  (∀ i, List.nth i la 0%L = 0%L)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Ha.
revert i.
induction len; intros; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev _)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    now rewrite Ha, rngl_mul_0_l.
  }
  cbn.
  now rewrite rngl_eqb_refl.
}
unfold lap_norm in IHlen.
specialize (IHlen (S i)).
rewrite Hlc in IHlen.
now apply List_eq_rev_nil in IHlen.
Qed.

Theorem lap_convol_mul_0_r : ∀ la lb i len,
  (∀ i, List.nth i lb 0%L = 0%L)
  → lap_norm (lap_convol_mul la lb i len) = [].
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hb.
revert i.
induction len; intros; [ easy | ].
cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev _)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  rewrite all_0_rngl_summation_0. 2: {
    intros j Hj.
    rewrite Hb, rngl_mul_0_r; [ easy | easy ].
  }
  cbn.
  now rewrite rngl_eqb_refl.
}
unfold lap_norm in IHlen.
specialize (IHlen (S i)).
rewrite Hlc in IHlen.
now apply List_eq_rev_nil in IHlen.
Qed.

Theorem lap_convol_mul_cons_with_0_l : ∀ a la lb i len,
  (∀ i, List.nth i la 0%L = 0%L)
  → lap_convol_mul (a :: la) lb i len = lap_convol_mul [a] lb i len.
Proof.
intros * Hla.
revert i.
induction len; intros; [ easy | ].
cbn.
f_equal; [ | apply IHlen ].
apply rngl_summation_eq_compat.
intros j Hj.
destruct j; [ easy | ].
rewrite Tauto_match_nat_same.
now rewrite Hla.
Qed.

Theorem lap_convol_mul_app_rep_0_l : ∀ la lb i len n,
  lap_norm (lap_convol_mul (la ++ List.repeat 0%L n) lb i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert la i len.
induction n; intros. {
  now cbn; rewrite List.app_nil_r.
}
cbn.
rewrite List_cons_is_app.
rewrite List.app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | ].
cbn.
do 2 rewrite strip_0s_app.
rewrite <- (List.rev_involutive (strip_0s _)).
rewrite fold_lap_norm.
rewrite <- (List.rev_involutive (strip_0s (List.rev _))).
rewrite fold_lap_norm.
rewrite IHlen.
remember (List.rev (lap_norm _)) as lc eqn:Hlc; symmetry in Hlc.
f_equal.
destruct lc as [| c]. {
  apply List_eq_rev_nil in Hlc.
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (List.length la)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow la); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (List.length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec j (List.length la)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow la); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec j (List.length la)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
Qed.

Theorem lap_convol_mul_app_rep_0_r : ∀ la lb i len n,
  lap_norm (lap_convol_mul la (lb ++ List.repeat 0%L n) i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
revert lb i len.
induction n; intros; [ now cbn; rewrite List.app_nil_r | cbn ].
rewrite List_cons_is_app.
rewrite List.app_assoc.
rewrite IHn; clear n IHn.
revert la i.
induction len; intros; [ easy | cbn ].
do 2 rewrite strip_0s_app.
rewrite <- (List.rev_involutive (strip_0s _)).
rewrite fold_lap_norm.
rewrite <- (List.rev_involutive (strip_0s (List.rev _))).
rewrite fold_lap_norm.
rewrite IHlen.
remember (List.rev (lap_norm _)) as lc eqn:Hlc; symmetry in Hlc.
f_equal.
destruct lc as [| c]. {
  apply List_eq_rev_nil in Hlc.
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec (i - j) (List.length lb)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow lb); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec (i - j) (List.length lb)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
} {
  f_equal; f_equal.
  apply rngl_summation_eq_compat.
  intros j Hj.
  f_equal; clear.
  destruct (lt_dec (i - j) (List.length lb)) as [Hjla| Hjla]. {
    now rewrite List.app_nth1.
  }
  apply Nat.nlt_ge in Hjla.
  rewrite (List.nth_overflow lb); [ | easy ].
  rewrite List.app_nth2; [ | easy ].
  destruct (Nat.eq_dec (i - j) (List.length lb)) as [Hjla2| Hjla2]. {
    now rewrite Hjla2, Nat.sub_diag.
  }
  rewrite List.nth_overflow; [ easy | cbn; flia Hjla Hjla2 ].
}
Qed.

Theorem lap_norm_convol_mul_norm_r : ∀ la lb i len,
  lap_norm (lap_convol_mul la (lap_norm lb) i len) =
  lap_norm (lap_convol_mul la lb i len).
Proof.
intros.
rewrite (lap_norm_app_repeat_0 lb) at 2.
now rewrite lap_convol_mul_app_rep_0_r.
Qed.

Theorem lap_norm_cons_norm : ∀ a la lb i len,
  List.length (a :: la) + List.length lb - 1 ≤ i + len
  → lap_norm (lap_convol_mul (a :: lap_norm la) lb i len) =
    lap_norm (lap_convol_mul (a :: la) lb i len).
Proof.
intros * Hlen.
rewrite (lap_norm_app_repeat_0 la) at 2.
rewrite List.app_comm_cons.
now rewrite lap_convol_mul_app_rep_0_l.
Qed.

Theorem lap_mul_norm_idemp_l : ∀ la lb,
  lap_norm (lap_norm la * lb)%lap = lap_norm (la * lb)%lap.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [Haz| Haz]. {
    cbn.
    apply (rngl_eqb_eq Heo) in Haz.
    destruct lb as [| b]; [ easy | cbn ].
    rewrite lap_convol_mul_0_l; [ easy | ].
    intros i; cbn.
    destruct i; [ easy | ].
    specialize (proj1 (eq_strip_0s_nil 0%L _) Hlc) as H1.
    destruct (lt_dec i (List.length la)) as [Hil| Hil]. {
      specialize (H1 (List.length la - S i)).
      rewrite List.length_rev in H1.
      assert (H : List.length la - S i < List.length la) by
        now apply Nat.sub_lt.
      specialize (H1 H); clear H.
      rewrite List.rev_nth in H1. {
        rewrite <- Nat_succ_sub_succ_r in H1; [ | easy ].
        rewrite Nat.sub_sub_distr in H1; [ | now apply Nat.lt_le_incl | easy ].
        now rewrite Nat.sub_diag in H1.
      }
      now apply Nat.sub_lt.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite List.nth_overflow.
  }
  cbn.
  destruct lb as [| b]; [ easy | ].
  remember (b :: lb) as ld eqn:Hld; symmetry in Hld.
  do 2 rewrite Nat.sub_0_r.
  rewrite fold_lap_norm.
  rewrite (lap_convol_mul_cons_with_0_l _ la). 2: {
    intros i.
    specialize (proj1 (eq_strip_0s_nil 0%L _) Hlc) as H1.
    destruct (lt_dec i (List.length la)) as [Hil| Hil]. {
      specialize (H1 (List.length la - S i)).
      rewrite List.length_rev in H1.
      assert (H : List.length la - S i < List.length la) by
        now apply Nat.sub_lt.
      specialize (H1 H); clear H.
      rewrite List.rev_nth in H1. {
        rewrite <- Nat_succ_sub_succ_r in H1; [ | easy ].
        rewrite Nat.sub_sub_distr in H1; [ | now apply Nat.lt_le_incl | easy ].
        now rewrite Nat.sub_diag in H1.
      }
      now apply Nat.sub_lt.
    }
    apply Nat.nlt_ge in Hil.
    now rewrite List.nth_overflow.
  }
  rewrite Nat.add_comm.
  apply (lap_convol_mul_more Heo Hos); cbn.
  now rewrite Nat.sub_0_r.
}
rewrite List.rev_app_distr; cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (List.rev lc ++ [c]) with (List.rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_lap_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
rewrite
  (lap_convol_mul_more Heo Hos (List.length la - List.length (lap_norm la))).
    2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite (Nat.add_comm _ (List.length lb)).
rewrite <- Nat.add_assoc.
rewrite Nat.add_sub_assoc; [ | apply lap_norm_length_le ].
rewrite (Nat.add_comm _ (List.length la)).
rewrite Nat.add_sub.
rewrite Nat.add_comm.
apply lap_norm_cons_norm.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem lap_mul_norm_idemp_r : ∀ la lb,
  lap_norm (la * lap_norm lb)%lap = lap_norm (la * lb)%lap.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
unfold "*"%lap; cbn.
destruct la as [| a]; [ easy | cbn ].
unfold lap_norm.
remember (strip_0s (List.rev lb)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. {
  cbn.
  specialize (proj1 (eq_strip_0s_nil 0%L _) Hlc) as H1.
  rewrite List.length_rev in H1.
  destruct lb as [| b]; [ easy | cbn ].
  rewrite fold_lap_norm.
  symmetry; apply lap_convol_mul_0_r.
  intros i.
  specialize (H1 (List.length lb - i)).
  rewrite List.rev_nth in H1; [ | cbn; flia ].
  cbn in H1.
  destruct (le_dec i (List.length lb)) as [Hib| Hib]. 2: {
    apply Nat.nle_gt in Hib.
    now rewrite List.nth_overflow.
  }
  assert (H : List.length lb - i < S (List.length lb)) by flia Hib.
  specialize (H1 H).
  now replace (List.length lb - (List.length lb - i)) with i in H1
    by flia Hib.
}
cbn.
rewrite fold_lap_norm.
destruct lb as [| b]; [ easy | ].
remember (b :: lb) as d eqn:Hd.
replace (List.rev lc ++ [c]) with (List.rev (c :: lc)) by easy.
rewrite <- Hlc.
rewrite fold_lap_norm.
do 2 rewrite Nat.sub_0_r.
clear c lc b lb Hlc Hd.
rename d into lb.
remember (lap_norm lb) as lc eqn:Hlc.
symmetry in Hlc.
destruct lc as [| c]. {
  rewrite fold_lap_norm.
  unfold lap_norm in Hlc.
  apply List_eq_rev_nil in Hlc.
  specialize (proj1 (eq_strip_0s_rev_nil lb) Hlc) as H1.
  clear Hlc; rename H1 into Hlb.
  rewrite lap_convol_mul_0_r; [ easy | ].
  intros i.
  destruct (lt_dec i (List.length lb)) as [Hil| Hil]. 2: {
    apply Nat.nlt_ge in Hil.
    now apply List.nth_overflow.
  }
  now apply Hlb.
}
cbn.
rewrite fold_lap_norm.
rewrite
    (lap_convol_mul_more Heo Hos (List.length lb - S (List.length lc))).
    2: {
  now cbn; rewrite Nat.sub_0_r.
}
rewrite <- Nat.add_assoc.
rewrite (Nat.add_comm (S (List.length lc))).
rewrite Nat.sub_add. 2: {
  etransitivity; [ | apply lap_norm_length_le ].
  now rewrite Hlc.
}
rewrite <- Hlc.
apply lap_norm_convol_mul_norm_r.
Qed.

Theorem list_nth_lap_opp :
  rngl_has_opp T = true →
  ∀ k la, (List.nth k (lap_opp la) 0 = - List.nth k la 0)%L.
Proof.
intros Hop *.
revert la.
induction k; intros. {
  destruct la as [| a]; cbn; [ now rewrite rngl_opp_0 | easy ].
}
destruct la as [| a]; cbn; [ now rewrite rngl_opp_0 | ].
apply IHk.
Qed.

Theorem list_nth_lap_sub :
  rngl_has_opp T = true →
  ∀ k la lb,
  (List.nth k (lap_sub la lb) 0 =
   List.nth k la 0 - List.nth k lb 0)%L.
Proof.
intros Hop *.
unfold lap_sub.
rewrite Hop.
rewrite list_nth_lap_add.
rewrite (list_nth_lap_opp Hop).
now rewrite (rngl_add_opp_r Hop).
Qed.

Theorem lap_add_opp_diag_r :
  rngl_has_opp T = true
  → ∀ la, (la + - la)%lap = List.repeat 0%L (List.length la).
Proof.
intros Hop *.
clear Hos.
induction la as [| a]; [ easy | cbn ].
rewrite fold_lap_opp.
rewrite rngl_add_opp_r; [ | easy ].
rewrite rngl_sub_diag; [ | now apply rngl_has_opp_has_opp_or_psub ].
now f_equal.
Qed.

Theorem lap_norm_repeat_0 : ∀ n, lap_norm (List.repeat 0%L n) = [].
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
unfold lap_norm.
rewrite List.rev_repeat.
induction n; [ easy | cbn ].
now rewrite (rngl_eqb_refl Heo).
Qed.

Theorem lap_norm_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ la, lap_norm (- la + la)%lap = [].
Proof.
intros Hop *.
rewrite (lap_add_opp_diag_l Hop).
apply lap_norm_repeat_0.
Qed.

(* *)

Theorem lap_psub_diag :
  ∀ la, lap_psub la la = List.repeat 0%L (List.length la).
Proof.
intros.
unfold lap_psub.
rewrite Nat.sub_diag, List.app_nil_r.
induction la as [| a]; [ easy | cbn ].
rewrite IHla; f_equal.
apply (rngl_psub_diag Hos).
Qed.

Theorem lap_add_sub :
  ∀ la lb,
  (la + lb - lb)%lap =
    la ++ List.repeat 0%L (List.length lb - List.length la).
Proof.
intros.
unfold lap_sub.
remember (rngl_has_opp T) as op eqn:Hop; symmetry in Hop.
destruct op. {
rewrite <- lap_add_assoc.
rewrite (lap_add_opp_diag_r Hop).
destruct (le_dec (List.length lb) (List.length la)) as [Hlba| Hlba]. {
  rewrite lap_add_repeat_0_r; [ | easy ].
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  symmetry; apply List.app_nil_r.
}
apply Nat.nle_gt in Hlba.
replace (List.length lb) with
  (List.length la + (List.length lb - List.length la)) at 1 by flia Hlba.
rewrite List.repeat_app.
rewrite lap_add_app_r; [ | now rewrite List.repeat_length ].
f_equal.
now apply lap_add_repeat_0_r.
}
remember (rngl_has_psub T) as su eqn:Hsu; symmetry in Hsu.
destruct su. {
  revert lb.
  induction la as [| a]; intros. {
    rewrite lap_add_0_l, List.app_nil_l, Nat.sub_0_r.
    apply lap_psub_diag.
  }
  destruct lb as [| b]. {
    cbn - [ lap_psub ].
    rewrite rngl_add_0_r, List.app_nil_r.
    rewrite List_map2_rngl_add_0_r.
    apply (lap_psub_0_r Hsu).
  }
  cbn.
  rewrite fold_lap_add, fold_lap_psub.
  rewrite IHla; f_equal.
  specialize (rngl_add_sub Hos a b) as H1.
  unfold rngl_sub in H1.
  now rewrite Hop, Hsu in H1.
}
apply rngl_has_opp_or_psub_iff in Hos.
destruct Hos; congruence.
Qed.

Theorem lap_add_move_l :
  ∀ la lb lc : list T,
  (la + lb)%lap = lc
  → lb ++ List.repeat 0%L (List.length la - List.length lb) = (lc - la)%lap.
Proof.
intros * Hab.
subst lc.
symmetry; rewrite lap_add_comm.
now rewrite lap_add_sub.
Qed.

Theorem lap_mul_has_polyn_prop :
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → has_polyn_prop (la * lb)%lap = true.
Proof.
intros Hiv.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Ha Hb.
unfold has_polyn_prop in Ha, Hb |-*.
apply Bool.orb_true_iff in Ha, Hb.
apply Bool.orb_true_iff.
destruct Ha as [Ha| Ha]. {
  apply is_empty_list_empty in Ha; subst la.
  rewrite lap_mul_0_l.
  now left.
}
destruct Hb as [Hb| Hb]. {
  apply is_empty_list_empty in Hb; subst lb.
  rewrite lap_mul_0_r.
  now left.
}
right.
apply (rngl_neqb_neq Heo) in Ha, Hb.
apply (rngl_neqb_neq Heo).
rewrite last_lap_mul.
intros Hab.
now apply (rngl_eq_mul_0_l Hos Hiq) in Hab.
Qed.

Theorem lap_norm_mul :
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → lap_norm (la * lb) = (la * lb)%lap.
Proof.
intros Hiv * Ha Hb.
apply has_polyn_prop_lap_norm.
now apply (lap_mul_has_polyn_prop Hiv).
Qed.

Theorem lap_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ la lb,
  has_polyn_prop la = true
  → has_polyn_prop lb = true
  → lb ≠ []
  → (la * lb / lb)%lap = la.
Proof.
intros Hco Hop Hiv.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * pa pb Hbz.
remember (lap_pdiv_rem (la * lb) lb) as qr eqn:Hqr.
symmetry in Hqr.
destruct qr as (lq, lr).
specialize (lap_div_mod Hco Hop Hiv) as H1.
specialize (H1 (la * lb)%lap lb lq lr).
specialize (H1 (lap_mul_has_polyn_prop Hiv la lb pa pb)).
assert (H : List.last lb 0%L ≠ 0%L). {
  apply (rngl_neqb_neq Heo).
  apply Bool.orb_true_iff in pb.
  destruct pb as [pb| ]; [ | easy ].
  now apply is_empty_list_empty in pb.
}
specialize (H1 H); clear H.
assert (pr : has_polyn_prop lr = true). {
  specialize (lap_rem_is_norm (la * lb)%lap lb) as H2.
  specialize (H2 (lap_mul_has_polyn_prop Hiv la lb pa pb) pb).
  assert (H : lr = ((la * lb) mod lb)%lap). {
    unfold lap_rem.
    unfold lap_pdiv_rem in Hqr.
    destruct (rlap_pdiv_rem _ _).
    now injection Hqr.
  }
  now rewrite <- H in H2.
}
move lq before lb; move lr before lq.
move pr before pb.
specialize (H1 pr Hqr).
destruct H1 as (Hab & Hrb & pq).
move pq before pb.
generalize Hab; intros Hab1.
symmetry in Hab1.
apply lap_add_move_l in Hab1.
symmetry in Hab1.
rewrite (lap_mul_comm Hco) in Hab1.
rewrite <- (lap_mul_sub_distr_l Hop) in Hab1.
apply (f_equal lap_norm) in Hab1.
rewrite (lap_norm_app_0_r Heo) in Hab1 by apply List.nth_repeat.
rewrite (has_polyn_prop_lap_norm lr pr) in Hab1.
rewrite <- lap_mul_norm_idemp_r in Hab1.
rewrite (lap_norm_mul Hiv) in Hab1; [ | easy | apply polyn_norm_prop ].
generalize Hab1; intros Hab2.
apply (f_equal (λ l, List.length l)) in Hab2.
rewrite lap_mul_length in Hab2.
destruct lb as [| b]; [ easy | clear Hbz ].
remember (lap_norm (la - lq)) as lc eqn:Hlc; symmetry in Hlc.
destruct lc as [| c]. 2: {
  cbn in Hab2.
  cbn in Hrb; flia Hrb Hab2.
}
apply eq_sym, List.length_zero_iff_nil in Hab2.
clear Hab Hab1 Hrb pr; subst lr.
unfold lap_pdiv.
unfold lap_pdiv_rem in Hqr.
remember (rlap_pdiv_rem _ _) as qr eqn:Hqr'.
symmetry in Hqr'.
destruct qr as (rlq, rlr).
injection Hqr; clear Hqr; intros Hr Hq; rewrite Hq.
specialize (proj2 (all_0_lap_norm_nil _) Hlc) as H1.
rewrite <- (has_polyn_prop_lap_norm la pa).
rewrite <- (has_polyn_prop_lap_norm lq pq).
apply (list_nth_lap_eq Heo).
intros i.
specialize (H1 i).
rewrite (list_nth_lap_sub Hop) in H1.
now apply -> (rngl_sub_move_0_r Hop) in H1.
Qed.

Let Heo := rngl_has_eq_dec_or_is_ordered_l Hed.

Theorem lap_rngl_of_nat :
  let lop := lap_ring_like_op Heo in
  ∀ n, rngl_of_nat n = if Nat.eq_dec n 0 then [] else [rngl_of_nat n].
Proof.
intros; cbn.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction n; [ easy | clear Hnz ].
remember [1%L] as x; cbn; subst x.
(**)
destruct n; [ easy | ].
now rewrite IHn.
Qed.

End a.

(* polynomials *)

Record polyn T {ro : ring_like_op T} := mk_polyn
  { lap : list T;
    lap_prop : has_polyn_prop lap = true }.

Arguments mk_polyn {T ro} lap%_lap.
Arguments lap {T ro}.
Arguments lap_prop {T ro}.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context (Hos : rngl_has_opp_or_psub T = true).
Context (Hed : rngl_has_eq_dec T = true).

(* polyn_eq is equivalent to lap_eq *)

Theorem eq_polyn_eq : ∀ pa pb,
  lap pa = lap pb
  ↔ pa = pb.
Proof.
intros.
split; intros Hab; [ | now subst ].
destruct pa as (la, pa).
destruct pb as (lb, pb).
cbn in Hab.
subst lb.
f_equal.
apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Theorem polyn_eq_dec : ∀ P Q : polyn T, {P = Q} + {P ≠ Q}.
Proof.
intros.
progress unfold rngl_has_eq_dec in Hed.
destruct rngl_opt_eq_dec as [rngl_eq_dec| ]; [ | easy ].
specialize (List.list_eq_dec rngl_eq_dec (lap P) (lap Q)) as H1.
destruct H1 as [H1| H1]. {
  now apply eq_polyn_eq in H1; left.
} {
  right; intros H; apply H1.
  now apply eq_polyn_eq.
}
Qed.

Definition polyn_of_norm_lap la :=
  mk_polyn (lap_norm la) (polyn_norm_prop la).

Definition polyn_of_const c :=
  polyn_of_norm_lap [c].

Arguments polyn_of_const c%_L.

Definition polyn_zero := mk_polyn [] eq_refl.
Definition polyn_one := polyn_of_const 1.

Definition polyn_norm la := mk_polyn (lap_norm la) (polyn_norm_prop la).
Definition polyn_add p1 p2 := polyn_norm (lap_add (lap p1) (lap p2)).
Definition polyn_opp pol := polyn_norm (lap_opp (lap pol)).

Definition polyn_psub p1 p2 := polyn_norm (lap_psub (lap p1) (lap p2)).

Definition polyn_mul p1 p2 := polyn_norm (lap_mul (lap p1) (lap p2)).

Definition polyn_pdiv (pa pb : polyn T) : polyn T :=
  match Sumbool.sumbool_of_bool (rngl_has_inv T) with
  | left Hiv =>
      let lq := lap_pdiv (lap pa) (lap pb) in
      mk_polyn lq
        (lap_pdiv_is_norm Hos Hed Hiv (lap pa) (lap pb) (lap_prop pa)
           (lap_prop pb))
  | right _ =>
      polyn_zero
  end.

(* polyn opposite or subtraction *)

Definition polyn_opt_opp_or_psub :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match rngl_opt_opp_or_psub T with
  | Some (inl _) => Some (inl polyn_opp)
  | Some (inr _) => Some (inr polyn_psub)
  | None => None
  end.

(* polyn quotient *)

Definition polyn_opt_inv_or_pdiv :
  option ((polyn T → polyn T) + (polyn T → polyn T → polyn T)) :=
  match Sumbool.sumbool_of_bool (rngl_mul_is_comm T) with
  | left Hco =>
      match Sumbool.sumbool_of_bool (rngl_has_opp T) with
      | left Hop =>
          match Sumbool.sumbool_of_bool (rngl_has_inv T) with
         | left Hiv =>
             match rngl_opt_inv_or_pdiv T with
             | Some _ => Some (inr polyn_pdiv)
             | None => None
             end
          | right _ => None
          end
      | right _ => None
      end
  | right _ => None
  end.

Definition polyn_ring_like_op : ring_like_op (polyn T) :=
  {| rngl_zero := polyn_zero;
     rngl_one := polyn_one;
     rngl_add := polyn_add;
     rngl_mul := polyn_mul;
     rngl_opt_opp_or_psub := polyn_opt_opp_or_psub;
     rngl_opt_inv_or_pdiv := polyn_opt_inv_or_pdiv;
     rngl_opt_is_zero_divisor := Some (λ _, True);
     rngl_opt_eq_dec := Some polyn_eq_dec;
     rngl_opt_leb := None |}.

(* allows to use ring-like theorems on polynomials
Canonical Structure polyn_ring_like_op.
*)

(* to search for ring-like polynomials operators in the context *)
(*
Existing Instance polyn_ring_like_op.
*)
(* Another way is to add at the beginning of the theorem
  let _ := polyn_ring_like_op in
*)

Declare Scope polyn_scope.
Delimit Scope polyn_scope with pol.

Notation "0" := polyn_zero : polyn_scope.
Notation "1" := polyn_one : polyn_scope.
Notation "- a" := (polyn_opp a) : polyn_scope.
Notation "a + b" := (polyn_add a b) : polyn_scope.
Notation "a * b" := (polyn_mul a b) : polyn_scope.

Theorem polyn_add_comm :
  let rop := polyn_ring_like_op in
  ∀ a b : polyn T, (a + b)%L = (b + a)%L.
Proof.
intros.
cbn.
progress unfold "+"%pol.
now rewrite lap_add_comm.
Qed.

Theorem polyn_add_assoc : ∀ pa pb pc,
  (pa + (pb + pc) = (pa + pb) + pc)%pol.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros (la, lapr) (lb, lbpr) (lc, lcpr).
apply eq_polyn_eq.
cbn - [ lap_norm ].
do 4 rewrite fold_lap_add.
rewrite (lap_add_norm_idemp_l Heo).
rewrite (lap_add_norm_idemp_r Heo).
now rewrite lap_add_assoc.
Qed.

Theorem polyn_add_0_l : ∀ p, (0 + p)%pol = p.
Proof.
intros (la, lapr).
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, Nat.sub_0_r, List.app_nil_r.
rewrite List_map2_rngl_add_0_l.
now apply has_polyn_prop_lap_norm.
Qed.

Theorem polyn_mul_assoc : ∀ p1 p2 p3,
  (p1 * (p2 * p3))%pol = ((p1 * p2) * p3) %pol.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
unfold "*"%pol.
remember (lap p1) as la.
remember (lap p2) as lb.
remember (lap p3) as lc.
clear p1 Heqla.
clear p2 Heqlb.
clear p3 Heqlc.
unfold polyn_norm at 1 3.
apply eq_polyn_eq; cbn.
rewrite (lap_mul_norm_idemp_l Hos Hed).
rewrite (lap_mul_norm_idemp_r Hos Hed).
now rewrite lap_mul_assoc.
Qed.

Theorem polyn_mul_1_l : ∀ p, (1 * p)%pol = p.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros (la, lapr).
unfold "*"%pol.
unfold polyn_one.
apply eq_polyn_eq; cbn.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  rewrite (rngl_characteristic_1 Hos Hch 1), (rngl_eqb_refl Heo); cbn.
  apply Bool.orb_true_iff in lapr.
  destruct lapr as [lapr| lapr]; [ now apply is_empty_list_empty in lapr | ].
  apply (rngl_neqb_neq Heo) in lapr.
  exfalso; apply lapr.
  apply (rngl_characteristic_1 Hos Hch).
}
apply (rngl_1_neq_0_iff), (rngl_eqb_neq Heo) in Hch; rewrite Hch.
cbn - [ lap_mul ].
rewrite (lap_mul_1_l Hos).
now apply (has_polyn_prop_lap_norm Hed).
Qed.

Theorem polyn_mul_add_distr_l : ∀ pa pb pc,
  (pa * (pb + pc))%pol = (pa * pb + pa * pc)%pol.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, fold_lap_add.
rewrite (lap_mul_norm_idemp_r Hos Hed).
rewrite (lap_add_norm_idemp_l Heo).
rewrite (lap_add_norm_idemp_r Heo).
f_equal.
now rewrite lap_mul_add_distr_l.
Qed.

Theorem polyn_mul_add_distr_r :
  ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
apply eq_polyn_eq; cbn.
rewrite fold_lap_norm, fold_lap_add.
rewrite (lap_mul_norm_idemp_l Hos Hed).
rewrite (lap_add_norm_idemp_l Heo).
rewrite (lap_add_norm_idemp_r Heo).
f_equal.
now rewrite lap_mul_add_distr_r.
Qed.

Theorem polyn_opt_mul_comm :
  if rngl_mul_is_comm T then ∀ a b : polyn T, (a * b)%pol = (b * a)%pol
  else not_applicable.
Proof.
remember (rngl_mul_is_comm T) as ic eqn:Hic; symmetry in Hic.
destruct ic; [ | easy ].
intros.
apply eq_polyn_eq; cbn.
now rewrite (lap_mul_comm Hic).
Qed.

(* optional right multiplication by 1; not required if multiplication
   is commutative *)

Theorem polyn_mul_1_r : ∀ a : polyn T, (a * 1)%pol = a.
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
apply eq_polyn_eq; cbn.
unfold polyn_one.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hch| Hch]. {
  destruct a as (la, pa); cbn.
  apply Bool.orb_true_iff in pa.
  destruct pa as [pa| pa]. {
    now apply is_empty_list_empty in pa; subst la.
  }
  apply (rngl_neqb_neq Heo) in pa.
  exfalso; apply pa.
  apply (rngl_characteristic_1 Hos Hch).
}
apply (rngl_1_neq_0_iff), (rngl_eqb_neq Heo) in Hch; rewrite Hch.
cbn - [ lap_mul ].
rewrite (lap_mul_1_r Hos).
apply (has_polyn_prop_lap_norm Hed).
now destruct a.
Qed.

Theorem polyn_opt_mul_1_r :
  if rngl_mul_is_comm T then not_applicable
  else ∀ a : polyn T, (a * 1)%pol = a.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
now apply polyn_mul_1_r.
Qed.

(* optional right distributivity; not required if multiplication
   is commutative *)

Theorem polyn_opt_mul_add_distr_r :
   if rngl_mul_is_comm T then not_applicable
   else ∀ a b c : polyn T, ((a + b) * c)%pol = (a * c + b * c)%pol.
Proof.
destruct rngl_mul_is_comm; [ easy | ].
apply polyn_mul_add_distr_r.
Qed.

Theorem polyn_add_opp_diag_l :
  rngl_has_opp T = true
  → ∀ a : polyn T, (- a + a)%pol = 0%pol.
Proof.
intros Hop.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros.
apply eq_polyn_eq.
destruct a as (la, Ha); cbn.
rewrite fold_lap_add.
do 2 rewrite fold_lap_norm.
rewrite (lap_add_norm_idemp_l Heo).
now apply lap_norm_add_opp_diag_l.
Qed.

Theorem polyn_opt_add_opp_diag_l :
  let rop := polyn_ring_like_op in
  if rngl_has_opp (polyn T) then ∀ a : polyn T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
intros rop; subst rop.
remember (rngl_has_opp (polyn T)) as op eqn:Hop; symmetry in Hop.
intros.
destruct op; [ | easy ].
intros a.
unfold rngl_opp; cbn.
unfold polyn_opt_opp_or_psub.
specialize polyn_add_opp_diag_l as add_opp_diag_l.
unfold rngl_has_opp in Hop, add_opp_diag_l.
cbn in Hop, add_opp_diag_l.
unfold polyn_opt_opp_or_psub in Hop, add_opp_diag_l.
destruct rngl_opt_opp_or_psub as [opp| ]; [ | easy ].
destruct opp as [opp| ]; [ | easy ].
now apply add_opp_diag_l.
Qed.

Theorem polyn_opt_has_no_inv : ∀ P,
  let rop := polyn_ring_like_op in
  if rngl_has_inv (polyn T) then P
  else not_applicable.
Proof.
intros.
progress unfold rngl_has_inv; cbn.
progress unfold polyn_opt_inv_or_pdiv.
destruct (Sumbool.sumbool_of_bool (rngl_mul_is_comm T)) as [Hic| Hic];
  [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_opp T)) as [Hop| Hop]; [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)); [ | easy ].
now destruct rngl_opt_inv_or_pdiv.
Qed.

Theorem polyn_opt_has_no_inv_and : ∀ e P,
  let rop := polyn_ring_like_op in
  if (rngl_has_inv (polyn T) && e)%bool then P
  else not_applicable.
Proof.
intros.
progress unfold rngl_has_inv; cbn.
progress unfold polyn_opt_inv_or_pdiv.
destruct (Sumbool.sumbool_of_bool (rngl_mul_is_comm T)); [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_opp T)); [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)); [ | easy ].
now destruct rngl_opt_inv_or_pdiv.
Qed.

Notation "a / b" := (polyn_pdiv a b) : polyn_scope.

Theorem polyn_mul_div :
  rngl_mul_is_comm T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  ∀ a b,
  b ≠ 0%pol
  → (a * b / b)%pol = a.
Proof.
intros Hco Hop Hiv * Hbz.
destruct a as (la, pa).
destruct b as (lb, pb).
move lb before la.
unfold polyn_mul.
assert (H : lb ≠ []). {
  intros H; apply Hbz.
  now apply eq_polyn_eq.
}
clear Hbz; rename H into Hbz.
apply eq_polyn_eq; cbn.
unfold polyn_norm; cbn.
unfold polyn_pdiv; cbn.
destruct (Sumbool.sumbool_of_bool _) as [Hiv2| Hiv2]. {
  cbn; rewrite (lap_norm_mul Hos Hed Hiv _ _ pa pb).
  now apply lap_mul_div.
}
congruence.
Qed.

Theorem polyn_opt_mul_div :
  let _ := polyn_ring_like_op in
  if rngl_has_pdiv (polyn T) then ∀ a b, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof.
intros rop; subst rop.
progress unfold rngl_has_pdiv; cbn.
progress unfold polyn_opt_inv_or_pdiv.
destruct (Sumbool.sumbool_of_bool (rngl_mul_is_comm T)) as [Hco| ];
  [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_opp T)) as [Hop| ]; [ | easy ].
destruct (Sumbool.sumbool_of_bool (rngl_has_inv T)) as [Hiv| ]; [ | easy ].
remember (rngl_opt_inv_or_pdiv T) as iq eqn:Hiq; symmetry in Hiq.
destruct iq as [inv| ]; [ | easy ].
intros a b Hbz.
progress unfold rngl_div, rngl_has_inv; cbn.
progress unfold polyn_opt_inv_or_pdiv.
progress unfold rngl_has_pdiv, polyn_opt_inv_or_pdiv; cbn.
progress unfold rngl_pdiv; cbn.
progress unfold polyn_opt_inv_or_pdiv.
rewrite Hco, Hop, Hiv, Hiq.
destruct (Sumbool.sumbool_of_bool true); [ | easy ].
now apply polyn_mul_div.
Qed.

Theorem lap_polyn_rngl_of_nat_char_0 :
  let _ := polyn_ring_like_op in
  rngl_characteristic T = 0
  → ∀ i, i ≠ 0 → lap (rngl_of_nat i) = [rngl_of_nat i].
Proof.
intros rop Hch * Hiz; cbn.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
subst rop.
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction i; [ easy | clear Hiz; cbn ].
assert (H : rngl_characteristic T ≠ 1) by now rewrite Hch.
specialize (proj1 (rngl_1_neq_0_iff) H) as H1; clear H.
apply (rngl_eqb_neq Heo) in H1; rewrite H1.
cbn - [ lap_add ].
destruct i; [ now cbn; rewrite rngl_add_0_r, H1 | ].
rewrite IHi; [ cbn | easy ].
rewrite if_bool_if_dec.
destruct (Sumbool.sumbool_of_bool _) as [H11| H11]; [ | easy ].
clear IHi; exfalso.
apply (rngl_eqb_eq Heo) in H11.
specialize (rngl_characteristic_0 Hch) as H2.
now specialize (H2 (S i)).
Qed.

Theorem lap_polyn_rngl_of_nat_2 :
  let rop := polyn_ring_like_op in
  ∀ i, 0 < i < rngl_characteristic T
  → lap (rngl_of_nat i) = [rngl_of_nat i].
Proof.
specialize (rngl_has_eq_dec_or_is_ordered_l Hed) as Heo.
intros * Hi; cbn.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  flia Hi Hc1.
}
specialize (proj1 (rngl_1_neq_0_iff) Hc1) as H11.
specialize rngl_opt_characteristic_prop as Hch.
rewrite if_bool_if_dec in Hch.
destruct (Sumbool.sumbool_of_bool _) as [Hchz| Hchz]. {
  apply Nat.eqb_eq in Hchz.
  now rewrite Hchz in Hi.
}
clear Hchz.
destruct Hch as (Hbef, Hch).
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat.
induction i; [ easy | cbn ].
cbn in IHi.
remember (lap (List.fold_right polyn_add 0%pol (List.repeat 1%pol i)))
  as la eqn:Hla.
symmetry in Hla.
apply (rngl_eqb_neq Heo) in H11; rewrite H11.
cbn - [ lap_add rngl_mul_nat ].
destruct la as [| a]. {
  cbn.
  rewrite rngl_add_0_r, H11.
  cbn; f_equal; symmetry.
  rewrite <- rngl_add_0_r.
  apply rngl_add_compat_l.
  destruct i; [ easy | ].
  assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
  now specialize (IHi H).
}
symmetry; apply List_rev_symm; symmetry; cbn.
rewrite strip_0s_app.
remember (strip_0s (List.rev la)) as lb eqn:Hlb; symmetry in Hlb.
destruct lb as [| b]. {
  cbn.
  rewrite if_bool_if_dec.
  destruct (Sumbool.sumbool_of_bool _) as [H12| H12]. {
    exfalso; apply (rngl_eqb_eq Heo) in H12.
    destruct i; [ easy | ].
    assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
    specialize (IHi H); clear H.
    injection IHi; clear IHi; intros; subst a la.
    clear Hlb.
    cbn - [ lap_add ] in Hla.
    rewrite H11 in Hla.
    cbn - [ lap_add ] in Hla.
    remember (lap (List.fold_right polyn_add 0%pol _)) as lb eqn:Hlb.
    symmetry in Hlb.
    destruct lb as [| b]; cbn in Hla. {
      rewrite rngl_add_0_r, H11 in Hla.
      cbn in Hla.
      injection Hla; clear Hla; intros Hla; symmetry in Hla.
      rewrite <- rngl_add_0_r in Hla.
      apply (rngl_add_cancel_l Hos) in Hla.
      cbn in H12.
      rewrite Hla in H12.
      apply (Hbef 2); [ flia Hi | easy ].
    }
    now specialize (Hbef (S (S i)) Hi) as H1.
  }
  rewrite Nat.sub_0_r, List.app_nil_r, List_map2_rngl_add_0_l, Hlb.
  f_equal.
  apply rngl_add_compat_l; symmetry.
  destruct i; [ easy | ].
  assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
  specialize (IHi H).
  now injection IHi; clear IHi; intros; subst a la.
}
exfalso.
destruct i; [ easy | ].
assert (H : 0 < S i < rngl_characteristic T) by flia Hi.
specialize (IHi H); clear H.
now injection IHi; clear IHi; intros; subst a la.
Qed.

Let Heo := rngl_has_eq_dec_or_is_ordered_l Hed.

Theorem lap_polyn_rngl_of_nat :
  let lop := lap_ring_like_op Heo in
  let rop := polyn_ring_like_op in
  ∀ n, lap (rngl_of_nat n) = lap_norm (rngl_of_nat n).
Proof.
intros; cbn.
progress unfold rngl_of_nat.
progress unfold rngl_mul_nat.
progress unfold mul_nat; cbn.
induction n; [ easy | ].
cbn - [ lap_add ].
rewrite IHn.
rewrite fold_lap_norm.
rewrite (lap_add_norm_idemp_r Heo).
specialize (proj1 (rngl_1_neq_0_iff)) as H1.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H2.
  rewrite (H2 1%L), (rngl_eqb_refl Heo).
  progress replace (List.rev []) with ([] : list T) by easy.
  rewrite <- (lap_add_norm_idemp_l Heo [0%L]).
  progress replace (lap_norm [0%L]) with ([] : list T). 2: {
    now cbn; rewrite rngl_eqb_refl.
  }  
  easy.
}
specialize (H1 Hc1).
now apply (rngl_eqb_neq Heo) in H1; rewrite H1.
Qed.

Theorem polyn_integral :
  let rop := polyn_ring_like_op in
  ∀ a b : polyn T,
  (a * b)%L = 0%L
  → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
now right; right; left.
Qed.

Theorem polyn_characteristic_prop : let rop := polyn_ring_like_op in
  if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
  else
    (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L)
     ∧ rngl_of_nat (rngl_characteristic T) = 0%L.
Proof.
intros rop; subst rop.
set (rol := lap_ring_like_op Heo).
cbn - [ rngl_mul_nat ].
specialize rngl_opt_characteristic_prop as H1.
rewrite if_eqb_eq_dec in H1 |-*.
destruct (Nat.eq_dec (rngl_characteristic T) 0) as [Hcz| Hcz]. {
  intros i.
  specialize (H1 i) as H.
  intros Hi; apply H; clear H.
  apply (f_equal lap) in Hi.
  now rewrite lap_polyn_rngl_of_nat_char_0 in Hi.
} {
  destruct H1 as (Hbef, Hch).
  split. {
    intros i Hi; cbn.
    specialize (Hbef _ Hi) as H1.
    intros H; apply H1; clear H1; rename H into H1.
    generalize H1; intros H2.
    apply (f_equal lap) in H2; cbn in H2.
    now rewrite lap_polyn_rngl_of_nat_2 in H2.
  }
  apply eq_polyn_eq; cbn.
  rewrite lap_polyn_rngl_of_nat.
  rewrite (lap_rngl_of_nat Hed).
  destruct (Nat.eq_dec _ _) as [Hc1| Hc1]; [ easy | ].
  rewrite Hch; cbn.
  now rewrite (rngl_eqb_refl Heo).
}
Qed.

(* *)

Theorem rngl_has_opp_rngl_polyn_has_opp :
  let rop := polyn_ring_like_op in
  rngl_has_opp T = rngl_has_opp (polyn T).
Proof.
intros.
unfold rngl_has_opp; cbn.
unfold polyn_opt_opp_or_psub.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem rngl_has_psub_rngl_polyn_has_psub :
  let rop := polyn_ring_like_op in
  rngl_has_psub T = rngl_has_psub (polyn T).
Proof.
intros.
unfold rngl_has_psub; cbn.
unfold polyn_opt_opp_or_psub.
destruct rngl_opt_opp_or_psub as [os| ]; [ | easy ].
now destruct os.
Qed.

Theorem polyn_opt_add_sub :
  let rop := polyn_ring_like_op in
  if rngl_has_psub (polyn T) then ∀ a b : polyn T, (a + b - b)%L = a
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (polyn T)) as su eqn:Hsup; symmetry in Hsup.
destruct su; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsup) as Hopp.
specialize rngl_has_opp_rngl_polyn_has_opp as Hop; cbn in Hop.
specialize rngl_has_psub_rngl_polyn_has_psub as Hsu; cbn in Hsu.
fold rop in Hop; rewrite Hopp in Hop.
fold rop in Hsu; rewrite Hsup in Hsu.
intros.
apply eq_polyn_eq; cbn.
unfold rngl_sub.
rewrite Hopp, Hsup.
unfold rngl_psub; cbn.
unfold polyn_opt_opp_or_psub.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]. 2: {
  unfold rngl_has_opp_or_psub in Hos.
  clear - Hos Hos'.
  now rewrite Hos' in Hos.
}
destruct os as [opp| psub]. {
  unfold rngl_has_opp in Hop; cbn in Hop.
  unfold polyn_opt_opp_or_psub in Hop.
  exfalso; clear - Hop Hos'.
  now rewrite Hos' in Hop.
}
unfold polyn_psub.
destruct a as (la, pa).
destruct b as (lb, pb).
move lb before la.
cbn - [ lap_norm lap_add lap_psub ].
rewrite (lap_psub_norm_idemp_l Hed Hsu).
specialize (lap_opt_add_sub Hos Hsu) as H2.
unfold lap_sub in H2.
rewrite Hop, Hsu in H2.
rewrite H2.
rewrite (lap_norm_app_0_r Heo); [ | intros; apply List.nth_repeat ].
now apply (has_polyn_prop_lap_norm Hed).
Qed.

(* *)

Theorem polyn_opt_sub_add_distr :
  let rop := polyn_ring_like_op in
  if rngl_has_psub (polyn T) then
    ∀ a b c : polyn T, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (polyn T)) as su eqn:Hsup; symmetry in Hsup.
destruct su; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsup) as Hopp.
specialize rngl_has_opp_rngl_polyn_has_opp as Hop; cbn in Hop.
specialize rngl_has_psub_rngl_polyn_has_psub as Hsu; cbn in Hsu.
fold rop in Hop; rewrite Hopp in Hop.
fold rop in Hsu; rewrite Hsup in Hsu.
intros.
apply eq_polyn_eq; cbn.
unfold rngl_sub.
rewrite Hopp, Hsup.
unfold rngl_psub; cbn.
unfold polyn_opt_opp_or_psub.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]. 2: {
  unfold rngl_has_opp_or_psub in Hos.
  clear - Hos Hos'.
  now rewrite Hos' in Hos.
}
destruct os as [opp| psub]. {
  unfold rngl_has_opp in Hop; cbn in Hop.
  unfold polyn_opt_opp_or_psub in Hop.
  exfalso; clear - Hop Hos'.
  now rewrite Hos' in Hop.
}
unfold polyn_psub.
destruct a as (la, pa).
destruct b as (lb, pb).
destruct c as (lc, pc).
move lb before la; move lc before lb.
cbn - [ lap_norm lap_add lap_psub ].
rewrite (lap_psub_norm_idemp_l Hed Hsu).
rewrite (lap_psub_norm_idemp_r Hed Hsu).
specialize (lap_opt_sub_add_distr Hos Hsu) as H1.
unfold lap_sub in H1.
rewrite Hop, Hsu in H1.
f_equal; apply H1.
Qed.

Theorem polyn_opt_sub_0_l :
  let rop := polyn_ring_like_op in
  if rngl_has_psub (polyn T) then ∀ a : polyn T, (0 - a)%L = 0%L
  else not_applicable.
Proof.
intros.
remember (rngl_has_psub (polyn T)) as su eqn:Hsup; symmetry in Hsup.
destruct su; [ | easy ].
specialize (rngl_has_psub_has_no_opp Hsup) as Hopp.
specialize rngl_has_opp_rngl_polyn_has_opp as Hop; cbn in Hop.
specialize rngl_has_psub_rngl_polyn_has_psub as Hsu; cbn in Hsu.
fold rop in Hop; rewrite Hopp in Hop.
fold rop in Hsu; rewrite Hsup in Hsu.
intros.
apply eq_polyn_eq; cbn.
unfold rngl_sub.
rewrite Hopp, Hsup.
unfold rngl_psub; cbn.
unfold polyn_opt_opp_or_psub.
remember (rngl_opt_opp_or_psub T) as os eqn:Hos'; symmetry in Hos'.
destruct os as [os| ]. 2: {
  unfold rngl_has_opp_or_psub in Hos.
  clear - Hos Hos'.
  now rewrite Hos' in Hos.
}
destruct os as [opp| psub]. {
  unfold rngl_has_opp in Hop; cbn in Hop.
  unfold polyn_opt_opp_or_psub in Hop.
  exfalso; clear - Hop Hos'.
  now rewrite Hos' in Hop.
}
unfold polyn_psub.
destruct a as (la, pa).
cbn.
rewrite List.app_nil_r, Nat.sub_0_r.
rewrite List_rev_map2; [ | now rewrite List.repeat_length ].
rewrite List.rev_repeat.
(* lemma *)
apply List.rev_inj; cbn.
rewrite List.rev_involutive.
(* end lemma *)
remember (List.rev la) as lb eqn:Hlb.
apply (f_equal (@List.rev _)) in Hlb.
rewrite List.rev_involutive in Hlb.
subst la.
rewrite List.length_rev.
rename lb into la.
clear pa.
induction la as [| a]; [ easy | cbn ].
rewrite IHla.
remember (rngl_psub 0 a =? 0)%L as za eqn:Hza.
symmetry in Hza.
destruct za; [ easy | exfalso ].
apply (rngl_eqb_neq Heo) in Hza.
apply Hza; clear Hza.
specialize rngl_opt_sub_0_l as H1.
progress unfold rngl_sub in H1.
rewrite Hop, Hsu in H1.
apply H1.
Qed.

Definition polyn_ring_like_prop : ring_like_prop (polyn T) :=
  {| rngl_mul_is_comm := rngl_mul_is_comm T;
     rngl_is_archimedean := false;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := polyn_add_comm;
     rngl_add_assoc := polyn_add_assoc;
     rngl_add_0_l := polyn_add_0_l;
     rngl_mul_assoc := polyn_mul_assoc;
     rngl_mul_1_l := polyn_mul_1_l;
     rngl_mul_add_distr_l := polyn_mul_add_distr_l;
     rngl_opt_mul_comm := polyn_opt_mul_comm;
     rngl_opt_mul_1_r := polyn_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := polyn_opt_mul_add_distr_r;
     rngl_opt_add_opp_diag_l := polyn_opt_add_opp_diag_l;
     rngl_opt_add_sub := polyn_opt_add_sub;
     rngl_opt_sub_add_distr := polyn_opt_sub_add_distr;
     rngl_opt_sub_0_l := polyn_opt_sub_0_l;
     rngl_opt_mul_inv_diag_l := polyn_opt_has_no_inv _;
     rngl_opt_mul_inv_diag_r := polyn_opt_has_no_inv_and _ _;
     rngl_opt_mul_div := polyn_opt_mul_div;
     rngl_opt_integral := polyn_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := polyn_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

End a.
