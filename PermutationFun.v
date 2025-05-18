(* Testing if a list is a permutation of another one *)

Set Nested Proofs Allowed.

From Stdlib Require Import Utf8 Arith.
From Stdlib Require FinFun.
Import Init.Nat.
Import List.ListNotations.

Require Import Misc Utils.

Definition reflexive {A} (rel : A → A → bool) :=
  ∀ a, rel a a = true.

Fixpoint is_permutation {A} (eqb : A → A → bool) (la lb : list A) :=
  match la with
  | [] => match lb with [] => true | _ => false end
  | a :: la' =>
      match List_extract (eqb a) lb with
      | None => false
      | Some (bef, _, aft) => is_permutation eqb la' (bef ++ aft)
      end
  end.

Definition permutation {A} (eqb : A → _) la lb :=
  is_permutation eqb la lb = true.

Theorem permutation_cons_l_iff : ∀ A (eqb : A → _) a la lb,
  permutation eqb (a :: la) lb
  ↔ match List_extract (eqb a) lb with
     | Some (bef, _, aft) => permutation eqb la (bef ++ aft)
     | None => False
     end.
Proof.
intros.
unfold permutation; cbn.
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl.
now destruct lxl as [((bef, x), aft)| ].
Qed.

(* *)

Theorem permutation_cons_inv : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb a,
  permutation eqb (a :: la) (a :: lb) → permutation eqb la lb.
Proof.
intros * Heqb * Hpab.
apply permutation_cons_l_iff in Hpab.
cbn in Hpab.
now rewrite (equality_refl Heqb) in Hpab.
Qed.

Theorem permutation_app_inv_aux : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb lc ld a,
  a ∉ la
  → a ∉ lc
  → permutation eqb (la ++ a :: lb) (lc ++ a :: ld)
  → permutation eqb (la ++ lb) (lc ++ ld).
Proof.
intros * Heqb * Hala Halc Hp.
revert lb lc ld a Hp Hala Halc.
induction la as [| b]; intros. {
  clear Hala; cbn in Hp |-*.
  apply permutation_cons_l_iff in Hp.
  remember (List_extract (eqb a) (lc ++ a :: ld)) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply List_extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply List.app_eq_app in Hlb.
  destruct Hlb as (l & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst lc.
    destruct l as [| b]; cbn in H2. {
      injection H2; clear H2; intros; subst aft.
      now rewrite List.app_nil_r.
    }
    injection H2; clear H2; intros H2 H; subst b.
    exfalso; apply Halc.
    now apply List.in_or_app; right; left.
  }
  subst bef.
  destruct l as [| b]; cbn in H2. {
    injection H2; clear H2; intros; subst aft.
    now rewrite List.app_nil_r in Hp.
  }
  injection H2; clear H2; intros H2 H; subst b.
  specialize (Hbef a) as H1.
  assert (H : a ∈ lc ++ a :: l) by now apply List.in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
cbn in Hp |-*.
apply permutation_cons_l_iff in Hp.
remember (List_extract (eqb b) (lc ++ a :: ld)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply List.app_eq_app in Hlb.
destruct Hlb as (l & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst lc.
  destruct l as [| c]; cbn in H2. {
    injection H2; clear H2; intros; subst aft b.
    now exfalso; apply Hala; left.
  }
  injection H2; clear H2; intros H2 H; subst c aft.
  rewrite <- List.app_assoc.
  apply permutation_cons_l_iff.
  remember (List_extract (eqb b) (bef ++ (b :: l) ++ ld)) as lxl eqn:Hlxl.
  symmetry in Hlxl.
  destruct lxl as [((bef', x), aft')| ]. 2: {
    specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
    specialize (H1 b).
    assert (H : b ∈ bef ++ (b :: l) ++ ld). {
      now apply List.in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  apply List_extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef' & H & Hlb).
  apply Heqb in H; subst x.
  apply List.app_eq_app in Hlb.
  destruct Hlb as (l' & Hlb).
  destruct Hlb as [(H1, H2)| (H1, H2)]. {
    subst bef.
    destruct l' as [| c]; cbn in H2. 2: {
      injection H2; clear H2; intros H2 H; subst c aft'.
      specialize (Hbef b) as H1.
      assert (H : b ∈ bef' ++ b :: l'). {
        now apply List.in_or_app; right; left.
      }
      specialize (H1 H); clear H.
      now rewrite (equality_refl Heqb) in H1.
    }
    injection H2; clear H2; intros; subst aft'.
    rewrite List.app_nil_r in Hp, Halc.
    rewrite List.app_assoc.
    apply IHla with (a := a); cycle 1. {
      now intros H; apply Hala; right.
    } {
      intros H; apply Halc.
      apply List.in_app_or in H.
      apply List.in_or_app.
      now destruct H as [H| H]; [ left | right; right ].
    }
    now rewrite <- List.app_assoc.
  }
  subst bef'.
  destruct l' as [| c]; cbn in H2. 2: {
    injection H2; clear H2; intros H2 H; subst c.
    specialize (Hbef' b) as H1.
    assert (H : b ∈ bef ++ b :: l'). {
      now apply List.in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  injection H2; clear H2; intros H2; subst aft'.
  rewrite List.app_nil_r in Hbef' |-*.
  rewrite List.app_assoc.
  apply IHla with (a := a); cycle 1. {
    now intros H; apply Hala; right.
  } {
    intros H; apply Halc.
    apply List.in_app_or in H.
    apply List.in_or_app.
    now destruct H as [H| H]; [ left | right; right ].
  }
  now rewrite <- List.app_assoc.
}
subst bef.
apply permutation_cons_l_iff.
remember (List_extract (eqb b) (lc ++ ld)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft')| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 b).
  assert (H : b ∈ lc ++ ld). {
    apply List.in_or_app; right.
    specialize (List.in_elt b l aft) as H3.
    rewrite <- H2 in H3.
    destruct H3 as [H3| H3]; [ subst b | easy ].
    now exfalso; apply Hala; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb).
apply Heqb in H; subst x.
apply List.app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H3)| (H1, H3)]. 2: {
  subst bef ld.
  rewrite List.app_comm_cons in H2.
  apply List.app_eq_app in H2.
  destruct H2 as (l'' & H2).
  destruct H2 as [(H2, H4)| (H2, H4)]. {
    destruct l'' as [| c]. {
      rewrite List.app_nil_r in H2; subst l; cbn in H4.
      injection H4; clear H4; intros; subst aft'.
      rewrite <- List.app_assoc.
      apply IHla with (a := a); [ | | easy ]. 2: {
        now intros H; apply Hala; right.
      }
      now rewrite List.app_comm_cons, List.app_assoc.
    }
    cbn in H4.
    injection H4; clear H4; intros H4 H; subst c aft.
    specialize (Hbef' b) as H1.
    assert (H : b ∈ lc ++ l'). {
      apply List.in_or_app; right.
      specialize (List.in_elt b l l'') as H3.
      rewrite <- H2 in H3.
      destruct H3 as [H3| H3]; [ subst b | easy ].
      now exfalso; apply Hala; left.
    }
    specialize (H1 H); clear H.
    now rewrite (equality_refl Heqb) in H1.
  }
  subst l.
  destruct l'' as [| c]. {
    rewrite List.app_nil_r in Hp.
    cbn in H4.
    injection H4; clear H4; intros; subst aft'.
    rewrite <- List.app_assoc.
    apply IHla with (a := a); [ | | easy ]. 2: {
      now intros H; apply Hala; right.
    }
    now rewrite List.app_comm_cons, List.app_assoc.
  }
  cbn in H4.
  injection H4; clear H4; intros H4 H; subst c aft'.
  specialize (Hbef b) as H1.
  assert (H : b ∈ lc ++ (a :: l') ++ b :: l''). {
    apply List.in_or_app; right.
    now apply List.in_or_app; right; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
subst lc.
move H2 before H3.
destruct l as [| c]. {
  cbn in H2.
  injection H2; clear H2; intros; subst b aft.
  now exfalso; apply Hala; left.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst c ld.
destruct l' as [| c]. {
  cbn in H3.
  rewrite List.app_nil_r in Hp, Hbef, Halc.
  destruct l as [| c]. {
    cbn in H3.
    injection H3; clear H3; intros; subst aft'.
    rewrite <- List.app_assoc in Hp; cbn in Hp.
    apply IHla with (a := a); [ easy | | easy ].
    now intros H; apply Hala; right.
  }
  cbn in H3.
  injection H3; clear H3; intros H3 H; subst c aft'.
  specialize (Hbef b) as H1.
  assert (H : b ∈ bef ++ a :: b :: l). {
    now apply List.in_or_app; right; right; left.
  }
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
cbn in H3.
injection H3; clear H3; intros H3 H; subst c.
specialize (Hbef b) as H1.
assert (H : b ∈ (bef ++ b :: l') ++ a :: l). {
  apply List.in_or_app; left.
  now apply List.in_or_app; right; left.
}
specialize (H1 H); clear H.
now rewrite (equality_refl Heqb) in H1.
Qed.

(* *)

Theorem permutation_refl : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l, permutation eqb l l.
Proof.
intros * Heqb *.
induction l as [| a]; [ easy | cbn ].
apply permutation_cons_l_iff; cbn.
now rewrite (equality_refl Heqb).
Qed.

Theorem permutation_in_iff : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ [la lb], permutation eqb la lb → ∀ a, a ∈ la ↔ a ∈ lb.
Proof.
intros * Heqb * Hpab a.
revert a lb Hpab.
induction la as [| b]; intros; [ now destruct lb | ].
apply permutation_cons_l_iff in Hpab.
remember (List_extract (eqb b) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x lb.
split. {
  intros Hla.
  destruct Hla as [Hla| Hla]. {
    now subst b; apply List.in_or_app; right; left.
  }
  assert (Ha : a ∈ bef ++ aft) by now apply IHla.
  apply List.in_app_or in Ha.
  apply List.in_or_app.
  now destruct Ha; [ left | right; right ].
} {
  intros Ha.
  apply List.in_app_or in Ha.
  destruct Ha as [Ha| Ha]. 2: {
    destruct Ha as [Ha| Ha]; [ now left | right ].
    apply (IHla a (bef ++ aft) Hpab).
    now apply List.in_or_app; right.
  }
  right; apply (IHla a (bef ++ aft) Hpab).
  now apply List.in_or_app; left.
}
Qed.

Theorem permutation_sym : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb, permutation eqb la lb → permutation eqb lb la.
Proof.
intros * Heqb * Hpab.
revert la Hpab.
induction lb as [| b]; intros; [ now destruct la | cbn ].
apply permutation_cons_l_iff.
remember (List_extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1; clear Hlxl.
  specialize (permutation_in_iff Heqb Hpab) as H2.
  specialize (proj2 (H2 b) (or_introl eq_refl)) as H3.
  specialize (H1 _ H3).
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (H1 & H2 & H3).
apply Heqb in H2; subst x.
subst la.
apply IHlb.
replace lb with ([] ++ lb) by easy.
apply permutation_app_inv_aux with (a := b); [ easy | | easy | easy ].
intros H; specialize (H1 _ H).
now rewrite (equality_refl Heqb) in H1.
Qed.

Theorem permutation_nil_l : ∀ {A} {eqb : A → _} l,
  permutation eqb [] l → l = [].
Proof. now intros; destruct l. Qed.

Theorem permutation_nil_r : ∀ {A} {eqb : A → _} l,
  permutation eqb l [] → l = [].
Proof. now intros; destruct l. Qed.

Theorem permutation_trans : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb lc,
  permutation eqb la lb → permutation eqb lb lc → permutation eqb la lc.
Proof.
intros * Heqb * Hpab Hpbc.
revert lb lc Hpab Hpbc.
induction la as [| a]; intros; cbn. {
  now cbn in Hpab, Hpbc; destruct lb.
}
cbn in Hpab.
apply permutation_cons_l_iff.
remember (List_extract (eqb a) lc) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  apply permutation_cons_l_iff in Hpab.
  remember (List_extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft) | ]; [ | easy ].
  apply List_extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlb).
  apply Heqb in H; subst x.
  apply (permutation_sym Heqb) in Hpbc.
  specialize (permutation_in_iff Heqb Hpbc) as H2.
  specialize (proj2 (H2 a)) as H3.
  assert (H : a ∈ lb) by now subst lb; apply List.in_or_app; right; left.
  specialize (H3 H); clear H.
  specialize (H1 _ H3).
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply permutation_cons_l_iff in Hpab.
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst lb lc.
apply IHla with (lb := bef' ++ aft'); [ easy | ].
assert (Hanb : a ∉ bef). {
  intros H; apply Hbef in H.
  now rewrite (equality_refl Heqb) in H.
}
assert (Hanb' : a ∉ bef'). {
  intros H; apply Hbef' in H.
  now rewrite (equality_refl Heqb) in H.
}
clear Hbef Hbef'.
clear la IHla Hpab.
now apply permutation_app_inv_aux in Hpbc.
Qed.

(* theorems equivalent to Permutation type *)

Theorem permutation_nil_nil : ∀ {A} {eqb : A → _}, permutation eqb [] [].
Proof. easy. Qed.

Theorem permutation_skip : ∀ {A} {eqb : A → _},
  reflexive eqb
  → ∀ a la lb, permutation eqb la lb → permutation eqb (a :: la) (a :: lb).
Proof.
intros * Heqb * Hpab; cbn.
apply permutation_cons_l_iff; cbn.
now rewrite Heqb.
Qed.

Theorem permutation_swap : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ a b la, permutation eqb (b :: a :: la) (a :: b :: la).
Proof.
intros * Heqb *.
apply permutation_cons_l_iff; cbn.
rewrite (equality_refl Heqb).
remember (eqb b a) as ba eqn:Hba; symmetry in Hba.
destruct ba; [ | now apply permutation_refl ].
apply Heqb in Hba; subst b.
now apply permutation_refl.
Qed.

(* *)

Theorem permutation_add_inv : ∀ {A} {eqb : A → _} (Heqb : equality eqb),
  ∀ a la lb,
  permutation eqb la lb
  → ∀ lc ld,
  permutation eqb (a :: lc) la
  → permutation eqb (a :: ld) lb
  → permutation eqb lc ld.
Proof.
intros * Heqb * Hab * Hc Hd.
apply permutation_cons_l_iff in Hc, Hd.
remember (List_extract (eqb a) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((befa, x), afta)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (H1 & H & H3).
apply Heqb in H; subst x la.
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((befb, x), aftb)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (H2 & H & H4).
apply Heqb in H; subst x lb.
move H2 before H1.
apply (permutation_app_inv_aux Heqb) in Hab; cycle 1. {
  intros H; specialize (H1 _ H).
  now rewrite (equality_refl Heqb) in H1.
} {
  intros H; specialize (H2 _ H).
  now rewrite (equality_refl Heqb) in H2.
}
apply (permutation_trans Heqb) with (lb := befa ++ afta); [ easy | ].
apply (permutation_trans Heqb) with (lb := befb ++ aftb); [ easy | ].
now apply (permutation_sym Heqb).
Qed.

(* *)

Theorem permutation_app_tail : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l l' tl,
  permutation eqb l l' → permutation eqb (l ++ tl) (l' ++ tl).
Proof.
intros * Heqb * Hll'.
revert l' tl Hll'.
induction l as [| a]; intros. {
  destruct l'; [ apply (permutation_refl Heqb) | easy ].
}
rewrite <- List.app_comm_cons; cbn in Hll' |-*.
apply permutation_cons_l_iff in Hll'.
remember (List_extract (eqb a) l') as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply permutation_cons_l_iff.
remember (List_extract (eqb a) (l' ++ tl)) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1; clear Hlxl.
  specialize (H1 a).
  assert (H : a ∈ l' ++ tl). {
    subst l'.
    apply List.in_or_app; left.
    now apply List.in_or_app; right; left.
  }
  specialize (H1 H).
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb').
apply Heqb in H; subst x.
subst l'.
rewrite <- List.app_assoc in Hlb'; cbn in Hlb'.
apply List.app_eq_app in Hlb'.
destruct Hlb' as (l' & H1).
destruct H1 as [(H1, H2)| (H1, H2)]. {
  subst bef'.
  destruct l' as [| b]. {
    cbn in H2.
    injection H2; clear H2; intros H2; subst aft.
    rewrite List.app_assoc.
    rewrite List.app_nil_r in Hll'.
    now apply IHl.
  }
  cbn in H2.
  injection H2; clear H2; intros H2 H; subst b aft.
  specialize (Hbef a).
  assert (H : a ∈ bef ++ a :: l') by now apply List.in_or_app; right; left.
  specialize (Hbef H); clear H.
  now rewrite (equality_refl Heqb) in Hbef.
}
subst bef.
destruct l' as [| b]. {
  cbn in H2.
  injection H2; clear H2; intros; subst aft.
  rewrite List.app_nil_r, List.app_assoc.
  now apply IHl.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst b.
specialize (Hbef' a).
assert (H : a ∈ bef' ++ a :: l') by now apply List.in_or_app; right; left.
specialize (Hbef' H); clear H.
now rewrite (equality_refl Heqb) in Hbef'.
Qed.

Theorem permutation_app_head : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l tl tl',
  permutation eqb tl tl' → permutation eqb (l ++ tl) (l ++ tl').
Proof.
intros * Heqb * Hll'.
revert tl tl' Hll'.
induction l as [| a]; intros; [ easy | ].
apply permutation_cons_l_iff; cbn.
rewrite (equality_refl Heqb).
now apply IHl.
Qed.

Theorem permutation_app : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l m l' m',
  permutation eqb l l'
  → permutation eqb m m'
  → permutation eqb (l ++ m) (l' ++ m').
Proof.
intros * Heqb * Hll' Hmm'.
apply (permutation_trans Heqb) with (lb := l ++ m'). {
  now apply permutation_app_head.
}
now apply permutation_app_tail.
Qed.

Theorem permutation_cons_append : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l x, permutation eqb (x :: l) (l ++ [x]).
Proof.
intros * Heqb *.
revert x.
induction l as [| a]; intros; [ now apply permutation_refl | cbn ].
eapply (permutation_trans Heqb); [ apply (permutation_swap Heqb) | ].
apply permutation_skip; [ | easy ].
now unfold reflexive; apply equality_refl.
Qed.

Theorem permutation_app_comm : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l l', permutation eqb (l ++ l') (l' ++ l).
Proof.
intros * Heqb *.
remember (length (l ++ l')) as len eqn:Hlen; symmetry in Hlen.
revert l l' Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply List.length_zero_iff_nil in Hlen.
  apply List.app_eq_nil in Hlen.
  destruct Hlen; subst l l'.
  now apply permutation_refl.
}
destruct l as [| a]. {
  rewrite List.app_nil_r.
  now apply permutation_refl.
}
cbn in Hlen; apply Nat.succ_inj in Hlen; cbn.
apply permutation_cons_l_iff.
remember (List_extract (eqb a) (l' ++ a :: l)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ].  2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 a).
  assert (H : a ∈ l' ++ a :: l) by now apply List.in_or_app; right; left.
  specialize (H1 H); clear H.
  now rewrite equality_refl in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
eapply (permutation_trans Heqb). {
  apply IHlen with (m := List.length (l ++ l')); [ | easy ].
  now rewrite Hlen.
}
apply List.app_eq_app in Hlb.
destruct Hlb as (l'' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  rewrite H1, <- List.app_assoc.
  apply (permutation_app_head Heqb).
  destruct l'' as [| x]. {
    cbn in H2.
    injection H2; clear H2; intros; subst aft.
    now apply permutation_refl.
  }
  cbn in H2.
  injection H2; clear H2; intros H2 H; subst x.
  destruct l as [| b]. {
    rewrite List.app_nil_r, H2.
    replace (a :: l'') with ([a] ++ l'') by easy.
    apply IHlen with (m := (List.length ([a] ++ l''))); [ | easy ].
    subst len; cbn.
    apply -> Nat.succ_lt_mono.
    rewrite H1; cbn.
    rewrite List.length_app; cbn.
    flia.
  }
  rewrite H2, List_app_cons, List.app_assoc.
  apply (permutation_sym Heqb).
  do 2 rewrite List_app_cons, List.app_assoc.
  apply (permutation_app_tail Heqb).
  apply (permutation_app_tail Heqb).
  apply IHlen with (m := List.length (l'' ++ [a])); [ | easy ].
  rewrite <- Hlen, H1;cbn.
  do 3 rewrite List.length_app; cbn.
  flia.
}
destruct l'' as [| x]. {
  cbn in H2.
  injection H2; clear H2; intros; subst aft.
  rewrite List.app_nil_r in H1; subst bef.
  now apply permutation_refl.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst x.
rewrite H1, H2.
rewrite List_app_cons.
do 2 rewrite List.app_assoc.
apply (permutation_app_tail Heqb).
rewrite <- List.app_assoc.
apply (permutation_app_head Heqb).
apply IHlen with (m := List.length (l'' ++ [a])); [ | easy ].
rewrite <- Hlen, H2.
do 3 rewrite List.length_app; cbn; flia.
Qed.

Theorem permutation_cons_app : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l l1 l2 a,
  permutation eqb l (l1 ++ l2)
  → permutation eqb (a :: l) (l1 ++ a :: l2).
Proof.
intros * Heqb * H12; cbn.
apply permutation_cons_l_iff.
remember (List_extract (eqb a) (l1 ++ a :: l2)) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  specialize (H1 a).
  rewrite (equality_refl Heqb) in H1.
  apply Bool.diff_true_false, H1.
  now apply List.in_or_app; right; left.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x.
apply List.app_eq_app in Hlb.
destruct Hlb as (l' & Hlb).
destruct Hlb as [(H1, H2)| (H1, H2)]. {
  subst l1.
  destruct l' as [| b]; cbn in H2. {
    rewrite List.app_nil_r in H12.
    now injection H2; clear H2; intros; subst aft.
  }
  injection H2; clear H2; intros H2 H; subst b aft.
  remember ((bef ++ a :: l') ++ l2) as lb eqn:Hlb.
  apply (permutation_trans Heqb) with (lb := lb); [ easy | subst lb ].
  rewrite <- List.app_assoc.
  apply (permutation_app_head Heqb).
  rewrite List_app_cons, List.app_assoc.
  apply (permutation_app_tail Heqb).
  replace (a :: l') with ([a] ++ l') by easy.
  now apply permutation_app_comm.
}
destruct l' as [| b]. {
  cbn in H2; rewrite List.app_nil_r in H1.
  now injection H2; clear H2; intros; subst bef aft.
}
cbn in H2.
injection H2; clear H2; intros H2 H; subst b.
specialize (Hbef a).
assert (H : a ∈ bef) by now rewrite H1; apply List.in_or_app; right; left.
specialize (Hbef H).
now rewrite equality_refl in Hbef.
Qed.

Theorem permutation_middle : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb a,
  permutation eqb (a :: la ++ lb) (la ++ a :: lb).
Proof.
intros * Heqb *.
apply (permutation_cons_app Heqb).
now apply permutation_refl.
Qed.

Theorem permutation_elt : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ (la lb lc ld : list A) (a : A),
  permutation eqb (la ++ lb) (lc ++ ld)
  → permutation eqb (la ++ a :: lb) (lc ++ a :: ld).
Proof.
intros * Heqb * Hpab.
eapply (permutation_trans Heqb). {
  apply (permutation_sym Heqb).
  apply (permutation_middle Heqb).
}
now apply (permutation_cons_app Heqb).
Qed.

Theorem permutation_rev_l : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l, permutation eqb (List.rev l) l.
Proof.
intros * Heqb *.
induction l as [| a]; [ easy | cbn ].
eapply (permutation_trans Heqb). {
  apply (permutation_sym Heqb).
  apply (permutation_cons_append Heqb).
}
apply permutation_skip; [ | easy ].
now unfold reflexive; apply equality_refl.
Qed.

Theorem permutation_rev_r : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l, permutation eqb l (List.rev l).
Proof.
intros * Heqb *.
induction l as [| a]; [ easy | cbn ].
eapply (permutation_trans Heqb). 2: {
  apply (permutation_cons_append Heqb).
}
apply permutation_skip; [ | easy ].
now unfold reflexive; apply equality_refl.
Qed.

Theorem permutation_length : ∀ {A} {eqb : A → _} {la lb},
  permutation eqb la lb → List.length la = List.length lb.
Proof.
intros * Hpab.
unfold permutation in Hpab.
revert lb Hpab.
induction la as [| a]; intros. {
  now apply permutation_nil_l in Hpab; subst lb.
}
cbn in Hpab.
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb); subst lb.
rewrite List.length_app; cbn.
rewrite Nat.add_succ_r, <- List.length_app; f_equal.
now apply IHla.
Qed.

Theorem permutation_app_inv : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb lc ld a,
  permutation eqb (la ++ a :: lb) (lc ++ a :: ld)
  → permutation eqb (la ++ lb) (lc ++ ld).
Proof.
intros * Heqb * Hp.
specialize (permutation_add_inv Heqb) as H1.
apply (H1 a _ _ Hp (la ++ lb) (lc ++ ld)). {
  rewrite (List_cons_is_app a).
  rewrite (List_cons_is_app _ lb).
  do 2 rewrite List.app_assoc.
  apply (permutation_app_tail Heqb).
  apply (permutation_app_comm Heqb).
} {
  rewrite (List_cons_is_app a).
  rewrite (List_cons_is_app _ ld).
  do 2 rewrite List.app_assoc.
  apply (permutation_app_tail Heqb).
  apply (permutation_app_comm Heqb).
}
Qed.

Theorem permutation_app_inv_l : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l l1 l2,
  permutation eqb (l ++ l1) (l ++ l2) → permutation eqb l1 l2.
Proof.
intros * Heqb * H12.
revert l1 l2 H12.
induction l as [| a]; intros; [ easy | ].
cbn in H12.
apply permutation_cons_l_iff in H12; cbn in H12.
rewrite (equality_refl Heqb) in H12.
rewrite List.app_nil_l in H12.
now apply IHl.
Qed.

Theorem permutation_app_inv_r : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l l1 l2,
  permutation eqb (l1 ++ l) (l2 ++ l) → permutation eqb l1 l2.
Proof.
intros * Heqb * Hll.
apply (permutation_app_inv_l Heqb) with (l := l).
eapply (permutation_trans Heqb); [ now apply permutation_app_comm | ].
eapply (permutation_trans Heqb); [ apply Hll | ].
now apply permutation_app_comm.
Qed.

Theorem permutation_length_1 : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ a b,
  permutation eqb [a] [b] → a = b.
Proof.
intros * Heqb * Hpab.
unfold permutation in Hpab; cbn in Hpab.
remember (eqb a b) as ab eqn:Hab; symmetry in Hab.
destruct ab; [ now apply Heqb in Hab | easy ].
Qed.

Theorem permutation_length_1_inv_l :
  ∀ {A} {eqb : A → _} (Heqb : equality eqb) a l,
  permutation eqb [a] l → l = [a].
Proof.
intros * Heqb * Ha.
apply permutation_cons_l_iff in Ha.
remember (List_extract (eqb a) l) as ll eqn:Hll; symmetry in Hll.
destruct ll as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hll.
destruct Hll as (H1 & H & H2).
apply permutation_nil_l in Ha.
apply List.app_eq_nil in Ha.
destruct Ha; subst bef aft; cbn in H2; subst l.
f_equal; symmetry.
now apply Heqb.
Qed.

Theorem permutation_length_1_inv_r :
  ∀ {A} {eqb : A → _} (Heqb : equality eqb) a l,
  permutation eqb l [a] → l = [a].
Proof.
intros * Heqb * Ha.
apply (permutation_sym Heqb) in Ha.
now apply permutation_length_1_inv_l in Ha.
Qed.

Theorem NoDup_permutation : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb,
  List.NoDup la
  → List.NoDup lb
  → (∀ x : A, x ∈ la ↔ x ∈ lb)
  → permutation eqb la lb.
Proof.
intros * Heqb * Hna Hnb Hiab.
revert lb Hnb Hiab.
induction Hna as [| a la Ha Hna ]; intros. {
  destruct lb as [| b]; [ easy | ].
  now specialize (proj2 (Hiab b) (or_introl eq_refl)).
}
apply permutation_cons_l_iff.
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl.
  specialize (proj1 (Hiab a) (or_introl eq_refl)) as H2.
  specialize (H1 _ H2).
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x lb.
apply IHHna. {
  now apply List.NoDup_remove_1 in Hnb.
} {
  intros i.
  split; intros Hi. {
    specialize (proj1 (Hiab i) (or_intror Hi)) as H1.
    apply List.in_app_or in H1; apply List.in_or_app.
    destruct H1 as [H1| H1]; [ now left | right ].
    destruct H1 as [H1| H1]; [ | easy ].
    now subst i.
  } {
    specialize (proj2 (Hiab i)) as H1.
    assert (H : i ∈ bef ++ a :: aft). {
      apply List.in_app_or in Hi; apply List.in_or_app.
      destruct Hi as [Hi| Hi]; [ now left | now right; right ].
    }
    specialize (H1 H); clear H.
    destruct H1 as [H1| H1]; [ | easy ].
    subst i.
    now apply List.NoDup_remove_2 in Hnb.
  }
}
Qed.

Theorem NoDup_permutation_bis : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb,
  List.NoDup la
  → List.length lb ≤ List.length la
  → List.incl la lb
  → permutation eqb la lb.
Proof.
intros * Heqb * Hnda Hll Hiab.
specialize List.NoDup_incl_NoDup as Hndb.
specialize (Hndb _ la lb Hnda Hll Hiab).
apply (NoDup_permutation Heqb); [ easy | easy | ].
intros i.
split; [ apply Hiab | ].
now apply List.NoDup_length_incl.
Qed.

Theorem permutation_NoDup : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ [la lb],
  permutation eqb la lb → List.NoDup la → List.NoDup lb.
Proof.
intros * Heqb * Hpab Hla.
revert lb Hpab.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hpab; subst lb.
}
apply permutation_cons_l_iff in Hpab.
remember (List_extract (eqb a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqb in H; subst x lb.
generalize Hpab; intros H.
apply IHla in H; [ | now apply List.NoDup_cons_iff in Hla ].
apply NoDup_app_iff in H.
apply NoDup_app_iff.
destruct H as (Hndb & Hnda & Haft).
split; [ easy | ].
split. {
  apply List.NoDup_cons_iff.
  split; [ | easy ].
  intros Ha.
  assert (H : a ∈ bef ++ aft) by now apply List.in_or_app; right.
  apply (permutation_in_iff Heqb) with (a := a) in Hpab.
  apply Hpab in H.
  now apply List.NoDup_cons_iff in Hla.
}
intros b Hb.
intros H.
destruct H as [H| H]; [ subst b | now apply Haft in Hb ].
assert (H : a ∈ bef ++ aft) by now apply List.in_or_app; left.
apply (permutation_in_iff Heqb) with (a := a) in Hpab.
apply Hpab in H.
now apply List.NoDup_cons_iff in Hla.
Qed.

Theorem permutation_map : ∀ {A B} [eqba : A → _] [eqbb : B → _],
  equality eqba →
  equality eqbb →
  ∀ (f : A → B) (la lb : list A),
  permutation eqba la lb → permutation eqbb (List.map f la) (List.map f lb).
Proof.
intros * Heqba Heqbb * Hpab.
revert lb Hpab.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hpab; subst lb.
}
apply permutation_cons_l_iff in Hpab.
remember (List_extract (eqba a) lb) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
apply Heqba in H; subst x lb.
rewrite List.map_app; cbn.
apply (permutation_cons_app Heqbb).
rewrite <- List.map_app.
now apply IHla.
Qed.

(* *)

Theorem List_rank_loop_extract : ∀ A (la : list A) f i,
  List_rank_loop i f la =
  match List_extract f la with
  | Some (bef, _, _) => i + List.length bef
  | None => i + List.length la
  end.
Proof.
intros.
revert i.
induction la as [| a]; cbn; intros. {
  symmetry; apply Nat.add_0_r.
}
destruct (f a); [ now rewrite Nat.add_0_r | ].
rewrite IHla.
remember (List_extract f la) as lxl eqn:Hlxl; symmetry in Hlxl.
now destruct lxl as [((bef, x), aft)| ]; cbn; rewrite Nat.add_succ_r.
Qed.

Theorem List_rank_extract : ∀ A (la : list A) f,
  List_rank f la =
  match List_extract f la with
  | Some (bef, _, _) => List.length bef
  | None => List.length la
  end.
Proof.
intros.
apply List_rank_loop_extract.
Qed.

Theorem List_rank_not_found : ∀ n l i,
  permutation Nat.eqb l (List.seq 0 n)
  → i < n
  → List_rank (Nat.eqb i) l ≠ List.length l.
Proof.
intros n f i Hp Hi Hx.
rewrite List_rank_extract in Hx.
remember (List_extract (Nat.eqb i) f) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. {
  apply List_extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Haft); subst f.
  rewrite List.length_app in Hx; cbn in Hx; flia Hx.
}
clear Hx.
specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
specialize (H1 i).
assert (H : i ∈ f). {
  apply (permutation_in_iff Nat.eqb_eq Hp).
  now apply List.in_seq.
}
specialize (H1 H); clear H.
now apply Nat.eqb_neq in H1.
Qed.

(* permutation_fun : bijective function from permutation *)

Definition option_eqb {A} (eqb : A → A → bool) ao bo :=
  match (ao, bo) with
  | (Some a, Some b) => eqb a b
  | _ => false
  end.

Fixpoint permutation_assoc_loop {A} eqb (la : list A) lbo :=
  match la with
  | [] => []
  | a :: la' =>
      match List_extract (λ bo, option_eqb eqb bo (Some a)) lbo with
      | Some (befo, _, afto) =>
          List.length befo ::
            permutation_assoc_loop eqb la' (befo ++ None :: afto)
      | None => []
      end
  end.

Definition permutation_assoc {A} (eqb : A → _) la lb :=
  permutation_assoc_loop eqb la (List.map Some lb).

Definition permutation_fun {A} (eqb : A → _) la lb i :=
  let j := List_rank (Nat.eqb i) (permutation_assoc eqb la lb) in
  if j =? List.length la then 0 else j.

Fixpoint filter_Some {A} (lao : list (option A)) :=
  match lao with
  | [] => []
  | Some a :: lao' => a :: filter_Some lao'
  | None :: lao' => filter_Some lao'
  end.

Theorem fold_permutation_assoc : ∀ {A} {eqb : A → _} la lb,
  permutation_assoc_loop eqb la (List.map Some lb) =
  permutation_assoc eqb la lb.
Proof. easy. Qed.

Theorem filter_Some_inside : ∀ A l1 l2 (x : option A),
  filter_Some (l1 ++ x :: l2) =
    filter_Some l1 ++
    match x with
    | Some a => a :: filter_Some l2
    | None => filter_Some l2
    end.
Proof.
intros.
revert x l2.
induction l1 as [| yo]; intros; [ easy | ].
cbn - [ option_eqb ].
destruct yo; [ | apply IHl1 ].
cbn; f_equal; apply IHl1.
Qed.

Theorem filter_Some_map_Some : ∀ A (la : list A),
  filter_Some (List.map Some la) = la.
Proof.
intros.
induction la as [| a]; [ easy | cbn ].
now f_equal.
Qed.

Theorem permutation_assoc_loop_length : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lbo,
  permutation eqb la (filter_Some lbo)
  → List.length (permutation_assoc_loop eqb la lbo) = List.length la.
Proof.
intros * Heqb * Hpab.
revert lbo Hpab.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lbo). {
    specialize (permutation_in_iff Heqb Hpab) as H2.
    specialize (proj1 (H2 a) (or_introl eq_refl)) as H3.
    clear - H3.
    induction lbo as [| bo]; [ easy | cbn in H3 ].
    destruct bo as [b| ]. {
      destruct H3 as [H3| H3]; [ now subst b; left | ].
      now right; apply IHlbo.
    }
    now right; apply IHlbo.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
cbn; f_equal.
apply IHla.
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hxa & Hlbo).
cbn in Hxa.
destruct x as [b| ]; [ | easy ].
apply Heqb in Hxa; subst b.
subst lbo.
rewrite filter_Some_inside in Hpab |-*.
apply (permutation_app_inv Heqb [] _ _ _ _ Hpab).
Qed.

Theorem permutation_assoc_length : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ {la lb},
  permutation eqb la lb
  → List.length (permutation_assoc eqb la lb) = List.length la.
Proof.
intros * Heqb * Hpab.
apply (permutation_assoc_loop_length Heqb).
now rewrite filter_Some_map_Some.
Qed.

Theorem permutation_assoc_loop_ub : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lbo i,
  permutation eqb la (filter_Some lbo)
  → i < List.length la
  → List.nth i (permutation_assoc_loop eqb la lbo) 0 < List.length lbo.
Proof.
intros * Heqb * Hpab Hla.
revert lbo i Hpab Hla.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  rewrite List_nth_nil.
  destruct lbo; [ | now cbn ].
  cbn in Hpab.
  now apply permutation_nil_r in Hpab.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
cbn in H.
destruct x as [b| ]; [ | easy ].
apply Heqb in H; subst b.
destruct i. {
  rewrite List_nth_0_cons.
  apply (f_equal (λ l, List.length l)) in Hlb.
  rewrite List.length_app in Hlb; cbn in Hlb.
  rewrite Hlb; flia.
}
cbn in Hla; apply Nat.succ_lt_mono in Hla.
rewrite List_nth_succ_cons.
replace (List.length lbo) with (List.length (bef ++ None :: aft)). 2: {
  rewrite Hlb.
  now do 2 rewrite List.length_app.
}
apply IHla; [ | easy ].
subst lbo.
rewrite filter_Some_inside in Hpab |-*.
apply (permutation_app_inv Heqb [] _ _ _ _ Hpab).
Qed.

Theorem permutation_assoc_loop_None_inside : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lbo lco,
  permutation_assoc_loop eqb la (lbo ++ None :: lco) =
  List.map (λ i, if i <? List.length lbo then i else S i)
    (permutation_assoc_loop eqb la (lbo ++ lco)).
Proof.
intros * Heqb *.
revert lbo lco.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb "<?" ].
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl; cbn - [ option_eqb ] in H1.
  remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
  destruct lxl as [((bef, x), aft)| ]; [ | easy ].
  apply List_extract_Some_iff in Hlxl.
  destruct Hlxl as (Hbef & H & Hlbc).
  cbn in H.
  destruct x as [x| ]; [ | easy ].
  apply Heqb in H; subst x.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lbo ++ None :: lco). {
    clear - Hlbc.
    enough (H : Some a ∈ lbo ++ lco). {
      apply List.in_app_or in H; apply List.in_or_app.
      destruct H as [H| H]; [ now left | now right; right ].
    }
    rewrite Hlbc.
    now apply List.in_or_app; right; left.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlbc).
cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  clear Hlxl; cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ lbo ++ lco). {
    enough (H : Some a ∈ lbo ++ None :: lco). {
      apply List.in_app_or in H; apply List.in_or_app.
      destruct H as [H| H]; [ now left | ].
      destruct H as [H| H]; [ easy | now right ].
    }
    rewrite Hlbc.
    now apply List.in_or_app; right; left.
  }
  specialize (H1 H).
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
cbn - [ "<?" ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlbc').
cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
move Hlbc before Hlbc'.
move Hbef before Hbef'.
rewrite if_ltb_lt_dec.
destruct (lt_dec (List.length bef') (List.length lbo)) as [Hfo| Hfo]. {
  apply List.app_eq_app in Hlbc'.
  destruct Hlbc' as (ldo & H4).
  destruct H4 as [(H4, H5)| (H4, H5)]. {
    subst lbo.
    rewrite List.length_app in Hfo.
    destruct ldo as [| d]; [ cbn in Hfo; flia Hfo | ].
    cbn in H5; clear Hfo.
    injection H5; clear H5; intros; subst d aft'.
    rewrite <- List.app_assoc in Hlbc.
    cbn in Hlbc.
    apply List.app_eq_app in Hlbc.
    destruct Hlbc as (lfo & H4).
    destruct H4 as [(H4, H5)| (H4, H5)]. {
      subst bef'; clear Hbef; rename Hbef' into Hbef.
      rewrite List.length_app, Nat.add_comm.
      destruct lfo as [| d]. {
        f_equal.
        rewrite List.app_nil_r.
        injection H5; clear H5; intros; subst aft.
        replace (List.length (bef ++ Some a :: ldo)) with
          (List.length (bef ++ None :: ldo)). 2: {
          now do 2 rewrite List.length_app.
        }
        rewrite List_cons_is_app.
        do 2 rewrite List.app_assoc.
        remember (bef ++ None :: ldo) as lbo eqn:Hlbo.
        replace ((bef ++ [None]) ++ ldo) with lbo. 2: {
          subst lbo.
          now rewrite <- List.app_assoc.
        }
        subst lbo.
        now rewrite IHla, <- List.app_assoc.
      } {
        exfalso.
        injection H5; clear H5; intros H5 H; subst d.
        specialize (Hbef (Some a)) as H1.
        assert (H : Some a ∈ bef ++ Some a :: lfo). {
          now apply List.in_or_app; right; left.
        }
        specialize (H1 H); clear H; cbn in H1.
        now rewrite (equality_refl Heqb) in H1.
      }
    } {
      subst bef; rename bef' into bef; clear Hbef'.
      rewrite List.length_app, Nat.add_comm.
      destruct lfo as [| d]. {
        f_equal.
        rewrite List.app_nil_r.
        injection H5; clear H5; intros; subst aft.
        replace (List.length (bef ++ Some a :: ldo)) with
          (List.length (bef ++ None :: ldo)). 2: {
          now do 2 rewrite List.length_app.
        }
        rewrite List_cons_is_app.
        do 2 rewrite List.app_assoc.
        remember (bef ++ None :: ldo) as lbo eqn:Hlbo.
        replace ((bef ++ [None]) ++ ldo) with lbo. 2: {
          subst lbo.
          now rewrite <- List.app_assoc.
        }
        subst lbo.
        now rewrite IHla, <- List.app_assoc.
      } {
        exfalso.
        injection H5; clear H5; intros H5 H; subst d.
        specialize (Hbef (Some a)) as H1.
        assert (H : Some a ∈ bef ++ Some a :: lfo). {
          now apply List.in_or_app; right; left.
        }
        specialize (H1 H); clear H; cbn in H1.
        now rewrite (equality_refl Heqb) in H1.
      }
    }
  } {
    subst bef' lco.
    rewrite List.length_app in Hfo; flia Hfo.
  }
} {
  apply Nat.nlt_ge in Hfo.
  apply List.app_eq_app in Hlbc'.
  destruct Hlbc' as (ldo & H4).
  destruct H4 as [(H4, H5)| (H4, H5)]. {
    subst lbo.
    rewrite List.length_app in Hfo.
    destruct ldo; [ | cbn in Hfo; flia Hfo ].
    cbn in H5; clear Hfo.
    subst lco.
    rewrite List.app_nil_r in Hlbc.
    apply List.app_eq_app in Hlbc.
    destruct Hlbc as (lfo & H4).
    destruct H4 as [(H4, H5)| (H4, H5)]. {
      subst bef'; exfalso.
      destruct lfo as [| d]; [ easy | ].
      cbn in H5.
      injection H5; clear H5; intros; subst d aft.
      specialize (Hbef' (Some a)) as H1.
      assert (H : Some a ∈ bef ++ Some a :: lfo). {
        now apply List.in_or_app; right; left.
      }
      specialize (H1 H); clear H; cbn in H1.
      now rewrite (equality_refl Heqb) in H1.
    } {
      subst bef.
      rewrite List.length_app, Nat.add_comm.
      destruct lfo as [| d]; [ easy | ].
      destruct lfo as [| d']. {
        f_equal.
        rewrite List.app_nil_r.
        injection H5; clear H5; intros; subst aft' d.
        now rewrite <- IHla, <- List.app_assoc.
      } {
        injection H5; clear H5; intros; subst d d' aft'.
        specialize (Hbef (Some a)) as H1.
        assert (H : Some a ∈ bef' ++ None :: Some a :: lfo). {
          now apply List.in_or_app; right; right; left.
        }
        specialize (H1 H); clear H; cbn in H1.
        now rewrite (equality_refl Heqb) in H1.
      }
    }
  } {
    subst bef' lco.
    clear Hfo.
    apply List.app_eq_app in Hlbc.
    destruct Hlbc as (lfo & H4).
    destruct H4 as [(H4, H5)| (H4, H5)]. {
      subst lbo.
      destruct lfo as [| d]; [ easy | ].
      injection H5; clear H5; intros H5 H; subst d.
      specialize (Hbef' (Some a)) as H1.
      assert (H : Some a ∈ (bef ++ Some a :: lfo) ++ ldo). {
        rewrite <- List.app_assoc.
        now apply List.in_or_app; right; left.
      }
      specialize (H1 H); clear H; cbn in H1.
      now rewrite (equality_refl Heqb) in H1.
    } {
      subst bef.
      do 2 rewrite List.length_app; cbn - [ "<?" ].
      rewrite <- Nat.add_succ_r.
      destruct lfo as [| d]; [ easy | ].
      cbn - [ "<?" ].
      injection H5; clear H5; intros H5 H; subst d.
      apply List.app_eq_app in H5.
      destruct H5 as (lgo & H5).
      destruct H5 as [(H4, H5)| (H4, H5)]. {
        subst ldo.
        do 2 rewrite Nat.add_succ_r.
        rewrite List.length_app, (Nat.add_comm (List.length lfo)).
        rewrite Nat.add_assoc.
        rewrite (Nat.add_comm _ (List.length lgo)).
        destruct lgo as [| d]. {
          f_equal.
          rewrite List.app_nil_r.
          injection H5; clear H5; intros; subst aft'.
          do 2 rewrite <- List.app_assoc.
          apply IHla.
        }
        exfalso.
        injection H5; clear H5; intros; subst d aft.
        specialize (Hbef' (Some a)) as H1.
        assert (H : Some a ∈ lbo ++ lfo ++ Some a :: lgo). {
          rewrite List.app_assoc.
          now apply List.in_or_app; right; left.
        }
        specialize (H1 H); clear H; cbn in H1.
        now rewrite (equality_refl Heqb) in H1.
      } {
        subst lfo.
        do 2 rewrite Nat.add_succ_r.
        rewrite List.length_app, Nat.add_assoc, Nat.add_comm.
        destruct lgo as [| d]. {
          f_equal.
          rewrite List.app_nil_r.
          injection H5; clear H5; intros; subst aft'.
          do 2 rewrite <- List.app_assoc.
          apply IHla.
        }
        exfalso.
        injection H5; clear H5; intros; subst d aft'.
        specialize (Hbef (Some a)) as H1.
        assert (H : Some a ∈ lbo ++ None :: ldo ++ Some a :: lgo). {
          apply List.in_or_app; right; right.
          now apply List.in_or_app; right; left.
        }
        specialize (H1 H); clear H; cbn in H1.
        now rewrite (equality_refl Heqb) in H1.
      }
    }
  }
}
Qed.

Theorem filter_Some_app : ∀ A (l1 l2 : list (option A)),
  filter_Some (l1 ++ l2) = filter_Some l1 ++ filter_Some l2.
Proof.
intros.
revert l2.
induction l1 as [| xo]; intros; [ easy | cbn ].
destruct xo as [x| ]; [ | apply IHl1 ].
cbn; f_equal; apply IHl1.
Qed.

Theorem permutation_assoc_loop_nth_nth : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ d la lbo i j,
  permutation eqb la (filter_Some lbo)
  → i < List.length la
  → List.nth i (permutation_assoc_loop eqb la lbo) 0 = j
  → List.nth i la d = unsome d (List.nth j lbo None).
Proof.
intros * Heqb * Hpab Hi Hij.
subst j.
revert d lbo i Hpab Hi.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb ].
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl (Some a)) as H1.
  cbn - [ option_eqb List.In ] in H1.
  specialize (permutation_in_iff Heqb) as H2.
  specialize (proj1 (H2 _ _ Hpab _) (or_introl eq_refl)) as H3.
  assert (H : Some a ∈ lbo). {
    clear - H3.
    induction lbo as [| bo]; [ easy | ].
    cbn in H3.
    destruct bo as [b| ]. {
      destruct H3 as [H2| H2]; [ now left; subst b | right ].
      now apply IHlbo.
    }
    now right; apply IHlbo.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
subst lbo.
rewrite filter_Some_app in Hpab; cbn in Hpab.
specialize (permutation_app_inv Heqb) as H.
specialize (H [] _ _ _ _ Hpab).
cbn in H; move H before Hpab; clear Hpab; rename H into Hpab.
rewrite <- filter_Some_app in Hpab.
destruct i. {
  cbn.
  rewrite List.app_nth2; [ | now unfold ge ].
  now rewrite Nat.sub_diag.
}
rewrite List_nth_succ_cons.
cbn in Hi.
apply Nat.succ_lt_mono in Hi.
rewrite IHla with (lbo := bef ++ aft); [ | easy | easy ].
f_equal.
rewrite (permutation_assoc_loop_None_inside Heqb).
rewrite (List_map_nth' 0). 2: {
  now rewrite (permutation_assoc_loop_length Heqb).
}
remember (List.nth i (permutation_assoc_loop _ _ _) 0) as j eqn:Hj.
symmetry in Hj.
rewrite if_ltb_lt_dec.
destruct (lt_dec j (List.length bef)) as [Hjb| Hjb]. {
  rewrite List.app_nth1; [ | easy ].
  now rewrite List.app_nth1.
}
apply Nat.nlt_ge in Hjb.
rewrite List.app_nth2; [ | easy ].
rewrite List.app_nth2; [ | flia Hjb ].
now rewrite Nat.sub_succ_l.
Qed.

Theorem unmap_Some_app_cons : ∀ A (a : A) la lbo lco,
  List.map Some la = lbo ++ Some a :: lco
  → lbo = List.map Some (filter_Some lbo) ∧
    lco = List.map Some (filter_Some lco) ∧
    la = filter_Some lbo ++ a :: filter_Some lco.
Proof.
intros * Hla.
assert (H : lbo = List.map Some (filter_Some lbo)). {
  revert la Hla.
  induction lbo as [| bo]; intros; [ easy | cbn ].
  cbn in Hla.
  destruct la as [| a']; [ easy | ].
  injection Hla; clear Hla; intros Hla H; subst bo.
  cbn; f_equal.
  now apply (IHlbo la).
}
rewrite H in Hla |-*; clear H.
rewrite filter_Some_map_Some.
assert (H : lco = List.map Some (filter_Some lco)). {
  rewrite List_cons_is_app, List.app_assoc in Hla.
  replace (List.map Some (filter_Some lbo) ++ [Some a]) with
    (List.map Some (filter_Some lbo ++ [a])) in Hla. 2: {
    now rewrite List.map_app.
  }
  remember (filter_Some lbo ++ [a]) as lb eqn:Hlb.
  clear a lbo Hlb.
  revert la lco Hla.
  induction lb as [| b]; intros; cbn. {
    cbn in Hla; subst lco.
    symmetry; f_equal; apply filter_Some_map_Some.
  }
  cbn in Hla.
  destruct la as [| a]; [ easy | ].
  injection Hla; clear Hla; intros Hlb H.
  now apply (IHlb la).
}
rewrite H in Hla |-*; clear H.
apply (f_equal filter_Some) in Hla.
rewrite filter_Some_map_Some in Hla |-*.
rewrite filter_Some_app in Hla; cbn in Hla.
now do 2 rewrite filter_Some_map_Some in Hla.
Qed.

Theorem permutation_permutation_assoc : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ {la lb},
  permutation eqb la lb
  → permutation Nat.eqb (permutation_assoc eqb la lb)
      (List.seq 0 (List.length la)).
Proof.
intros * Heqb * Hpab.
revert lb Hpab.
induction la as [| a]; intros; [ easy | ].
cbn - [ option_eqb List.seq ].
remember (List_extract (λ bo, option_eqb eqb bo (Some a)) (List.map Some lb))
  as lxl.
rename Heqlxl into Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ List.map Some lb). {
    apply List.in_map_iff.
    exists a; split; [ easy | ].
    now apply (permutation_in_iff Heqb Hpab a); left.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hlb).
cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
apply unmap_Some_app_cons in Hlb.
destruct Hlb as (H1 & H2 & Hlb).
subst lb.
specialize (permutation_app_inv Heqb [] _ _ _ _ Hpab) as H.
cbn in H; move H before Hpab; clear Hpab; rename H into Hpab.
specialize (IHla _ Hpab) as H3.
rewrite List_seq_cut3 with (i := List.length bef). 2: {
  apply List.in_seq; split; [ easy | cbn ].
  rewrite H1, List.length_map.
  apply permutation_length in Hpab.
  rewrite List.length_app in Hpab.
  flia Hpab.
}
rewrite Nat.sub_0_r, Nat.add_0_l.
cbn - [ "<?" ].
replace (List.length la - List.length bef) with (List.length aft). 2: {
  rewrite H1, H2.
  do 2 rewrite List.length_map.
  apply permutation_length in Hpab.
  rewrite List.length_app in Hpab.
  flia Hpab.
}
remember (List.length bef) as i eqn:Hi.
apply (permutation_elt Nat.eqb_eq []); cbn.
rewrite (permutation_assoc_loop_None_inside Heqb).
rewrite <- Hi.
set (f := λ j, if j <? i then j else S j).
destruct (Nat.eq_dec (List.length aft) 0) as [Haz| Haz]. {
  apply List.length_zero_iff_nil in Haz; move Haz at top; subst aft.
  clear H2; cbn in Hpab |-*.
  rewrite List.app_nil_r in Hpab.
  do 2 rewrite List.app_nil_r.
  unfold f.
  rewrite Hi.
  erewrite List.map_ext_in. 2: {
    intros j Hj.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec j (List.length bef)) as [Hji| Hji]. 2: {
      exfalso; apply Hji.
      apply (List.In_nth _ _ 0) in Hj.
      rewrite (permutation_assoc_loop_length Heqb) in Hj; [ | easy ].
      destruct Hj as (k & Hk & Hkj).
      rewrite <- Hkj.
      now apply (permutation_assoc_loop_ub Heqb).
    }
    easy.
  }
  rewrite List.map_id.
  replace (List.length bef) with (List.length la). 2: {
    rewrite (permutation_length Hpab).
    now rewrite H1, filter_Some_map_Some, List.length_map.
  }
  rewrite H1.
  rewrite fold_permutation_assoc.
  now apply IHla.
}
replace (List.seq 0 i ++ List.seq (S i) (List.length aft)) with
    (List.map f (List.seq 0 (i + List.length aft))). 2: {
  rewrite List_seq_cut3 with (i := i). 2: {
    apply List.in_seq.
    split; [ easy | ].
    flia Haz.
  }
  rewrite Nat.sub_0_r, Nat.add_0_l.
  rewrite List.map_app.
  unfold f.
  erewrite List.map_ext_in. 2: {
    intros j Hj.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec j i) as [Hji| Hji]. 2: {
      apply List.in_seq in Hj.
      now exfalso; apply Hji.
    }
    easy.
  }
  rewrite List.map_id; f_equal.
  erewrite List.map_ext_in. 2: {
    intros j Hj.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec j i) as [Hji| Hji]. {
      exfalso.
      apply List.in_app_or in Hj.
      destruct Hj as [[Hj| Hj]| Hj]; [ flia Hj Hji | easy | ].
      apply List.in_seq in Hj.
      flia Hj Hji.
    }
    easy.
  }
  cbn.
  rewrite List.seq_shift.
  destruct aft; [ easy | cbn ].
  f_equal; f_equal.
  rewrite Nat.add_succ_r; cbn.
  now rewrite Nat.add_comm, Nat.add_sub.
}
apply (permutation_map Nat.eqb_eq Nat.eqb_eq).
replace (i + List.length aft) with (List.length la). 2: {
  rewrite (permutation_length Hpab).
  rewrite List.length_app.
  rewrite <- (List.length_map Some (filter_Some _)), <- H1.
  rewrite <- (List.length_map Some (filter_Some _)), <- H2.
  now rewrite Hi.
}
rewrite H1, H2, <- List.map_app.
rewrite fold_permutation_assoc.
now apply IHla.
Qed.

Theorem map_permutation_assoc : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ d [la lb],
  permutation eqb la lb
  → la = List.map (λ i, List.nth i lb d) (permutation_assoc eqb la lb).
Proof.
intros * Heqb * Hpab.
unfold permutation_assoc.
revert lb Hpab.
induction la as [| a]; intros; [ easy | ].
apply permutation_cons_l_iff in Hpab.
remember (List_extract _ _) as lxl eqn:Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
symmetry in Hlxl.
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Haft).
apply Heqb in H; subst x lb.
cbn - [ option_eqb ].
remember (List_extract _ _) as lxl eqn:Hlxl.
symmetry in Hlxl.
destruct lxl as [((bef', x), aft')| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  cbn - [ option_eqb ] in H1.
  specialize (H1 (Some a)).
  assert (H : Some a ∈ List.map Some (bef ++ a :: aft)). {
    rewrite List.map_app; cbn.
    now apply List.in_or_app; right; left.
  }
  specialize (H1 H); clear H.
  cbn in H1.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef' & H & Hlb); cbn in H.
destruct x as [x| ]; [ | easy ].
apply Heqb in H; subst x.
rewrite List.map_app in Hlb; cbn in Hlb.
apply List_app_eq_app' in Hlb. 2: {
  rewrite List.length_map.
  clear Hpab.
  revert bef' Hbef' Hlb.
  induction bef as [| b]; intros. {
    cbn in Hlb.
    destruct bef' as [| b']; [ easy | ].
    cbn in Hlb.
    injection Hlb; clear Hlb; intros; subst b'.
    specialize (Hbef' _ (or_introl eq_refl)) as H1; cbn in H1.
    now rewrite (equality_refl Heqb) in H1.
  }
  cbn in Hlb.
  destruct bef' as [| b']. {
    cbn in Hlb.
    injection Hlb; clear Hlb; intros Hlb H; subst b.
    specialize (Hbef _ (or_introl eq_refl)).
    now rewrite (equality_refl Heqb) in Hbef.
  }
  cbn; f_equal.
  cbn in Hlb.
  injection Hlb; clear Hlb; intros Hlb H; subst b'.
  apply IHbef; [ | | easy ]. {
    now intros; apply Hbef; right.
  } {
    now intros; apply Hbef'; right.
  }
}
destruct Hlb as (Hbb' & Haa').
subst bef'.
injection Haa'; clear Haa'; intros; subst aft'.
rewrite List.length_map.
cbn.
rewrite List.app_nth2; [ | now unfold ge ].
rewrite Nat.sub_diag; cbn.
f_equal.
rewrite (permutation_assoc_loop_None_inside Heqb).
rewrite List.length_map.
rewrite <- List.map_app.
rewrite List.map_map.
erewrite List.map_ext_in. 2: {
  intros b Hb.
  replace (List.nth _ _ _) with (List.nth b (bef ++ aft) d). 2: {
    rewrite if_ltb_lt_dec.
    destruct (lt_dec b (List.length bef)) as [Hbb| Hbb]. {
      rewrite List.app_nth1; [ | easy ].
      now rewrite List.app_nth1.
    }
    apply Nat.nlt_ge in Hbb.
    rewrite List.app_nth2; [ | easy ].
    rewrite List.app_nth2; [ | flia Hbb ].
    now rewrite Nat.sub_succ_l.
  }
  easy.
}
now apply IHla.
Qed.

Theorem permutation_fun_nth : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ d la lb i,
  permutation eqb la lb
  → i < List.length la
  → List.nth i lb d = List.nth (permutation_fun eqb la lb i) la d.
Proof.
intros * Heqb * Hpab Hi.
unfold permutation_fun.
set (l := permutation_assoc eqb la lb).
remember (List_rank (Nat.eqb i) l) as j eqn:Hj; symmetry in Hj.
destruct (Nat.eq_dec j (List.length l)) as [Hjl| Hjl]. {
  exfalso; revert Hj; rewrite Hjl.
  apply List_rank_not_found with (n := List.length la); [ | easy ].
  now apply permutation_permutation_assoc.
}
apply (List_rank_if 0) in Hj.
destruct Hj as (Hjl', Hj).
destruct Hj as [Hj| Hj]; [ clear Hjl | easy ].
destruct Hj as (Hjl, Hij).
apply Nat.eqb_eq in Hij.
symmetry in Hij; unfold l in Hij.
apply (permutation_assoc_loop_nth_nth Heqb) with (d := d) in Hij; cycle 1. {
  now rewrite filter_Some_map_Some.
} {
  unfold l in Hjl.
  now rewrite permutation_assoc_length in Hjl.
}
rewrite (List_map_nth' d) in Hij. {
  rewrite if_eqb_eq_dec.
  unfold l in Hjl; rewrite (permutation_assoc_length Heqb Hpab) in Hjl.
  destruct (Nat.eq_dec j (List.length la)) as [H| H]; [ flia H Hjl | easy ].
}
now rewrite (permutation_length Hpab) in Hi.
Qed.

Theorem permutation_nth : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb d,
  permutation eqb la lb
  ↔ (let n := List.length la in
     List.length lb = n ∧
     ∃ f : nat → nat,
     FinFun.bFun n f ∧
     FinFun.bInjective n f ∧
     (∀ x : nat, x < n → List.nth x lb d = List.nth (f x) la d)).
Proof.
intros * Heqb *.
split. {
  intros Hpab *.
  split. {
    subst n; symmetry.
    apply (permutation_length Hpab).
  }
  exists (permutation_fun eqb la lb).
  split. {
    intros i Hi.
    unfold permutation_fun.
    remember (List_rank _ _) as j eqn:Hj.
    symmetry in Hj.
    rewrite if_eqb_eq_dec.
    destruct (Nat.eq_dec j (List.length la)) as [Hjla| Hjla]; [ flia Hi | ].
    apply (List_rank_if 0) in Hj.
    rewrite (permutation_assoc_length Heqb) in Hj; [ | easy ].
    destruct Hj as (Hjl, Hj).
    destruct Hj as [Hj| Hj]; [ | easy ].
    now fold n in Hj.
  }
  split. {
    intros i j Hi Hj Hij.
    unfold permutation_fun in Hij.
    do 2 rewrite List_rank_extract in Hij.
    remember (List_extract (Nat.eqb i) _) as lxl eqn:Hlxl; symmetry in Hlxl.
    rewrite (permutation_assoc_length Heqb Hpab) in Hij.
    destruct lxl as [((bef, x), aft)| ]. 2: {
      specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
      specialize (permutation_permutation_assoc Heqb Hpab) as H2.
      specialize (permutation_in_iff Nat.eqb_eq H2) as H3.
      specialize (proj2 (H3 i)) as H4.
      fold n in H4.
      assert (H : i ∈ List.seq 0 n) by now apply List.in_seq.
      specialize (H4 H); clear H.
      specialize (H1 _ H4).
      now apply Nat.eqb_neq in H1.
    }
    apply List_extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef & H & Hp).
    apply Nat.eqb_eq in H; subst x.
    rewrite if_eqb_eq_dec in Hij.
    destruct (Nat.eq_dec (List.length bef) (List.length la)) as [Hba| Hba]. {
      apply (f_equal (λ l, List.length l)) in Hp.
      rewrite (permutation_assoc_length Heqb Hpab), List.length_app in Hp.
      cbn in Hp; flia Hp Hba.
    }
    remember (List_extract (Nat.eqb j) _) as lxl eqn:Hlxl; symmetry in Hlxl.
    destruct lxl as [((bef', x), aft')| ]. 2: {
      specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
      specialize (permutation_permutation_assoc Heqb Hpab) as H2.
      specialize (permutation_in_iff Nat.eqb_eq H2) as H3.
      specialize (proj2 (H3 j)) as H4.
      fold n in H4.
      assert (H : j ∈ List.seq 0 n) by now apply List.in_seq.
      specialize (H4 H); clear H.
      specialize (H1 _ H4).
      now apply Nat.eqb_neq in H1.
    }
    apply List_extract_Some_iff in Hlxl.
    destruct Hlxl as (Hbef' & H & Hp').
    apply Nat.eqb_eq in H; subst x.
    rewrite if_eqb_eq_dec in Hij.
    destruct (Nat.eq_dec (List.length bef') (List.length la))
        as [Hba'| Hba']. {
      apply (f_equal (λ l, List.length l)) in Hp'.
      rewrite (permutation_assoc_length Heqb Hpab), List.length_app in Hp'.
      cbn in Hp'; flia Hp' Hba'.
    }
    rewrite Hp' in Hp.
    apply List_app_eq_app' in Hp; [ | easy ].
    destruct Hp as (H1, H2).
    now injection H2.
  }
  intros i Hi.
  now apply (permutation_fun_nth Heqb).
} {
  intros (Hlab & f & Hbf & Hif & Hn).
  assert (Hsf : FinFun.bSurjective (List.length la) f). {
    now apply FinFun.bInjective_bSurjective.
  }
  move Hsf before Hif.
  specialize (FinFun.bSurjective_bBijective Hbf Hsf) as H.
  destruct H as (g & Hbg & Hfg).
  move g before f; move Hbg before Hbf.
  move Hfg before Hsf.
  unfold FinFun.bFun in Hbf, Hbg.
  clear Hif Hsf.
  remember (List.length la) as len eqn:Hlen.
  symmetry in Hlen.
  rename Hlen into Hal; rename Hlab into Hbl.
  revert f g la lb Hal Hbl Hbf Hbg Hfg Hn.
  induction len; intros. {
    now apply List.length_zero_iff_nil in Hal, Hbl; subst la lb.
  }
  destruct la as [| a]; [ easy | ].
  cbn in Hal; apply Nat.succ_inj in Hal.
  specialize (Hn (g 0)) as H1.
  assert (Hgb : g 0 < S len) by now apply Hbg.
  specialize (H1 Hgb).
  rewrite (proj2 (Hfg 0 (Nat.lt_0_succ _))) in H1; cbn in H1.
  rewrite <- (List.firstn_skipn (g 0) lb).
  replace (List.skipn (g 0) lb) with (a :: List.skipn (S (g 0)) lb). 2: {
    rewrite <- H1.
    symmetry.
    apply List_skipn_is_cons.
    now rewrite Hbl.
  }
  apply (permutation_cons_app Heqb).
  set (f' := λ i, if i <? g 0 then f i - 1 else f (S i) - 1).
  set (g' := λ i, if g 0 <? g (S i) then g (S i) - 1 else g (S i)).
  apply (IHlen f' g'); [ easy | | | | | ]. {
    rewrite List.length_app, List.length_firstn, List.length_skipn.
    rewrite Hbl, Nat.min_l; [ cbn | flia Hgb ].
    rewrite Nat.add_sub_assoc; [ | flia Hgb ].
    now rewrite Nat.add_comm, Nat.add_sub.
  } {
    intros i Hi.
    assert (His : i < S len) by flia Hi.
    unfold f'.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec i (g 0)) as [Higz| Higz]. {
      specialize (Hbf i His) as H2.
      remember (f i) as fi eqn:Hfi.
      destruct fi; [ | rewrite Nat_sub_succ_1; flia H2 ].
      flia Hi.
    }
    apply Nat.succ_lt_mono in Hi.
    specialize (Hbf (S i) Hi) as H2.
    apply Nat.nlt_ge in Higz.
    remember (f (S i)) as fsi eqn:Hfsi.
    destruct fsi; [ | rewrite Nat_sub_succ_1; flia H2 ].
    flia Hi.
  } {
    intros i Hi.
    assert (His : i < S len) by flia Hi.
    unfold g'.
    rewrite if_ltb_lt_dec.
    apply Nat.succ_lt_mono in Hi.
    destruct (lt_dec (g 0) (g (S i))) as [H2| H2]. {
      specialize (Hbg (S i) Hi) as H3.
      remember (g (S i)) as gi eqn:Hgi.
      destruct gi; [ | rewrite Nat_sub_succ_1; flia H3 ].
      flia Hi.
    }
    apply Nat.nlt_ge in H2.
    destruct (Nat.eq_dec (g (S i)) (g 0)) as [Hgg| Hgg]. {
      apply (f_equal f) in Hgg.
      rewrite (proj2 (Hfg _ Hi)) in Hgg.
      rewrite (proj2 (Hfg _ (Nat.lt_0_succ _))) in Hgg.
      easy.
    }
    flia Hgb H2 Hgg.
  } {
    intros i Hi.
    assert (His : i < S len) by flia Hi.
    unfold f', g'.
    do 4 rewrite if_ltb_lt_dec.
    split. {
      destruct (lt_dec i (g 0)) as [Higz| Higz]. {
        remember (f i) as fi eqn:Hfi.
        destruct fi. {
          rewrite Hfi in Higz.
          rewrite (proj1 (Hfg i His)) in Higz.
          flia Higz.
        }
        rewrite Nat_sub_succ_1.
        rewrite Hfi.
        rewrite (proj1 (Hfg i His)).
        destruct (lt_dec (g 0) i) as [H| H]; [ flia Higz H | easy ].
      } {
        apply Nat.nlt_ge in Higz.
        apply Nat.succ_lt_mono in Hi.
        remember (f (S i)) as fi eqn:Hfi.
        destruct fi. {
          rewrite Hfi in Higz.
          rewrite (proj1 (Hfg (S i) Hi)) in Higz.
          flia Higz.
        }
        rewrite Nat_sub_succ_1.
        rewrite Hfi.
        rewrite (proj1 (Hfg _ Hi)).
        destruct (lt_dec (g 0) (S i)) as [H| H]; [ | flia Higz H ].
        clear H.
        now rewrite Nat.sub_succ, Nat.sub_0_r.
      }
    } {
      destruct (lt_dec (g 0) (g (S i))) as [Hgzs| Hgzs]. {
        apply Nat.succ_lt_mono in Hi.
        remember (g (S i)) as gi eqn:Hgi.
        destruct gi; [ easy | ].
        rewrite Nat_sub_succ_1.
        rewrite Hgi.
        rewrite (proj2 (Hfg _ Hi)), Nat_sub_succ_1.
        destruct (lt_dec gi (g 0)) as [H| H]; [ flia Hgzs H | easy ].
      } {
        apply Nat.nlt_ge in Hgzs.
        apply Nat.succ_lt_mono in Hi.
        rewrite (proj2 (Hfg (S i) Hi)), Nat_sub_succ_1.
        destruct (lt_dec (g (S i)) (g 0)) as [H| H]; [ easy | ].
        apply Nat.nlt_ge in H.
        apply Nat.le_antisymm in H; [ | easy ].
        apply (f_equal f) in H.
        rewrite (proj2 (Hfg _ Hi)) in H.
        now rewrite (proj2 (Hfg 0 (Nat.lt_0_succ _))) in H.
      }
    }
  } {
    intros i Hi.
    assert (His : i < S len) by flia Hi.
    unfold f'.
    rewrite if_ltb_lt_dec.
    destruct (lt_dec i (g 0)) as [Higz| Higz]. {
      rewrite List.app_nth1. 2: {
        rewrite List.length_firstn, Hbl.
        apply Nat.min_glb_lt; [ easy | flia Hi ].
      }
      specialize (Hn i His) as H2.
      rewrite <- (List.firstn_skipn (g 0) lb) in H2.
      rewrite List.app_nth1 in H2. 2: {
        rewrite List.length_firstn, Hbl.
        apply Nat.min_glb_lt; [ easy | flia Hi ].
      }
      remember (f i) as fi eqn:Hfi.
      destruct fi. {
        rewrite Hfi in Higz.
        rewrite (proj1 (Hfg i His)) in Higz; flia Higz.
      }
      now rewrite Nat_sub_succ_1.
    }
    apply Nat.nlt_ge in Higz.
    rewrite List.app_nth2. 2: {
      rewrite List.length_firstn, Hbl; unfold ge.
      transitivity (g 0); [ | easy ].
      apply Nat.le_min_l.
    }
    rewrite List.length_firstn, Hbl.
    rewrite Nat.min_l; [ | flia Hgb ].
    rewrite List_nth_skipn.
    replace (i - g 0 + S (g 0)) with (S i) by flia Higz.
    apply Nat.succ_lt_mono in Hi.
    specialize (Hn (S i) Hi) as H2.
    rewrite H2.
    remember (f (S i)) as fsi eqn:Hfsi.
    destruct fsi; cbn; [ | now rewrite Nat.sub_0_r ].
    apply (f_equal g) in Hfsi.
    rewrite (proj1 (Hfg (S i) Hi)) in Hfsi.
    flia Hfsi Higz.
  }
}
Qed.

Theorem permutation_partition : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ f la lb lc,
  List.partition f la = (lb, lc)
  → permutation eqb la (lb ++ lc).
Proof.
intros * Heqb * Hp.
revert lb lc Hp.
induction la as [| a]; intros; cbn. {
  now injection Hp; clear Hp; intros; subst lb lc.
}
cbn in Hp.
remember (List.partition f la) as pa eqn:Hpa; symmetry in Hpa.
destruct pa as (ld, le).
specialize (IHla _ _ eq_refl).
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b; injection Hp; clear Hp; intros; subst lb lc. {
  cbn; apply permutation_skip; [ | easy ].
  now unfold reflexive; apply equality_refl.
} {
  now apply (permutation_cons_app Heqb).
}
Qed.

(* transposition list *)

Fixpoint transp_loop {A} (eqb : A → A → bool) i la lb :=
  match lb with
  | [] => []
  | b :: lb' =>
      match List_extract (eqb b) la with
      | Some ([], _, la2) => transp_loop eqb (S i) la2 lb'
      | Some (a :: la1, _, la2) =>
          (i, S (i + List.length la1)) ::
          transp_loop eqb (S i) (la1 ++ a :: la2) lb'
      | None => []
      end
  end.

(* list of transpositions to be done to "la" to get "lb" *)
Definition transp_list {A} (eqb : A → _) la lb := transp_loop eqb 0 la lb.

Definition swap_d {A} d i j (la : list A) :=
   List.map
     (λ k, List.nth (if k =? i then j else if k =? j then i else k) la d)
     (List.seq 0 (List.length la)).

Definition swap {A} i j (la : list A) :=
  match la with
  | [] => []
  | d :: _ => swap_d d i j la
  end.

Definition apply_transp_list {A} trl (la : list A) :=
  List.fold_left (λ lb ij, swap (fst ij) (snd ij) lb) trl la.

Definition shift_transp i trl :=
  List.map (λ ij, (fst ij + i, snd ij + i)) trl.

Theorem fold_apply_transp_list : ∀ A trl (la : list A),
  List.fold_left (λ lb ij, swap (fst ij) (snd ij) lb) trl la =
  apply_transp_list trl la.
Proof. easy. Qed.

Theorem transp_loop_shift : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ i la lb,
  transp_loop eqb i la lb = shift_transp i (transp_list eqb la lb).
Proof.
intros * Heqb *.
revert i la.
induction lb as [| b]; intros; [ easy | cbn ].
remember (List_extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hla).
apply Heqb in Hx; subst x.
subst la.
destruct bef as [| a]. {
  do 2 rewrite IHlb.
  unfold shift_transp; cbn.
  rewrite List.map_map; cbn.
  apply List.map_ext_in.
  intros ij Hij.
  now do 2 rewrite <- Nat.add_assoc.
}
cbn.
f_equal; [ now rewrite Nat.add_comm | ].
do 2 rewrite IHlb.
unfold shift_transp; cbn.
rewrite List.map_map; cbn.
apply List.map_ext_in.
intros ij Hij.
now do 2 rewrite <- Nat.add_assoc.
Qed.

Theorem swap_length : ∀ A (la : list A) i j,
  List.length (swap i j la) = List.length la.
Proof.
intros.
unfold swap, swap_d.
destruct la as [| a]; [ easy | ].
apply List_length_map_seq.
Qed.

Theorem apply_transp_list_shift_1_cons : ∀ A (a : A) la trl,
  (∀ ij, ij ∈ trl → fst ij < snd ij < List.length la)
  → apply_transp_list (shift_transp 1 trl) (a :: la) =
    a :: apply_transp_list trl la.
Proof.
intros * Htrl.
revert a la Htrl.
induction trl as [| ij]; intros; [ easy | ].
cbn - [ "=?" shift_transp ].
destruct ij as (i, j).
cbn - [ shift_transp ].
unfold apply_transp_list in IHtrl.
rewrite <- IHtrl; cbn. 2: {
  intros ij Hij.
  rewrite swap_length.
  now apply Htrl; right.
}
do 2 rewrite Nat.add_1_r.
f_equal; f_equal.
unfold swap.
destruct la as [| d]; [ easy | ].
rewrite <- List.seq_shift.
rewrite List.map_map.
apply List.map_ext_in.
intros k Hk; cbn.
apply List.in_seq in Hk.
destruct Hk as (_, Hk); cbn in Hk.
do 4 rewrite if_eqb_eq_dec.
specialize (Htrl _ (or_introl eq_refl)) as Hij.
cbn in Hij.
destruct (Nat.eq_dec k i) as [Hki| Hki]. {
  subst k.
  destruct j; [ easy | ].
  apply List.nth_indep; flia Hij.
}
destruct (Nat.eq_dec k j) as [Hkj| Hkj]. {
  subst k.
  destruct i; [ easy | ].
  apply List.nth_indep; flia Hij.
}
destruct k; [ easy | ].
apply Nat.succ_lt_mono in Hk.
now apply List.nth_indep.
Qed.

Theorem in_transp_loop_length : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb,
  List.length la = List.length lb
  → ∀ i j k,
  (i, j) ∈ transp_loop eqb k la lb
  → i < j < k + List.length la.
Proof.
intros * Heqb * Hlab * Htab.
revert k la Hlab Htab.
induction lb as [| b]; intros; [ easy | ].
cbn in Htab.
remember (List_extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hla); subst la.
apply Heqb in Hx; subst x.
rewrite List.length_app in Hlab; cbn in Hlab.
rewrite Nat.add_succ_r in Hlab.
apply Nat.succ_inj in Hlab.
destruct bef as [| c]; cbn. {
  rewrite <- Nat.add_succ_comm.
  now apply IHlb.
}
destruct Htab as [Htab | Htab]. {
  injection Htab; clear Htab; intros; subst k j.
  split; [ flia | ].
  rewrite List.length_app; cbn.
  rewrite <- Nat.add_succ_comm, <- Nat.add_succ_l.
  apply Nat.add_lt_mono_l; flia.
}
specialize (IHlb (S k) (bef ++ c :: aft)) as H1.
assert (H : List.length (bef ++ c :: aft) = List.length lb). {
  rewrite List.length_app; cbn.
  now rewrite Nat.add_succ_r.
}
specialize (H1 H Htab); clear H.
rewrite List.length_app in H1 |-*; cbn in H1 |-*.
now rewrite Nat.add_succ_r.
Qed.

Theorem in_transp_list_length : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb,
  List.length la = List.length lb
  → ∀ i j,
  (i, j) ∈ transp_list eqb la lb
  → i < j < List.length la.
Proof.
intros * Heqb * Hlab * Htab.
apply (in_transp_loop_length Heqb la lb Hlab i j 0 Htab).
Qed.

Theorem permutation_transp_list : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb,
  permutation eqb la lb
  → apply_transp_list (transp_list eqb la lb) la = lb.
Proof.
intros * Heqb * Hpab.
revert la Hpab.
induction lb as [| b]; intros; cbn. {
  now apply permutation_nil_r in Hpab.
}
remember (List_extract (eqb b) la) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]. 2: {
  specialize (proj1 (List_extract_None_iff _ _) Hlxl) as H1.
  specialize (H1 b).
  specialize (permutation_in_iff Heqb Hpab) as H2.
  specialize (proj2 (H2 b) (or_introl eq_refl)) as H.
  specialize (H1 H); clear H.
  now rewrite (equality_refl Heqb) in H1.
}
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hx & Hla).
apply Heqb in Hx; subst x.
subst la.
assert (H : permutation eqb (bef ++ aft) lb). {
  apply (permutation_cons_inv Heqb) with (a := b).
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  rewrite (List_cons_is_app b aft), List.app_assoc.
  rewrite List.app_comm_cons.
  apply (permutation_app_tail Heqb).
  now apply permutation_cons_append.
}
move H before Hpab; clear Hpab; rename H into Hpab.
destruct bef as [| a]. {
  cbn.
  rewrite (transp_loop_shift Heqb).
  rewrite fold_apply_transp_list.
  rewrite apply_transp_list_shift_1_cons. 2: {
    intros (i, j) Hij; cbn.
    apply permutation_length in Hpab.
    now apply (in_transp_list_length Heqb _ _ Hpab).
  }
  f_equal.
  now apply IHlb.
}
cbn - [ swap ].
replace (swap _ _ _) with (b :: bef ++ a :: aft). 2: {
  cbn.
  rewrite List.app_nth2; [ | now unfold ge ].
  rewrite Nat.sub_diag; cbn; f_equal.
  rewrite <- List.seq_shift, List.map_map; cbn.
  rewrite List_map_nth_seq with (la := bef ++ a :: aft) (d := a).
  do 2 rewrite List.length_app.
  apply List.map_ext_in.
  intros i Hi.
  rewrite if_eqb_eq_dec.
  destruct (Nat.eq_dec i (List.length bef)) as [Hib| Hib]. {
    rewrite Hib.
    rewrite List.app_nth2; [ | now unfold ge ].
    now rewrite Nat.sub_diag.
  }
  destruct (lt_dec i (List.length bef)) as [Hibl| Hibg]. {
    rewrite List.app_nth1; [ | easy ].
    now rewrite List.app_nth1.
  }
  rewrite List.app_nth2; [ | flia Hib Hibg ].
  rewrite List.app_nth2; [ | flia Hib Hibg ].
  now replace (i - List.length bef) with (S (i - S (List.length bef)))
    by flia Hib Hibg.
}
rewrite (transp_loop_shift Heqb).
cbn in Hpab.
assert (H : permutation eqb (bef ++ a :: aft) lb). {
  eapply (permutation_trans Heqb); [ | apply Hpab ].
  rewrite (List_cons_is_app a aft), List.app_assoc.
  rewrite List.app_comm_cons.
  apply (permutation_app_tail Heqb).
  apply (permutation_sym Heqb).
  now apply permutation_cons_append.
}
move H before Hpab; clear Hpab; rename H into Hpab.
rewrite fold_apply_transp_list.
rewrite apply_transp_list_shift_1_cons. 2: {
  intros (i, j) Hij; cbn.
  apply permutation_length in Hpab.
  now apply (in_transp_list_length Heqb _ _ Hpab).
}
f_equal.
apply (IHlb _ Hpab).
Qed.

Theorem swap_d_inside : ∀ A (d : A) l1 l2 l3 x y,
  swap_d d (List.length l1) (S (List.length (l1 ++ l2)))
    (l1 ++ x :: l2 ++ y :: l3) =
  l1 ++ y :: l2 ++ x :: l3.
Proof.
intros.
unfold swap_d.
rewrite List_map_nth_seq with (d := d).
do 3 rewrite List.length_app; cbn.
do 2 rewrite List.length_app; cbn.
apply List.map_ext_in.
intros i Hi.
do 2 rewrite if_eqb_eq_dec.
remember (List.length l1) as len1 eqn:Hl1.
remember (List.length l2) as len2 eqn:Hl2.
move len2 before len1.
destruct (lt_dec i len1) as [Hi1| Hi1]. {
  destruct (Nat.eq_dec i len1) as [H| H]; [ flia Hi1 H | clear H].
  destruct (Nat.eq_dec i (S (len1 + len2))) as [H| H]; [ flia Hi1 H | ].
  clear H.
  rewrite Hl1 in Hi1.
  rewrite List.app_nth1; [ now rewrite List.app_nth1 | easy ].
}
apply Nat.nlt_ge in Hi1.
symmetry.
rewrite List.app_nth2; [ | now rewrite Hl1 in Hi1 ].
destruct (Nat.eq_dec i len1) as [Hi2| Hi2]. {
  rewrite Hi2, Hl1, Nat.sub_diag; cbn.
  rewrite Hl1 in Hi1, Hi2.
  rewrite List.app_nth2; [ | flia ].
  rewrite <- Nat.add_succ_r, Nat.add_comm, Nat.add_sub.
  rewrite List_nth_succ_cons.
  rewrite List.app_nth2; [ | now unfold ge; subst len2 ].
  now rewrite Hl2, Nat.sub_diag, List_nth_0_cons.
}
assert (H : len1 < i) by flia Hi1 Hi2; clear Hi1 Hi2; rename H into Hi1.
replace (i - List.length l1) with (S (i - S (List.length l1))) by
  flia Hl1 Hi1.
cbn.
rewrite <- Hl1.
symmetry.
rewrite List.app_nth2. 2: {
  destruct (Nat.eq_dec i (S (len1 + len2))) as [H| H]; [ | flia Hl1 Hi1 ].
  flia Hl1 Hi1.
}
destruct (lt_dec i (S (len1 + len2))) as [Hi2| Hi2]. {
  destruct (Nat.eq_dec i (S (len1 + len2))) as [H| H]; [ flia Hi2 H | ].
  clear H.
  rewrite <- Hl1.
  replace (i - len1) with (S (i - S len1)) by flia Hi1.
  rewrite List_nth_succ_cons.
  rewrite List.app_nth1; [ | rewrite <- Hl2; flia Hi1 Hi2 ].
  rewrite List.app_nth1; [ | rewrite <- Hl2; flia Hi1 Hi2 ].
  easy.
}
apply Nat.nlt_ge in Hi2.
destruct (Nat.eq_dec i (S (len1 + len2))) as [Hi3| Hi3]. {
  rewrite Hl1, Nat.sub_diag, List_nth_0_cons at 1.
  rewrite Hi3.
  rewrite <- Nat.add_succ_l, Nat.add_comm, Nat.add_sub; cbn.
  rewrite List.app_nth2; [ | now unfold ge; rewrite Hl2 ].
  now rewrite Hl2, Nat.sub_diag.
}
assert (H : S (len1 + len2) < i) by flia Hi2 Hi3.
clear Hi2 Hi3; rename H into Hi2.
rewrite <- Hl1.
replace (i - len1) with (S (i - S len1)) by flia Hi1.
rewrite List_nth_succ_cons.
rewrite List.app_nth2; [ | rewrite <- Hl2; flia Hi2 ].
rewrite List.app_nth2; [ | rewrite <- Hl2; flia Hi2 ].
rewrite <- Hl2.
now replace (i - S len1 - len2) with (S (i - S len1 - S len2)) by flia Hi2.
Qed.

Theorem permutation_transp_inside : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ l1 l2 l3 x y,
  permutation eqb (l1 ++ y :: l2 ++ x :: l3) (l1 ++ x :: l2 ++ y :: l3).
Proof.
intros * Heqb *.
rewrite List_cons_is_app.
rewrite (List_cons_is_app x).
rewrite (List_cons_is_app x (l2 ++ _)).
rewrite (List_cons_is_app y l3).
apply (permutation_app_head Heqb).
do 4 rewrite List.app_assoc.
apply (permutation_app_tail Heqb).
eapply (permutation_trans Heqb); [ | apply (permutation_app_comm Heqb) ].
rewrite <- List.app_assoc.
apply (permutation_app_head Heqb).
apply (permutation_app_comm Heqb).
Qed.

Theorem permutation_swap_any : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ i j la,
  i < j < List.length la
  → permutation eqb (swap i j la) la.
Proof.
intros * Heqb * Hij.
unfold swap.
destruct la as [| d]; [ apply permutation_nil_nil | ].
remember (d :: la) as lb eqn:Hlb.
clear la Hlb; rename lb into la.
assert (H : i < List.length la) by flia Hij.
specialize (List.nth_split la d H) as H1; clear H.
destruct H1 as (l1 & l2 & Hla & Hi).
remember (List.nth i la d) as x eqn:Hx.
subst la.
rewrite List.length_app in Hij; cbn in Hij.
assert (H : j - S i < List.length l2) by flia Hij Hi.
specialize (List.nth_split l2 d H) as H1; clear H.
destruct H1 as (l3 & l4 & Hl2 & Hj).
remember (List.nth (j - S i) l2 d) as y eqn:Hy.
subst l2; rename l3 into l2; rename l4 into l3.
assert (H : j = S (List.length (l1 ++ l2))). {
  rewrite List.length_app, Hj, Hi.
  flia Hij.
}
rewrite <- Hi, H.
rewrite swap_d_inside.
now apply permutation_transp_inside.
Qed.

Theorem iter_list_permut : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ T (d : T) (op : T → T → T) (l1 l2 : list A) f
  (op_d_l : ∀ x, op d x = x)
  (op_d_r : ∀ x, op x d = x)
  (op_comm : ∀ a b, op a b = op b a)
  (op_assoc : ∀ a b c, op a (op b c) = op (op a b) c),
  permutation eqb l1 l2
  → iter_list l1 (λ (c : T) i, op c (f i)) d =
    iter_list l2 (λ (c : T) i, op c (f i)) d.
Proof.
intros * Heqb * op_d_l op_d_r op_comm op_assoc Hl.
specialize (permutation_length Hl) as H1.
remember (List.length l2) as n eqn:H2.
move H1 after H2; symmetry in H2.
destruct n. {
  apply List.length_zero_iff_nil in H1.
  apply List.length_zero_iff_nil in H2.
  now subst l1 l2.
}
revert n l2 Hl H1 H2.
induction l1 as [| a]; intros; [ easy | ].
apply permutation_cons_l_iff in Hl.
remember (List_extract (eqb a) l2) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Hl2).
apply Heqb in H; subst x.
subst l2.
cbn in H1; apply Nat.succ_inj in H1.
rewrite List.length_app in H2; cbn in H2.
rewrite Nat.add_succ_r in H2.
apply Nat.succ_inj in H2.
rewrite <- List.length_app in H2.
destruct n. {
  apply List.length_zero_iff_nil in H1.
  apply List.length_zero_iff_nil in H2.
  apply List.app_eq_nil in H2.
  destruct H2.
  now subst l1 bef aft.
}
rewrite iter_list_cons; [ | easy | easy | easy ].
rewrite List_cons_is_app, List.app_assoc.
rewrite iter_list_app.
rewrite iter_list_app.
unfold iter_list at 3.
cbn; symmetry.
rewrite IHl1 with (n := n) (l2 := bef ++ aft); [ | easy | easy | easy ].
rewrite iter_list_app.
rewrite iter_list_op_fun_from_d with (d := d); [ | easy | easy | easy ].
symmetry.
rewrite iter_list_op_fun_from_d with (d := d); [ | easy | easy | easy ].
symmetry.
rewrite op_comm; symmetry.
rewrite op_assoc, op_comm.
f_equal.
apply op_comm.
Qed.

Theorem incl_incl_permutation : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb,
  List.NoDup la
  → List.NoDup lb
  → la ⊂ lb
  → lb ⊂ la
  → permutation eqb la lb.
Proof.
intros * Heqb * Hnda Hndb Hla Hlb.
revert lb Hndb Hla Hlb.
induction la as [| a]; intros. {
  destruct lb as [| b]; [ easy | exfalso ].
  now specialize (Hlb b (or_introl eq_refl)).
}
assert (H : List.NoDup la) by now apply List.NoDup_cons_iff in Hnda.
specialize (IHla H); clear H.
specialize (Hla _ (or_introl eq_refl)) as Ha.
apply List.in_split in Ha.
destruct Ha as (l1 & l2 & H); subst lb.
apply (permutation_cons_app Heqb).
apply IHla. {
  apply NoDup_app_iff in Hndb.
  apply NoDup_app_iff.
  split; [ easy | ].
  destruct Hndb as (_ & H1 & H2).
  apply List.NoDup_cons_iff in H1.
  split; [ easy | ].
  intros c Hc Hc2.
  now specialize (H2 _ Hc); apply H2; right.
} {
  intros c Hc.
  unfold List.incl in Hla.
  specialize (Hla _ (or_intror Hc)).
  apply List.in_app_or in Hla.
  apply List.in_or_app.
  destruct Hla as [Hla| Hla]; [ now left | ].
  destruct Hla as [Hla| Hla]; [ | now right ].
  subst c.
  now apply List.NoDup_cons_iff in Hnda.
} {
  intros c Hc.
  unfold List.incl in Hla, Hlb.
  specialize (Hlb c).
  assert (H : c ∈ l1 ++ a :: l2). {
    apply List.in_app_or in Hc.
    apply List.in_or_app.
    destruct Hc as [Hc| Hc]; [ now left | ].
    now right; right.
  }
  specialize (Hlb H); clear H.
  destruct Hlb as [Hca| Hca]; [ | easy ].
  subst c.
  apply NoDup_app_iff in Hndb.
  apply List.in_app_or in Hc.
  destruct Hndb as (H1 & H2 & H3).
  destruct Hc as [Hc| Hc]. {
    specialize (H3 _ Hc).
    now exfalso; apply H3; left.
  }
  now apply List.NoDup_cons_iff in H2.
}
Qed.

Theorem permutation_firstn : ∀ {A} {eqb : A → _} d,
  equality eqb →
  ∀ P n la lb,
  (∀ i, i < n → P (List.nth i la d) ∧ P (List.nth i lb d))
  → (∀ i,
      n ≤ i < List.length la
      → ¬ P (List.nth i la d) ∧ ¬ P (List.nth i lb d))
  → permutation eqb la lb
  → permutation eqb (List.firstn n la) (List.firstn n lb).
Proof.
intros * Heqb * Hpn1 Hpn2 Hpab.
destruct (le_dec (List.length la) n) as [Hlan| Hlan]. {
  rewrite List.firstn_all2; [ | easy ].
  rewrite List.firstn_all2; [ easy | ].
  apply permutation_length in Hpab.
  congruence.
}
apply Nat.nle_gt in Hlan.
revert n lb Hpn1 Hpn2 Hpab Hlan.
induction la as [| ma]; intros; [ easy | ].
apply permutation_cons_l_iff in Hpab.
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hax & Haft).
apply Heqb in Hax; subst x lb.
destruct n; [ easy | ].
rewrite List.firstn_cons.
assert (Hbn : List.length bef ≤ n). {
  apply Nat.nlt_ge; intros H1.
  specialize (Hpn2 (List.length bef)) as H2.
  assert (H : S n ≤ List.length bef < List.length (ma :: la)). {
    split; [ easy | ].
    apply permutation_length in Hpab.
    rewrite List.length_app in Hpab; cbn; flia Hpab.
  }
  specialize (H2 H); clear H.
  destruct H2 as (H2, H3).
  rewrite List.app_nth2 in H3; [ | flia ].
  rewrite Nat.sub_diag in H3; cbn in H3.
  now specialize (Hpn1 0 (Nat.lt_0_succ _)) as H4.
}
cbn in Hlan; apply Nat.succ_lt_mono in Hlan.
replace (S n) with (List.length bef + (S n - List.length bef)) by flia Hbn.
rewrite List.firstn_app_2.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite List.firstn_cons.
apply (permutation_cons_app Heqb).
specialize (List.firstn_app n bef aft) as H1.
replace (List.firstn n bef) with bef in H1 by
  now symmetry; apply List.firstn_all2.
rewrite <- H1; clear H1.
apply IHla; [ | | easy | easy ]. {
  intros i Hi.
  apply Nat.succ_lt_mono in Hi.
  specialize (Hpn1 _ Hi) as H1.
  cbn in H1.
  split; [ easy | ].
  destruct H1 as (H1, H2).
  destruct (lt_dec i (List.length bef)) as [Hib| Hib]. {
    rewrite List.app_nth1; [ | easy ].
    specialize (Hpn1 i) as H3.
    assert (H : i < S n) by flia Hi.
    specialize (H3 H); clear H.
    destruct H3 as (H3, H4).
    rewrite List.app_nth1 in H4; [ easy | easy ].
  }
  apply Nat.nlt_ge in Hib.
  rewrite List.app_nth2; [ | easy ].
  rewrite List.app_nth2 in H2; [ | flia Hib ].
  rewrite Nat.sub_succ_l in H2; [ easy | easy ].
} {
  intros i Hni.
  specialize (Hpn2 (S i)) as H1.
  cbn in H1.
  assert (Hnia : S n ≤ S i < S (List.length la)) by flia Hni.
  specialize (H1 Hnia).
  split; [ easy | ].
  destruct H1 as (H1, H2).
  cbn - [ List.nth ] in Hpn2.
  destruct (lt_dec i (List.length bef)) as [Hib| Hib]. {
    rewrite List.app_nth1; [ | easy ].
    specialize (Hpn2 i) as H3.
    destruct (Nat.eq_dec i n) as [Hisn| Hisn]. 2: {
      assert (H : S n ≤ i < S (List.length la)) by flia Hni Hisn.
      specialize (H3 H); clear H.
      destruct H3 as (H3, H4).
      rewrite List.app_nth1 in H4; [ easy | easy ].
    }
    subst i; flia Hbn Hib.
  }
  apply Nat.nlt_ge in Hib.
  rewrite List.app_nth2; [ | easy ].
  specialize (Hpn2 (S i) Hnia) as H3.
  destruct H3 as (H3, H4).
  rewrite List.app_nth2 in H4; [ | flia Hib ].
  rewrite Nat.sub_succ_l in H4; [ easy | easy ].
}
Qed.

Theorem permutation_app_permutation_l : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ la lb lc ld,
  permutation eqb (la ++ lb) (lc ++ ld)
  → permutation eqb la lc
  → permutation eqb lb ld.
Proof.
intros * Heqb * Habcd Hac.
revert lb lc ld Habcd Hac.
induction la as [| a]; intros. {
  now apply permutation_nil_l in Hac; subst lc.
}
cbn in Habcd.
apply permutation_cons_l_iff in Hac.
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & Hax & Haft); subst lc.
apply Heqb in Hax; subst x.
rewrite <- List.app_assoc in Habcd; cbn in Habcd.
assert (H : permutation eqb (la ++ lb) (bef ++ aft ++ ld)). {
  apply (permutation_cons_inv Heqb) with (a := a).
  eapply (permutation_trans Heqb); [ apply Habcd | ].
  rewrite List_cons_is_app.
  rewrite (List_cons_is_app a (bef ++ aft ++ ld)).
  do 4 rewrite List.app_assoc.
  do 2 apply (permutation_app_tail Heqb).
  apply (permutation_sym Heqb); cbn.
  apply (permutation_cons_append Heqb).
}
rewrite List.app_assoc in H.
now apply IHla in H.
Qed.

Theorem permutation_filter : ∀ {A} {eqb : A → _},
  equality eqb →
  ∀ f la lb,
  permutation eqb la lb
  → permutation eqb (List.filter f la) (List.filter f lb).
Proof.
intros * Heqb * Hab.
revert lb Hab.
induction la as [| a]; intros; cbn. {
  now apply permutation_nil_l in Hab; subst lb.
}
apply permutation_cons_l_iff in Hab.
remember (List_extract _ _) as lxl eqn:Hlxl; symmetry in Hlxl.
destruct lxl as [((bef, x), aft)| ]; [ | easy ].
apply List_extract_Some_iff in Hlxl.
destruct Hlxl as (Hbef & H & Haft).
apply Heqb in H; subst x lb.
rewrite List.filter_app; cbn.
remember (f a) as fa eqn:Hfa; symmetry in Hfa.
destruct fa. {
  apply (permutation_cons_app Heqb).
  rewrite <- List.filter_app.
  now apply IHla.
}
rewrite <- List.filter_app.
now apply IHla.
Qed.
