(* -*- mode: coq -*- *)
(* Time-stamp: <2014/9/24 1:37:40> *)
(*
  Discrete.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category.

(** * 有限離散圏の定義  *)
Canonical Structure Setoid_eq (A: Type): Setoid :=
  Build_Setoid (@eq_equivalence A).

Require Import Arith.

Definition ltb (n m: nat) := andb (negb (beq_nat n m)) (leb n m).

(** 要素数 n の離散圏の対象 setoid は { m | m < n }  *)
Structure discrete (n: nat) :=
  Elem { dbody:> nat; prf_Elem: ltb dbody n = true }.

Lemma bool_eq_irrelevance (b1 b2: bool)(p q: b1 = b2): p = q.
Proof.
  intros; apply Eqdep_dec.eq_proofs_unicity; intros.
  destruct (Bool.bool_dec x y); tauto.
Qed.

Lemma prf_Elem_unique (n: nat)(m: nat)(p q: ltb n m = true): p = q.
Proof.
  apply bool_eq_irrelevance.
Qed.


(** hom setoid は n = m であり、その等価性は証明の等価性。
    nat の eq については proof_irrelevance が成立。
   *)
Definition Discr (n: nat) := Setoid_eq (discrete n).
Definition Discr_Hom (k: nat)(n m: Discr k) := n = m.
Arguments Discr_Hom k / n m.

Definition equal_Discr_Hom (k: nat)(n m: Discr k)(f g: Discr_Hom n m) := f = g.
Arguments equal_Discr_Hom k n m / f g.

Instance equal_Discr_Hom_Equiv (k: nat)(n m: Discr k)
: Equivalence (@equal_Discr_Hom k n m).
Proof.
  split; simpl.
  - intro f; reflexivity.
  - intros f g Heq; subst; reflexivity.
  - intros f g h Heq1 Heq2; subst; reflexivity.
Qed.

Canonical Structure Setoid_Discr_Hom (k: nat)(n m: Discr k): Setoid :=
  Build_Setoid (equal_Discr_Hom_Equiv n m).

(** 合成や恒等射はやってみればなんとかなります  *)
Definition compose_Discr (k: nat)(n m p: Discr k)(f: Discr_Hom n m)(g: Discr_Hom m p): Discr_Hom n p.
  revert f p g.
  unfold Discr_Hom; intro H; rewrite H; auto.
Defined.
Arguments compose_Discr k n m p / f g.

Program Instance Compose_Discr (k: nat): Compose (@Setoid_Discr_Hom k) :=
  { compose n m p f g := compose_Discr f g }.

Instance Identity_Discr (k: nat): Identity (@Setoid_Discr_Hom k) :=
  { identity n := eq_refl n }.

(** 圏であることの証明 *)
Instance Discr_IsCategory (k: nat): isCategory (Compose_Discr k) (@Identity_Discr k).
Proof.
  split; simpl; intros.
  - subst; reflexivity.
  - subst; simpl.
    intros; apply Eqdep_dec.eq_proofs_unicity; intros.
    destruct x as [n Hn]; destruct y as [m Hm]; simpl.
    destruct (eq_nat_dec n m); simpl.
    + left; subst.
      rewrite (prf_Elem_unique Hm Hn).
      reflexivity.
    + right; intro; apply n0.
      injection H; auto.
  - subst; simpl.
    intros; apply Eqdep_dec.eq_proofs_unicity; intros.
    destruct x as [n Hn]; destruct y as [m Hm]; simpl.
    destruct (eq_nat_dec n m); simpl; subst.
    + left.
      rewrite (prf_Elem_unique Hm Hn).
      reflexivity.
    + right; intro H.
      injection H; auto.
Qed.

Definition Discr_Category (k: nat): Category :=
  Build_Category (Discr_IsCategory k).
