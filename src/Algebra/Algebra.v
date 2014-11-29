(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/29 15:22:54> *)
(*
  Algebra.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.

(** * F-代数
    F-代数の圏を定義し、始代数から catamophism を定義します。
 *)

Require Import Category Functor.

(** ** F-代数 *)
Structure Alg `(F: Functor C C) :=
  { alg_obj:> C;
    alg_arr:> C (F alg_obj) alg_obj }.
(* Notation "'A^' x" := (alg_obj x) (at level 3, right associativity). *)

(** ** F-代数の間の準同型
 F X -F h-> F Y
  |         |
  X  - h ->  Y
*)
Class isAlgMap `(F: Functor C C)(x y: Alg F)(h: C x y): Prop :=
  alg_commute:
    y \o{C} fmap F h == h \o{C} x.

Structure AlgMap `(F: Functor C C)(x y: Alg F) :=
  { alg_map:> C x y;

    prf_AlgMap: isAlgMap alg_map }.
Existing Instance prf_AlgMap.

(** ** ALG(F) :: F-代数の圏 *)
Program Definition compose_AlgMap `(F: Functor C C)(x y z: Alg F)
        (f: AlgMap x y)(g: AlgMap y z): AlgMap x z :=
  {| alg_map := g \o{C} f |}.
Next Obligation.
  simpl; unfold isAlgMap.
  now rewrite (fmap_comp F), <- compose_assoc, alg_commute, compose_assoc, alg_commute, compose_assoc. 
Defined.
Arguments compose_AlgMap C F x y z / f g.

Program Definition id_AlgMap `(F: Functor C C)(x: Alg F): AlgMap x x :=
  {| alg_map := Id (x:C) |}.
Next Obligation.
  simpl; unfold isAlgMap.
  now rewrite (fmap_ident F), identity_dom, identity_cod.
Qed.

Definition equal_AlgMap `(F: Functor C C)(x y: Alg F)(f g: AlgMap x y) :=
  (f: C x y) == (g: C x y).
Arguments equal_AlgMap C F x y / f g.

Instance equal_AlgMap_Equiv `(F: Functor C C)(x y: Alg F)
: Equivalence (@equal_AlgMap C F x y).
Proof.
  split; simpl.
  - now intros f; simpl.
  - now intros f g Heq.
  - now intros f g h Heqfg Heqgh; rewrite Heqfg.
Qed.
Canonical Structure Setoid_AlgMap `(F: Functor C C)(x y: Alg F)
  := Build_Setoid (equal_AlgMap_Equiv F x y).

Instance Compose_AlgMap C (F: Functor C C): Compose (@Setoid_AlgMap _ F) :=
  { compose x y z f g := @compose_AlgMap C F x y z f g }.
Proof.
  now intros x y z f f' Heqf g g' Heqg; simpl in *; rewrite Heqf, Heqg.
Defined.

Instance Identity_AlgMap `(F: Functor C C): Identity (@Setoid_AlgMap _ F) :=
  { identity := @id_AlgMap C F }.

Program Instance Alg_IsCategory `(F: Functor C C)
: isCategory (Compose_AlgMap F) (Identity_AlgMap F).
Next Obligation.
  now apply compose_assoc.
Qed.
Next Obligation.
  now apply identity_dom.
Qed.
Next Obligation.
  now apply identity_cod.
Qed.

Canonical Structure ALG `(F: Functor C C): Category :=
  Build_Category (Alg_IsCategory F).


(** ** catamorphism :: F-始代数からの射  *)
Definition catamorphism `(F: Functor C C)
           (In: Initial (ALG F))(x: Alg F): C (init In) x :=
  initial In x.

Lemma cata_refl `(F: Functor C C)(In: Initial (ALG F)):
  catamorphism In (init In) == Id (init In: C).
Proof.
  now unfold catamorphism; simpl; apply (init_refl (C:=ALG F)).
Qed.

Lemma cata_fusion `(F: Functor C C)(In: Initial (ALG F))
      (f g: Alg F)(h: AlgMap f g):
  h \o catamorphism In f == catamorphism In g.
Proof.
  unfold catamorphism; simpl.
  now generalize (init_fusion In h); simpl; auto.
Qed.






  