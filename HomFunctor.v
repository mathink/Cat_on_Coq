(* Hom Functor *)

Set Implicit Arguments.
Require Import Setoid Category Functor.

Program Instance Setoids: Category :=
  { obj := Setoid;
    arr X Y := MapSetoid X Y;
    compose X Y Z f g := ComposeMap f g;
    id X := IdMap X }.
Next Obligation.
  simpl; intros; try equiv_refl.
Qed.
Next Obligation.
  equiv_trns_with (g' (f x)); auto.
  apply ap_preserve_eq; auto.
Qed.
Next Obligation.
  simpl; intros; try equiv_refl.
Qed.
Next Obligation.
  simpl; intros; try equiv_refl.
Qed.

Program Instance HomFunctor_fmap
        (C: Category)(X: C){Y Y': C}(g: Y ⟶ Y')
: Map (X ⟶ Y) (X ⟶ Y') :=
  { ap f := compose f g }.
Next Obligation.
  intros.
  apply compose_subst_fst; auto.
Qed.

Program Instance HomFunctor_fmap_Map
        (C: Category)(X: C){Y Y': C}
: Map (Y ⟶ Y') (MapSetoid (X ⟶ Y) (X ⟶ Y')) :=
  { ap := HomFunctor_fmap C X }.
Next Obligation.
  apply compose_subst_snd; auto.
Qed.

Program Instance opHomFunctor_fmap
        (C: Category)(Y: C){X X': C}(f: X ⟶ X')
: Map (X' ⟶ Y) (X ⟶ Y) :=
  { ap := compose f }.
Next Obligation.
  intros.
  apply compose_subst_snd; auto.
Qed.

Program Instance opHomFunctor_fmap_Map
        (C: Category)(Y: C){X X': C}
: Map (X ⟶ X') (MapSetoid (X' ⟶ Y) (X ⟶ Y)) :=
  { ap := opHomFunctor_fmap C Y }.
Next Obligation.
  apply compose_subst_fst; auto.
Qed.



Program Instance HomFunctor
        (C: Category)(X: C): Functor C Setoids :=
  { fobj Y := X ⟶ Y ; fmap Y Z := HomFunctor_fmap_Map C X }.
Next Obligation.
  simpl.
  apply id_cod.
Qed.
Next Obligation.
  equiv_symm; auto; apply compose_assoc.
Qed.

Program Instance contravariantHomFunctor
        (C: Category)(Y: C): contravariantFunctor C Setoids :=
  { op_fobj X := X ⟶ Y ; op_fmap X X' := opHomFunctor_fmap_Map C Y }.
Next Obligation.
  apply id_dom.
Qed.
Next Obligation.
  simpl; apply compose_assoc.
Qed.

Program Instance opHomFunctor
        (C: Category)(Y: C): Functor (op_Category C) Setoids :=
  contFunctor_Functor (contravariantHomFunctor C Y).


