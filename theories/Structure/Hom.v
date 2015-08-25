Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

(** 
 ** Hom 函手たち
[Hom(X,-)] と [Hom(-,Y)] を作るよ。
[Functor.build] 使うと定義書くのすごく楽。嬉しい。
 **)

(**
 *** 共変な方の [Hom]
 **)
Program Definition HomFunctor (C: Category)(X: C)
  : Functor C Setoids :=
  Functor.build (C X) (fun Y X g => [f :-> g \o{C} f]).
Next Obligation.
  intros C X Y Z g f f' Heq.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C X Y Z g g' Heq f; simpl.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C X Y Z W g h f; simpl.
  apply Category.comp_assoc.
Qed.
Next Obligation.
  intros C X Y f; simpl.
  apply Category.comp_id_cod.
Qed.


(**
 *** 反変な方の [Hom]
 **)
Program Definition OpHomFunctor (C: Category)(Y: C)
  : Functor (Category.op C) Setoids :=
  Functor.build (fun X => C X Y)
                (fun X Y f => [g :-> g \o{C} f]).
Next Obligation.
  intros C Z Y X f g g' Heq; simpl in *.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C Z Y X f g g' Heq; simpl in *.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C W Z Y X g f h; simpl in *.
  apply symmetry, Category.comp_assoc.
Qed.
Next Obligation.
  intros C Y X f; simpl in *.
  apply Category.comp_id_dom.
Qed.

(**
 *** 記法の定義
 **)
Notation "'Hom' ( X , - )" := (HomFunctor X): cat_scope.
Notation "'Hom' ( - , Y )" := (OpHomFunctor Y): cat_scope.

