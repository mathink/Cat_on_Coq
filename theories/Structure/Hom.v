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
  now intros f f' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros g g' Heq f; simpl; rewrite Heq.
Qed.
Next Obligation.
  now rewrite catCa.
Qed.
Next Obligation.
  now rewrite catCf1.
Qed.


(**
 *** 反変な方の [Hom]
 **)
Program Definition OpHomFunctor (C: Category)(Y: C)
  : Functor (Category.op C) Setoids :=
  Functor.build (fun X => C X Y)
                (fun X Y f => [g :-> g \o{C} f]).
Next Obligation.
  now intros g g' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros g g' Heq f; simpl; rewrite Heq.
Qed.
Next Obligation.
  now rewrite catCa.
Qed.
Next Obligation.
  now rewrite catC1f.
Qed.

(**
 *** 記法の定義
 **)
Notation "'Hom' ( X , - )" := (HomFunctor X): cat_scope.
Notation "'Hom' ( - , Y )" := (OpHomFunctor Y): cat_scope.

