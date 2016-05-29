Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid COC.Category.Category.

(** * Setoid の圏: Setoids
例にちょうどよい。
Hom 函手を定義する時とかに使うのでここで作っておく。
 **)
Program Canonical Structure Setoids: Category :=
  Category.build (@Map.setoid) (@Map.compose) (@Map.id).
Next Obligation.
  intros f f' Hf g g' Hg x; simpl.
  rewrite (Hf x); apply Hg.
Qed.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  reflexivity.
Qed.
