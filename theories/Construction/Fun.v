Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

(** 
 ** 函手圏
 **)
Program Definition Fun (C D: Category) :=
  Category.build (@Natrans.setoid C D)
                 (@Natrans.compose C D)
                 (@Natrans.id C D).
Next Obligation.
  revert X Y Z; intros F G H.
  intros S S' HeqS T T' HeqT X; simpl.
  now rewrite (HeqS X), (HeqT X).
Qed.
Next Obligation.
  now intros x; simpl; rewrite catCa.
Qed.
Next Obligation.
  now intros x; simpl in *; rewrite catC1f.
Qed.
Next Obligation.
  now intros x; simpl in *; rewrite catCf1.
Qed.

Notation "[ C :=> D ]" := (Fun C D) (D at level 200): cat_scope.
