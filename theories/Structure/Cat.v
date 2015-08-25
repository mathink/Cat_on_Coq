Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

(** 
 *** 圏の圏：Cat
Universe Polymorphism のおかげで定義できる。
 **)
Program Definition Cat: Category :=
  Category.build
    (@Functor.setoid)
    (@Functor.compose)
    (@Functor.id).
Next Obligation.
  intros C D E F F' G G' HeqF HeqG X Y f; simpl.
  destruct (HeqF _ _ f); simpl.
  eapply eq_Hom_trans.
  - apply eq_Hom_def.
    apply Map.substitute, H.
  - apply HeqG.
Qed.
Next Obligation.
  intros C D K L F G H X Y f; simpl in *.
  apply eq_Hom_refl.
Qed.
Next Obligation.
  intros C D F X Y f; simpl in *.
  apply eq_Hom_refl.
Qed.
Next Obligation.
  intros C D F X Y f; simpl in *.
  apply eq_Hom_refl.
Qed.
