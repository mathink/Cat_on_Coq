Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category.

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
  revert X Y Z.
  intros C D E F F' HeqF G G' HeqG X Y f; simpl.
  destruct (HeqF _ _ f); simpl.
  eapply eq_Hom_trans.
  - apply eq_Hom_def.
    apply Map.substitute, H.
  - apply HeqG.
Qed.
Next Obligation.
  apply eq_Hom_refl.
Qed.
Next Obligation.
  apply eq_Hom_refl.
Qed.
Next Obligation.
  apply eq_Hom_refl.
Qed.

