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
  intros C D F G H S S' T T' HeqS HeqT X; simpl.
  apply Category.comp_subst; [apply HeqS | apply HeqT].
Qed.
Next Obligation.
  intros C D F G H I S T U X; simpl in *.
  apply Category.comp_assoc.
Qed.
Next Obligation.
  intros C D F G S X; simpl in *.
  apply Category.comp_id_dom.
Qed.
Next Obligation.
  intros C D F G S X; simpl in *.
  apply Category.comp_id_cod.
Qed.

Notation "[ C :=> D ]" := (Fun C D) (D at level 200): cat_scope.


